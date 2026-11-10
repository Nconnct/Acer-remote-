package com.example.acerremote

import android.content.*
import android.hardware.ConsumerIrManager
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import android.net.nsd.NsdManager
import android.net.nsd.NsdServiceInfo
import android.os.*
import android.util.Base64
import android.speech.RecognizerIntent
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.foundation.*
import androidx.compose.foundation.gestures.detectTapGestures
import androidx.compose.foundation.text.KeyboardActions
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.platform.LocalSoftwareKeyboardController
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.hapticfeedback.HapticFeedbackType
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalHapticFeedback
import androidx.compose.ui.text.input.KeyboardType
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.shape.*
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.*
import java.io.*
import java.math.BigInteger
import java.net.Socket
import java.security.*
import java.security.cert.X509Certificate
import java.security.interfaces.RSAPublicKey
import java.util.concurrent.Executors
import java.util.concurrent.LinkedBlockingQueue
import javax.net.ssl.*
import java.net.InetSocketAddress
import java.security.spec.PKCS8EncodedKeySpec
import java.util.Date
import org.bouncycastle.asn1.x500.X500Name
import org.bouncycastle.cert.jcajce.JcaX509CertificateConverter
import org.bouncycastle.cert.jcajce.JcaX509v3CertificateBuilder
import org.bouncycastle.operator.jcajce.JcaContentSignerBuilder

// ---------- tiny protobuf helpers ----------
object Pb {
    fun varint(v0: Long): ByteArray {
        var v = v0; val o = ByteArrayOutputStream()
        while (true) {
            val b = (v and 0x7F).toInt(); v = v ushr 7
            if (v == 0L) { o.write(b); break } else o.write(b or 0x80)
        }
        return o.toByteArray()
    }
    fun int(f: Int, v: Int) = varint((f shl 3).toLong()) + varint(v.toLong())
    fun bytes(f: Int, b: ByteArray) = varint(((f shl 3) or 2).toLong()) + varint(b.size.toLong()) + b
    fun str(f: Int, s: String) = bytes(f, s.toByteArray())
    fun parse(b: ByteArray): Map<Int, Any> {
        val m = HashMap<Int, Any>(); var p = 0
        fun rv(): Long {
            var r = 0L; var s = 0
            while (p < b.size) {
                val x = b[p++].toInt() and 0xFF
                r = r or ((x and 0x7F).toLong() shl s)
                if ((x and 0x80) == 0) break
                s += 7
            }
            return r
        }
        while (p < b.size) {
            val t = rv().toInt(); val f = t ushr 3
            when (t and 7) {
                0 -> { val v = rv(); if (!m.containsKey(f)) m[f] = v }
                2 -> { val l = rv().toInt(); if (!m.containsKey(f)) m[f] = b.copyOfRange(p, p + l); p += l }
                1 -> p += 8
                5 -> p += 4
                else -> return m
            }
        }
        return m
    }
}
private fun frameWrite(o: OutputStream, b: ByteArray) { o.write(Pb.varint(b.size.toLong())); o.write(b); o.flush() }
private fun frameRead(i: InputStream): ByteArray {
    var len = 0; var sh = 0
    while (true) {
        val x = i.read(); if (x < 0) throw EOFException("TV closed the connection")
        len = len or ((x and 0x7F) shl sh)
        if ((x and 0x80) == 0) break
        sh += 7
    }
    val b = ByteArray(len); var n = 0
    while (n < len) { val r = i.read(b, n, len - n); if (r < 0) throw EOFException("TV closed the connection"); n += r }
    return b
}
private fun unsignedBytes(b: BigInteger): ByteArray {
    val a = b.toByteArray()
    return if (a.size > 1 && a[0] == 0.toByte()) a.copyOfRange(1, a.size) else a
}
private fun hexBytes(s: String): ByteArray {
    val c = s.trim()
    require(c.length % 2 == 0 && c.isNotEmpty()) { "Code must be 6 characters" }
    return ByteArray(c.length / 2) { c.substring(2 * it, 2 * it + 2).toInt(16).toByte() }
}

// ---------- Android TV Remote (Wi-Fi) client: pairing on 6467, control on 6466 ----------
class Tv(private val ctx: Context) {
    val status = mutableStateOf("Enter the TV's IP address (or tap Find TV), then tap Pair")
    val ip = mutableStateOf("")
    val askCode = mutableStateOf(false)
    val isConnected = mutableStateOf(false)
    @Volatile private var fg = true
    private var retry = 0
    val kbdReq = mutableStateOf(0)                 // bumps when the TV asks for the phone keyboard
    @Volatile private var imeSeen = false
    @Volatile private var imeCounter = 1
    @Volatile private var fieldCounter = 1
    val found = mutableStateListOf<Pair<String, String>>()
    private val prefs = ctx.getSharedPreferences("tv", 0)
    private val io = Executors.newSingleThreadExecutor()
    private val ui = Handler(Looper.getMainLooper())
    private val codeQ = LinkedBlockingQueue<String>()
    @Volatile private var sock: SSLSocket? = null
    @Volatile private var out: OutputStream? = null
    private var disc: NsdManager.DiscoveryListener? = null
    private var ident: Pair<PrivateKey, X509Certificate>? = null

    init { ip.value = prefs.getString("ip", "") ?: "" }
    fun paired() = prefs.getBoolean("paired", false) && ip.value.isNotBlank()
    fun connected() = out != null
    fun onStart() { fg = true; retry = 0; if (paired() && !connected()) connect() }
    fun onStop() { fg = false; disconnect() }   // saves battery; reconnects when you come back

    // Keep traffic on Wi-Fi even when the router has no internet (phone would otherwise use mobile data).
    private fun bindWifi() {
        try {
            val cm = ctx.getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            cm.allNetworks.firstOrNull { cm.getNetworkCapabilities(it)?.hasTransport(NetworkCapabilities.TRANSPORT_WIFI) == true }
                ?.let { cm.bindProcessToNetwork(it) }
        } catch (e: Exception) {}
    }

    // Our own client identity (software RSA key + self-signed certificate), saved on the phone.
    private fun identity(): Pair<PrivateKey, X509Certificate> {
        ident?.let { return it }
        val ks = prefs.getString("key2", null); val cs = prefs.getString("cert2", null)
        if (ks != null && cs != null) {
            try {
                val pk = KeyFactory.getInstance("RSA").generatePrivate(PKCS8EncodedKeySpec(Base64.decode(ks, Base64.DEFAULT)))
                val c = java.security.cert.CertificateFactory.getInstance("X.509")
                    .generateCertificate(ByteArrayInputStream(Base64.decode(cs, Base64.DEFAULT))) as X509Certificate
                return Pair(pk, c).also { ident = it }
            } catch (e: Exception) {}
        }
        val kp = KeyPairGenerator.getInstance("RSA").apply { initialize(2048) }.generateKeyPair()
        val n = X500Name("CN=acer-remote")
        val from = Date(System.currentTimeMillis() - 86_400_000L)
        val to = Date(System.currentTimeMillis() + 3650L * 86_400_000L)
        val holder = JcaX509v3CertificateBuilder(n, BigInteger.valueOf(System.currentTimeMillis()), from, to, n, kp.public)
            .build(JcaContentSignerBuilder("SHA256withRSA").build(kp.private))
        val c = JcaX509CertificateConverter().getCertificate(holder)
        prefs.edit().putString("key2", Base64.encodeToString(kp.private.encoded, Base64.DEFAULT))
            .putString("cert2", Base64.encodeToString(c.encoded, Base64.DEFAULT)).putBoolean("paired", false).apply()
        return Pair(kp.private, c).also { ident = it }
    }

    private fun factory(): SSLSocketFactory {
        val (pk, cert) = identity()
        val km = object : X509KeyManager {
            override fun getClientAliases(t: String?, i: Array<Principal>?): Array<String> = arrayOf("c")
            override fun chooseClientAlias(t: Array<String>?, i: Array<Principal>?, s: Socket?): String = "c"
            override fun getServerAliases(t: String?, i: Array<Principal>?): Array<String>? = null
            override fun chooseServerAlias(t: String?, i: Array<Principal>?, s: Socket?): String? = null
            override fun getCertificateChain(a: String?): Array<X509Certificate> = arrayOf(cert)
            override fun getPrivateKey(a: String?): PrivateKey = pk
        }
        // The TV uses a self-signed certificate on your local network, so we accept it.
        val tm = object : X509TrustManager {
            override fun checkClientTrusted(c: Array<X509Certificate>?, a: String?) {}
            override fun checkServerTrusted(c: Array<X509Certificate>?, a: String?) {}
            override fun getAcceptedIssuers(): Array<X509Certificate> = arrayOf()
        }
        return SSLContext.getInstance("TLS").apply { init(arrayOf(km), arrayOf(tm), null) }.socketFactory
    }

    // TCP connect with a timeout, then TLS. Gives readable errors instead of hanging.
    private fun open(host: String, port: Int, readTimeout: Int): SSLSocket {
        val plain = Socket()
        plain.tcpNoDelay = true
        try { plain.connect(InetSocketAddress(host, port), 6000) }
        catch (e: Exception) {
            try { plain.close() } catch (x: Exception) {}
            throw IOException("Can't reach $host:$port (${e.javaClass.simpleName}). Check the IP, that the phone and TV are on the same Wi-Fi, and that the TV is on")
        }
        val s = factory().createSocket(plain, host, port, true) as SSLSocket
        s.tcpNoDelay = true
        s.soTimeout = 15000
        try { s.startHandshake() }
        catch (e: Exception) {
            try { s.close() } catch (x: Exception) {}
            throw IOException("Secure connection failed (${e.javaClass.simpleName}: ${e.message})")
        }
        s.soTimeout = readTimeout
        return s
    }

    fun discover() {
        found.clear()
        try { bindWifi() } catch (e: Exception) {}
        status.value = "Looking for TVs on Wi-Fi…"
        val nsd = ctx.getSystemService(Context.NSD_SERVICE) as NsdManager
        try { disc?.let { nsd.stopServiceDiscovery(it) } } catch (e: Exception) {}
        val l = object : NsdManager.DiscoveryListener {
            override fun onServiceFound(si: NsdServiceInfo) {
                try {
                    nsd.resolveService(si, object : NsdManager.ResolveListener {
                        override fun onServiceResolved(r: NsdServiceInfo) {
                            val h = r.host?.hostAddress ?: return
                            ui.post { if (found.none { it.second == h }) found.add(Pair(r.serviceName, h)) }
                        }
                        override fun onResolveFailed(r: NsdServiceInfo, e: Int) {}
                    })
                } catch (e: Exception) {}
            }
            override fun onServiceLost(si: NsdServiceInfo) {}
            override fun onDiscoveryStarted(t: String) {}
            override fun onDiscoveryStopped(t: String) {}
            override fun onStartDiscoveryFailed(t: String, e: Int) { status.value = "Auto-find failed. Type the TV's IP address" }
            override fun onStopDiscoveryFailed(t: String, e: Int) {}
        }
        disc = l
        try { nsd.discoverServices("_androidtvremote2._tcp", NsdManager.PROTOCOL_DNS_SD, l) }
        catch (e: Exception) { status.value = "Auto-find failed. Type the TV's IP address" }
    }

    fun submit(code: String) { codeQ.offer(code) }

    fun pair() {
        val host = ip.value.trim()
        if (host.isEmpty()) { status.value = "Enter the TV's IP address first"; return }
        disconnect(); codeQ.clear()
        Thread {
            var stage = "starting"
            try {
                bindWifi()
                stage = "connecting to $host:6467"; status.value = "Pairing: $stage…"
                val s = open(host, 6467, 0)
                val i = s.inputStream; val o = s.outputStream
                fun xchg(f: Int, body: ByteArray): Map<Int, Any> {
                    frameWrite(o, Pb.int(1, 2) + Pb.int(2, 200) + Pb.bytes(f, body))
                    val r = Pb.parse(frameRead(i))
                    if ((r[2] as? Long) != 200L) throw IOException("TV refused (status ${r[2]})")
                    return r
                }
                val enc = Pb.int(1, 3) + Pb.int(2, 6)               // hexadecimal, 6 symbols
                stage = "pairing request (1/3)"; status.value = "Pairing: $stage…"
                xchg(10, Pb.str(1, "atvremote") + Pb.str(2, "Acer Remote"))
                stage = "options (2/3)"; status.value = "Pairing: $stage…"
                xchg(20, Pb.bytes(1, enc) + Pb.int(3, 1))           // we are the input side
                stage = "configuration (3/3)"; status.value = "Pairing: $stage…"
                xchg(30, Pb.bytes(1, enc) + Pb.int(2, 1))
                stage = "waiting for the code"
                status.value = "Type the 6-character code now shown on the TV"
                askCode.value = true
                val code = codeQ.take()
                askCode.value = false
                stage = "checking the code"
                val cb = hexBytes(code)
                val sv = s.session.peerCertificates[0].publicKey as RSAPublicKey
                val cv = identity().second.publicKey as RSAPublicKey
                val md = MessageDigest.getInstance("SHA-256")
                md.update(unsignedBytes(cv.modulus)); md.update(unsignedBytes(cv.publicExponent))
                md.update(unsignedBytes(sv.modulus)); md.update(unsignedBytes(sv.publicExponent))
                md.update(cb.copyOfRange(1, cb.size))
                val hash = md.digest()
                if (hash[0] != cb[0]) throw IOException("Wrong code. Tap Pair and try again")
                stage = "sending the secret"
                xchg(40, Pb.bytes(1, hash))
                try { s.close() } catch (e: Exception) {}
                prefs.edit().putBoolean("paired", true).putString("ip", host).apply()
                status.value = "Paired! Connecting…"
                Thread.sleep(600)
                connect()
            } catch (e: Exception) {
                askCode.value = false
                status.value = "Pairing failed at $stage: ${e.message ?: e.javaClass.simpleName}"
            }
        }.start()
    }

    fun connect() {
        val host = ip.value.trim()
        if (host.isEmpty()) { status.value = "Enter the TV's IP address first"; return }
        prefs.edit().putString("ip", host).apply()
        disconnect()
        Thread {
            var s: SSLSocket? = null
            var hello = false
            try {
                bindWifi()
                status.value = "Connecting to $host:6466…"
                s = open(host, 6466, 40000)
                sock = s; out = s.outputStream
                val i = s.inputStream
                val dev = Pb.str(1, "Phone") + Pb.str(2, "Acer Remote") + Pb.int(3, 1) +
                    Pb.str(4, "1") + Pb.str(5, "com.example.acerremote") + Pb.str(6, "1.0")
                while (true) {
                    val m = Pb.parse(frameRead(i)); hello = true
                    when {
                        m[1] is ByteArray -> send(Pb.bytes(1, Pb.int(1, 622) + Pb.bytes(2, dev)))
                        m[2] is ByteArray -> { send(Pb.bytes(2, Pb.int(1, 622))); status.value = "Connected to $host"; isConnected.value = true; retry = 0 }
                        m[8] is ByteArray -> {
                            val v = (Pb.parse(m[8] as ByteArray)[1] as? Long ?: 0L).toInt()
                            send(Pb.bytes(9, Pb.int(1, v)))
                        }
                        m[20] is ByteArray -> {                       // TV: a text box got focus
                            val p = Pb.parse(m[20] as ByteArray)
                            (p[1] as? ByteArray)?.let { a -> (Pb.parse(a)[1] as? Long)?.let { imeCounter = it.toInt() } }
                            (p[2] as? ByteArray)?.let { t -> (Pb.parse(t)[1] as? Long)?.let { fieldCounter = it.toInt() } }
                            imeSeen = true
                        }
                        m[22] is ByteArray -> {                       // TV: please show the keyboard
                            val p = Pb.parse(m[22] as ByteArray)
                            (p[2] as? ByteArray)?.let { t -> (Pb.parse(t)[1] as? Long)?.let { fieldCounter = it.toInt() } }
                            imeSeen = true
                            ui.post { kbdReq.value++ }
                        }
                        m[3] is ByteArray -> status.value = "TV reported an error. Try Pair again"
                    }
                }
            } catch (e: Exception) {
                if (sock === s) {
                    out = null; sock = null; isConnected.value = false
                    val why = e.message ?: e.javaClass.simpleName
                    status.value = if (hello) "Connection lost ($why). Reconnecting…" else "$why. If this is the first time, tap Pair"
                    if (hello && fg && retry++ < 6) ui.postDelayed({ if (fg && !connected()) connect() }, 2500)
                }
            }
        }.start()
    }

    fun disconnect() {
        val s = sock; sock = null; out = null; isConnected.value = false; imeSeen = false
        try { s?.close() } catch (e: Exception) {}
    }
    fun close() {
        disconnect()
        try { disc?.let { (ctx.getSystemService(Context.NSD_SERVICE) as NsdManager).stopServiceDiscovery(it) } } catch (e: Exception) {}
    }

    private fun send(b: ByteArray) { synchronized(this) { val o = out ?: return; frameWrite(o, b) } }
    private fun safe(b: ByteArray) {
        io.execute {
            try { if (out == null) status.value = "Not connected. Tap Connect" else send(b) }
            catch (e: Exception) { status.value = "Send failed: ${e.message}" }
        }
    }

    fun key(code: Int) = safe(Pb.bytes(10, Pb.int(1, code) + Pb.int(2, 3)))   // 3 = short press
    fun app(link: String) = safe(Pb.bytes(90, Pb.str(1, link)))

    // Android TV ignores letter key presses; text must go through its text-input channel.
    fun type(s: String) {
        if (s.isEmpty()) return
        if (!imeSeen) { status.value = "On the TV, select a search box first, then type again"; return }
        val info = Pb.int(1, 1) + Pb.bytes(2, Pb.int(1, s.length) + Pb.int(2, s.length) + Pb.str(3, s))
        safe(Pb.bytes(21, Pb.int(1, imeCounter) + Pb.int(2, fieldCounter) + Pb.bytes(3, info)))
    }
}

// ---------- IR power: NEC, address 0x04, command 0x5F (bytes 04 FB 5F A0), 38 kHz ----------
fun irPower(ctx: Context) {
    val ir = ctx.getSystemService(Context.CONSUMER_IR_SERVICE) as? ConsumerIrManager
    if (ir == null || !ir.hasIrEmitter()) {
        Toast.makeText(ctx, "This phone has no IR blaster", Toast.LENGTH_SHORT).show(); return
    }
    val p = ArrayList<Int>()
    p += 9000; p += 4500
    for (b in intArrayOf(0x04, 0xFB, 0x5F, 0xA0)) for (i in 0..7) {
        p += 560; p += if (((b shr i) and 1) == 1) 1690 else 560
    }
    p += 560
    ir.transmit(38000, p.toIntArray())
}

class MainActivity : ComponentActivity() {
    private lateinit var tv: Tv

    override fun onCreate(b: Bundle?) {
        super.onCreate(b)
        val sp = getSharedPreferences("crash", 0)
        val lastCrash = sp.getString("c", null)
        val oldH = Thread.getDefaultUncaughtExceptionHandler()
        Thread.setDefaultUncaughtExceptionHandler { t, e ->
            sp.edit().putString("c", e.stackTraceToString().take(1500)).commit()
            oldH?.uncaughtException(t, e)
        }
        tv = Tv(this)
        if (tv.ip.value.isBlank()) tv.discover()
        setContent {
            val mic = rememberLauncherForActivityResult(ActivityResultContracts.StartActivityForResult()) { res ->
                res.data?.getStringArrayListExtra(RecognizerIntent.EXTRA_RESULTS)?.firstOrNull()?.let { tv.type(it) }
            }
            MaterialTheme(colorScheme = darkColorScheme(primary = Color(0xFF4FC3F7), onPrimary = Color.Black)) { RemoteUi(
                tv, crash = lastCrash,
                onPower = { irPower(this) },
                onMic = {
                    mic.launch(
                        Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
                            .putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
                    )
                }
            ) }
        }
    }
    override fun onStart() { super.onStart(); tv.onStart() }
    override fun onStop() { tv.onStop(); super.onStop() }
    override fun onDestroy() { tv.close(); super.onDestroy() }
}

// Tap with haptic tick; hold to repeat (arrows, volume, channel, delete).
@Composable
fun Modifier.press(rep: Boolean = false, on: () -> Unit): Modifier {
    val scope = rememberCoroutineScope()
    val haptic = LocalHapticFeedback.current
    val cur by rememberUpdatedState(on)
    return pointerInput(rep) {
        detectTapGestures(onPress = {
            haptic.performHapticFeedback(HapticFeedbackType.TextHandleMove)
            cur()
            if (rep) {
                val job = scope.launch { delay(450); while (true) { cur(); delay(90) } }
                tryAwaitRelease(); job.cancel()
            }
        })
    }
}

@Composable
fun B(
    t: String, w: Dp = 64.dp, h: Dp = 48.dp, bg: Color = Color(0xFF242424), fg: Color = Color.White,
    rad: Dp = 24.dp, fs: Int = 14, rep: Boolean = false, on: () -> Unit
) = Box(
    Modifier.size(w, h).clip(RoundedCornerShape(rad)).background(bg).press(rep, on),
    Alignment.Center
) { Text(t, color = fg, fontSize = fs.sp, fontWeight = FontWeight.Bold, textAlign = TextAlign.Center) }

@Composable
fun Rocker(label: String, up: () -> Unit, down: () -> Unit) = Column(
    Modifier.size(64.dp, 150.dp).clip(RoundedCornerShape(32.dp)).background(Color(0xFF242424)),
    Arrangement.Center, Alignment.CenterHorizontally
) {
    Box(Modifier.weight(1f).fillMaxWidth().press(true, up), Alignment.Center) { Text("+", color = Color.White, fontSize = 22.sp) }
    Text(label, color = Color.White, fontSize = 11.sp, fontWeight = FontWeight.Bold)
    Box(Modifier.weight(1f).fillMaxWidth().press(true, down), Alignment.Center) { Text("−", color = Color.White, fontSize = 22.sp) }
}

@OptIn(ExperimentalComposeUiApi::class)
@Composable
fun RemoteUi(t: Tv, onPower: () -> Unit, onMic: () -> Unit, crash: String? = null) {
    val light = Color(0xFFEDEDE8)
    val row = Modifier.fillMaxWidth()
    var text by remember { mutableStateOf("") }
    var code by remember { mutableStateOf("") }
    val focus = remember { FocusRequester() }
    val kbd = LocalSoftwareKeyboardController.current
    LaunchedEffect(t.kbdReq.value) {
        if (t.kbdReq.value > 0) { try { focus.requestFocus(); kbd?.show() } catch (e: Exception) {} }
    }

    Column(
        Modifier.fillMaxSize().background(Color(0xFF0B0B0B)).verticalScroll(rememberScrollState())
            .statusBarsPadding().padding(16.dp),
        Arrangement.spacedBy(12.dp), Alignment.CenterHorizontally
    ) {
        crash?.let { Text("Last crash:\n$it", color = Color(0xFFFF8A80), fontSize = 9.sp) }
        Text(t.status.value, color = Color(0xFF9AD), fontSize = 12.sp, textAlign = TextAlign.Center)
        if (t.isConnected.value) {
            TextButton(onClick = { t.disconnect() }) { Text("Change TV") }
        } else {
            OutlinedTextField(
                t.ip.value, { t.ip.value = it.filter { c -> c.isDigit() || c == '.' } }, Modifier.fillMaxWidth(),
                singleLine = true, label = { Text("TV IP address, e.g. 192.168.1.20") },
                keyboardOptions = KeyboardOptions(keyboardType = KeyboardType.Decimal)
            )
            Row(row, Arrangement.SpaceEvenly) {
                OutlinedButton(onClick = { t.discover() }) { Text("Find TV") }
                OutlinedButton(onClick = { t.pair() }) { Text("Pair") }
                Button(onClick = { t.connect() }) { Text("Connect") }
            }
            t.found.forEach { (n, h) -> TextButton(onClick = { t.ip.value = h }) { Text("$n  –  $h") } }
            if (t.askCode.value) {
                Row(row, Arrangement.spacedBy(8.dp), Alignment.CenterVertically) {
                    OutlinedTextField(code, { code = it.uppercase() }, Modifier.weight(1f), singleLine = true, label = { Text("Code from TV") })
                    Button(onClick = { t.submit(code); code = "" }) { Text("OK") }
                }
            }
        }

        Column(
            Modifier.width(300.dp).clip(RoundedCornerShape(32.dp)).background(Color(0xFF151515)).padding(vertical = 20.dp),
            Arrangement.spacedBy(14.dp), Alignment.CenterHorizontally
        ) {
            Row(row, Arrangement.SpaceEvenly) {
                B("⏻", bg = Color(0xFFC62828), fs = 20, on = onPower)      // IR
                B("🔇") { t.key(164) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("YouTube", 112.dp, bg = light, fg = Color(0xFFD32F2F), fs = 12) { t.app("https://www.youtube.com") }
                B("NETFLIX", 112.dp, bg = light, fg = Color(0xFFD32F2F), fs = 12) { t.app("https://www.netflix.com/title") }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("prime video", 112.dp, bg = light, fg = Color.Black, fs = 12) { t.app("https://app.primevideo.com") }
                B("▦", 112.dp, bg = light, fg = Color.Black, fs = 18) { t.key(284) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("👤") { t.key(288) }
                B("🎤", bg = light, fg = Color.Black, on = onMic)
                B("⚙", fs = 20) { t.key(176) }
            }

            Box(Modifier.size(210.dp).clip(CircleShape).background(light), Alignment.Center) {
                Box(Modifier.align(Alignment.TopCenter)) { B("▲", 70.dp, 56.dp, Color.Transparent, Color.Black, rep = true) { t.key(19) } }
                Box(Modifier.align(Alignment.BottomCenter)) { B("▼", 70.dp, 56.dp, Color.Transparent, Color.Black, rep = true) { t.key(20) } }
                Box(Modifier.align(Alignment.CenterStart)) { B("◀", 56.dp, 70.dp, Color.Transparent, Color.Black, rep = true) { t.key(21) } }
                Box(Modifier.align(Alignment.CenterEnd)) { B("▶", 56.dp, 70.dp, Color.Transparent, Color.Black, rep = true) { t.key(22) } }
                B("OK", 84.dp, 84.dp, Color(0xFF111111), rad = 42.dp, fs = 18) { t.key(23) }
            }

            Row(row, Arrangement.SpaceEvenly) {
                B("←", fs = 22) { t.key(4) }
                B("⌂", bg = light, fg = Color.Black, fs = 22) { t.key(3) }
                B("📺") { t.key(172) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("⏮") { t.key(88) }
                B("Live TV", 80.dp, 48.dp, Color(0xFF1565C0), fs = 12) { t.key(170) }
                B("⏭") { t.key(87) }
            }
            Row(row, Arrangement.SpaceEvenly, Alignment.CenterVertically) {
                Rocker("VOL", { t.key(24) }, { t.key(25) })
                Column(verticalArrangement = Arrangement.spacedBy(14.dp)) {
                    B("MENU", 76.dp, 40.dp, fs = 11) { t.key(82) }
                    B("SOURCE", 76.dp, 40.dp, fs = 11) { t.key(178) }
                }
                Rocker("CH", { t.key(166) }, { t.key(167) })
            }
        }

        Row(row, Arrangement.spacedBy(6.dp), Alignment.CenterVertically) {
            OutlinedTextField(
                text, { text = it }, Modifier.weight(1f).focusRequester(focus), singleLine = true,
                placeholder = { Text("Type to TV") },
                keyboardOptions = KeyboardOptions(imeAction = ImeAction.Send),
                keyboardActions = KeyboardActions(onSend = { t.type(text); text = "" })
            )
            Button(onClick = { t.type(text); text = "" }) { Text("Send") }
            B("⌫", 48.dp, 48.dp, rep = true) { t.key(67) }
            B("↵", 48.dp, 48.dp) { t.key(66) }
        }
    }
}
