package com.example.acerremote   // change to your package; minSdk 28, Compose + material3

import android.Manifest
import android.annotation.SuppressLint
import android.bluetooth.*
import android.content.*
import android.hardware.ConsumerIrManager
import android.os.*
import android.speech.RecognizerIntent
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.foundation.*
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.shape.*
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.*
import java.util.concurrent.Executors

// ---------- HID report descriptor: keyboard (ID 1) + consumer control (ID 2) ----------
private val DESC = intArrayOf(
    0x05, 0x01, 0x09, 0x06, 0xA1, 0x01, 0x85, 0x01,
    0x05, 0x07, 0x19, 0xE0, 0x29, 0xE7, 0x15, 0x00, 0x25, 0x01, 0x75, 0x01, 0x95, 0x08, 0x81, 0x02,
    0x95, 0x01, 0x75, 0x08, 0x81, 0x01,
    0x95, 0x06, 0x75, 0x08, 0x15, 0x00, 0x25, 0x65, 0x05, 0x07, 0x19, 0x00, 0x29, 0x65, 0x81, 0x00,
    0xC0,
    0x05, 0x0C, 0x09, 0x01, 0xA1, 0x01, 0x85, 0x02,
    0x15, 0x00, 0x26, 0xFF, 0x03, 0x19, 0x00, 0x2A, 0xFF, 0x03, 0x75, 0x10, 0x95, 0x01, 0x81, 0x00,
    0xC0
).map { it.toByte() }.toByteArray()

// Keyboard usages
private const val K_UP = 0x52; private const val K_DOWN = 0x51
private const val K_LEFT = 0x50; private const val K_RIGHT = 0x4F
private const val K_ENTER = 0x28; private const val K_BKSP = 0x2A
// Consumer usages
private const val C_BACK = 0x224; private const val C_HOME = 0x223; private const val C_MENU = 0x40
private const val C_SETTINGS = 0x209; private const val C_MUTE = 0xE2
private const val C_VOLUP = 0xE9; private const val C_VOLDN = 0xEA
private const val C_CHUP = 0x9C; private const val C_CHDN = 0x9D
private const val C_NEXT = 0xB5; private const val C_PREV = 0xB6
private const val C_GUIDE = 0x8D; private const val C_TV = 0x89

@SuppressLint("MissingPermission")
class HidRemote(private val ctx: Context) {
    val status = mutableStateOf("Starting…")
    private val ad: BluetoothAdapter? =
        (ctx.getSystemService(Context.BLUETOOTH_SERVICE) as BluetoothManager).adapter
    private var hid: BluetoothHidDevice? = null
    private var host: BluetoothDevice? = null
    private val ui = Handler(Looper.getMainLooper())
    private val prefs = ctx.getSharedPreferences("remote", 0)

    private val cb = object : BluetoothHidDevice.Callback() {
        override fun onAppStatusChanged(pluggedDevice: BluetoothDevice?, registered: Boolean) {
            status.value = if (registered) "Ready. Tap “Make visible”, then pair from the TV"
            else "HID registration failed"
        }
        override fun onConnectionStateChanged(device: BluetoothDevice, state: Int) {
            if (state == BluetoothProfile.STATE_CONNECTED) {
                host = device
                prefs.edit().putString("mac", device.address).apply()
                status.value = "Connected to ${device.name ?: device.address}"
            } else if (state == BluetoothProfile.STATE_DISCONNECTED && device == host) {
                host = null; status.value = "Disconnected"
            }
        }
    }

    // After the TV bonds with us, open the HID connection ourselves too.
    private val bondRx = object : BroadcastReceiver() {
        override fun onReceive(c: Context, i: Intent) {
            @Suppress("DEPRECATION")
            val d = i.getParcelableExtra<BluetoothDevice>(BluetoothDevice.EXTRA_DEVICE) ?: return
            if (i.getIntExtra(BluetoothDevice.EXTRA_BOND_STATE, 0) == BluetoothDevice.BOND_BONDED) hid?.connect(d)
        }
    }

    fun start() {
        val a = ad ?: run { status.value = "No Bluetooth"; return }
        ctx.registerReceiver(bondRx, IntentFilter(BluetoothDevice.ACTION_BOND_STATE_CHANGED))
        val ok = a.getProfileProxy(ctx, object : BluetoothProfile.ServiceListener {
            override fun onServiceConnected(p: Int, proxy: BluetoothProfile) {
                val h = proxy as BluetoothHidDevice
                hid = h
                val sdp = BluetoothHidDeviceAppSdpSettings(
                    "RC-525G", "Remote Control", "Acer",
                    BluetoothHidDevice.SUBCLASS1_COMBO, DESC
                )
                if (!h.registerApp(sdp, null, null, Executors.newSingleThreadExecutor(), cb))
                    status.value = "registerApp failed"
            }
            override fun onServiceDisconnected(p: Int) { hid = null }
        }, BluetoothProfile.HID_DEVICE)
        if (!ok) status.value = "This phone doesn't support Bluetooth HID device mode"
    }

    fun reconnect() {
        val m = prefs.getString("mac", null) ?: return
        ad?.getRemoteDevice(m)?.let { hid?.connect(it) }
    }

    private fun send(id: Int, d: ByteArray) { val h = host ?: return; hid?.sendReport(h, id, d) }
    fun cons(u: Int) {
        send(2, byteArrayOf(u.toByte(), (u shr 8).toByte()))
        ui.postDelayed({ send(2, ByteArray(2)) }, 40)
    }
    fun key(k: Int, mod: Int = 0) {
        send(1, byteArrayOf(mod.toByte(), 0, k.toByte(), 0, 0, 0, 0, 0))
        ui.postDelayed({ send(1, ByteArray(8)) }, 40)
    }
    fun type(s: String) {
        Thread {
            for (c in s) {
                val (k, m) = usage(c) ?: continue
                send(1, byteArrayOf(m.toByte(), 0, k.toByte(), 0, 0, 0, 0, 0)); Thread.sleep(30)
                send(1, ByteArray(8)); Thread.sleep(30)
            }
        }.start()
    }
    private fun usage(c: Char): Pair<Int, Int>? = when (c) {
        in 'a'..'z' -> Pair(0x04 + (c - 'a'), 0)
        in 'A'..'Z' -> Pair(0x04 + (c - 'A'), 2)
        in '1'..'9' -> Pair(0x1E + (c - '1'), 0)
        '0' -> Pair(0x27, 0); ' ' -> Pair(0x2C, 0); '.' -> Pair(0x37, 0)
        ',' -> Pair(0x36, 0); '-' -> Pair(0x2D, 0); '/' -> Pair(0x38, 0); '@' -> Pair(0x1F, 2)
        else -> null
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
    private lateinit var r: HidRemote

    override fun onCreate(b: Bundle?) {
        super.onCreate(b)
        r = HidRemote(this)
        val perms = if (Build.VERSION.SDK_INT >= 31)
            arrayOf(Manifest.permission.BLUETOOTH_CONNECT, Manifest.permission.BLUETOOTH_ADVERTISE)
        else arrayOf()
        setContent {
            val ask = rememberLauncherForActivityResult(ActivityResultContracts.RequestMultiplePermissions()) { r.start() }
            val mic = rememberLauncherForActivityResult(ActivityResultContracts.StartActivityForResult()) { res ->
                res.data?.getStringArrayListExtra(RecognizerIntent.EXTRA_RESULTS)?.firstOrNull()?.let { r.type(it) }
            }
            LaunchedEffect(Unit) { if (perms.isEmpty()) r.start() else ask.launch(perms) }
            RemoteUi(
                r,
                onPower = { irPower(this) },
                onVisible = {
                    startActivity(
                        Intent(BluetoothAdapter.ACTION_REQUEST_DISCOVERABLE)
                            .putExtra(BluetoothAdapter.EXTRA_DISCOVERABLE_DURATION, 300)
                    )
                },
                onMic = {
                    mic.launch(
                        Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
                            .putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
                    )
                }
            )
        }
    }
}

@Composable
fun B(
    t: String, w: Dp = 64.dp, h: Dp = 48.dp, bg: Color = Color(0xFF242424), fg: Color = Color.White,
    rad: Dp = 24.dp, fs: Int = 14, on: () -> Unit
) = Box(
    Modifier.size(w, h).clip(RoundedCornerShape(rad)).background(bg).clickable(onClick = on),
    Alignment.Center
) { Text(t, color = fg, fontSize = fs.sp, fontWeight = FontWeight.Bold, textAlign = TextAlign.Center) }

@Composable
fun Rocker(label: String, up: () -> Unit, down: () -> Unit) = Column(
    Modifier.size(64.dp, 150.dp).clip(RoundedCornerShape(32.dp)).background(Color(0xFF242424)),
    Arrangement.Center, Alignment.CenterHorizontally
) {
    Box(Modifier.weight(1f).fillMaxWidth().clickable(onClick = up), Alignment.Center) { Text("+", color = Color.White, fontSize = 22.sp) }
    Text(label, color = Color.White, fontSize = 11.sp, fontWeight = FontWeight.Bold)
    Box(Modifier.weight(1f).fillMaxWidth().clickable(onClick = down), Alignment.Center) { Text("−", color = Color.White, fontSize = 22.sp) }
}

@Composable
fun RemoteUi(r: HidRemote, onPower: () -> Unit, onVisible: () -> Unit, onMic: () -> Unit) {
    val ctx = androidx.compose.ui.platform.LocalContext.current
    val vendor = { Toast.makeText(ctx, "Vendor key: not available over standard Bluetooth HID", Toast.LENGTH_SHORT).show() }
    val light = Color(0xFFEDEDE8)
    val row = Modifier.fillMaxWidth()
    var text by remember { mutableStateOf("") }

    Column(
        Modifier.fillMaxSize().background(Color(0xFF0B0B0B)).verticalScroll(rememberScrollState())
            .statusBarsPadding().padding(16.dp),
        Arrangement.spacedBy(14.dp), Alignment.CenterHorizontally
    ) {
        Text(r.status.value, color = Color(0xFF9AD), fontSize = 12.sp, textAlign = TextAlign.Center)
        Row(row, Arrangement.SpaceEvenly) {
            Button(onClick = onVisible) { Text("Make visible") }
            OutlinedButton(onClick = { r.reconnect() }) { Text("Reconnect") }
        }

        Column(
            Modifier.width(300.dp).clip(RoundedCornerShape(32.dp)).background(Color(0xFF151515)).padding(vertical = 20.dp),
            Arrangement.spacedBy(14.dp), Alignment.CenterHorizontally
        ) {
            Row(row, Arrangement.SpaceEvenly) {
                B("⏻", bg = Color(0xFFC62828), fs = 20, on = onPower)      // IR
                B("🔇") { r.cons(C_MUTE) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("YouTube", 112.dp, bg = light, fg = Color(0xFFD32F2F), fs = 12) { vendor() }
                B("NETFLIX", 112.dp, bg = light, fg = Color(0xFFD32F2F), fs = 12) { vendor() }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("prime video", 112.dp, bg = light, fg = Color.Black, fs = 12) { vendor() }
                B("▦", 112.dp, bg = light, fg = Color.Black, fs = 18) { vendor() }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("👤") { vendor() }
                B("🎤", bg = light, fg = Color.Black, on = onMic)
                B("⚙", fs = 20) { r.cons(C_SETTINGS) }
            }

            Box(Modifier.size(210.dp).clip(CircleShape).background(light), Alignment.Center) {
                Box(Modifier.align(Alignment.TopCenter)) { B("▲", 70.dp, 56.dp, Color.Transparent, Color.Black) { r.key(K_UP) } }
                Box(Modifier.align(Alignment.BottomCenter)) { B("▼", 70.dp, 56.dp, Color.Transparent, Color.Black) { r.key(K_DOWN) } }
                Box(Modifier.align(Alignment.CenterStart)) { B("◀", 56.dp, 70.dp, Color.Transparent, Color.Black) { r.key(K_LEFT) } }
                Box(Modifier.align(Alignment.CenterEnd)) { B("▶", 56.dp, 70.dp, Color.Transparent, Color.Black) { r.key(K_RIGHT) } }
                B("OK", 72.dp, 72.dp, Color(0xFF242424), Color.White, fs = 15) { r.key(K_ENTER) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("Back") { r.cons(C_BACK) }; B("Home") { r.cons(C_HOME) }; B("Menu") { r.cons(C_MENU) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("−") { r.cons(C_VOLDN) }; B("Mute") { r.cons(C_MUTE) }; B("+") { r.cons(C_VOLUP) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("CH−") { r.cons(C_CHDN) }; B("Guide") { r.cons(C_GUIDE) }; B("CH+") { r.cons(C_CHUP) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("Prev") { r.cons(C_PREV) }; B("Play/Pause") { r.cons(C_NEXT) }; B("Next") { r.cons(C_NEXT) }
            }
        }

        OutlinedTextField(value = text, onValueChange = { text = it }, label = { Text("Type on TV") }, modifier = Modifier.fillMaxWidth())
        Button(onClick = { r.type(text) }, modifier = Modifier.fillMaxWidth()) { Text("Send text") }
    }
}
