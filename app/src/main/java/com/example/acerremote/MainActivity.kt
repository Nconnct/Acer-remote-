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
import android.bluetooth.BluetoothGattCharacteristic as GC
import android.bluetooth.BluetoothGattDescriptor as GD
import android.bluetooth.le.*
import java.util.UUID
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

private fun U(x: Int): UUID = UUID.fromString(String.format("%08x-0000-1000-8000-00805f9b34fb", x))

// BLE HID-over-GATT peripheral: advertises exactly like the real remote (HID service 0x1812)
@SuppressLint("MissingPermission")
class HidRemote(private val ctx: Context) {
    val status = mutableStateOf("Starting…")
    val version = mutableStateOf(0)
    private val bm = ctx.getSystemService(Context.BLUETOOTH_SERVICE) as BluetoothManager
    private val ad: BluetoothAdapter? = bm.adapter
    private var server: BluetoothGattServer? = null
    private var host: BluetoothDevice? = null
    private var oldName: String? = null
    private val pending = ArrayDeque<BluetoothGattService>()
    private val kbd = GC(U(0x2A4D), GC.PROPERTY_READ or GC.PROPERTY_NOTIFY, GC.PERMISSION_READ_ENCRYPTED)
    private val con = GC(U(0x2A4D), GC.PROPERTY_READ or GC.PROPERTY_NOTIFY, GC.PERMISSION_READ_ENCRYPTED)
    private val ui = Handler(Looper.getMainLooper())
    private var ble = "starting"
    private var cls = "starting"
    private var chid: BluetoothHidDevice? = null
    private var chost: BluetoothDevice? = null
    private var classicStarted = false
    private fun upd() { status.value = "BLE: $ble\nClassic: $cls" }

    private val ccb = object : BluetoothHidDevice.Callback() {
        override fun onConnectionStateChanged(d: BluetoothDevice, st: Int) {
            if (st == BluetoothProfile.STATE_CONNECTED) { chost = d; cls = "connected to ${d.name ?: d.address}"; upd() }
            else if (d == chost) { chost = null; cls = "disconnected"; upd() }
        }
    }
    private val bondRx = object : BroadcastReceiver() {
        override fun onReceive(c: Context, i: Intent) {
            @Suppress("DEPRECATION")
            val d = i.getParcelableExtra<BluetoothDevice>(BluetoothDevice.EXTRA_DEVICE) ?: return
            if (i.getIntExtra(BluetoothDevice.EXTRA_BOND_STATE, 0) == BluetoothDevice.BOND_BONDED && host == null) chid?.connect(d)
        }
    }
    private fun startClassic(a: BluetoothAdapter) {
        if (classicStarted) return
        classicStarted = true
        ctx.registerReceiver(bondRx, IntentFilter(BluetoothDevice.ACTION_BOND_STATE_CHANGED))
        val ok = a.getProfileProxy(ctx, object : BluetoothProfile.ServiceListener {
            override fun onServiceConnected(p: Int, proxy: BluetoothProfile) {
                val h = proxy as BluetoothHidDevice
                chid = h
                val sdp = BluetoothHidDeviceAppSdpSettings("RC-525G Phone", "Remote Control", "Acer",
                    BluetoothHidDevice.SUBCLASS1_COMBO, DESC)
                cls = if (h.registerApp(sdp, null, null, Executors.newSingleThreadExecutor(), ccb)) "registered" else "registerApp FAILED"
                upd()
            }
            override fun onServiceDisconnected(p: Int) { chid = null }
        }, BluetoothProfile.HID_DEVICE)
        if (!ok) { cls = "NOT supported by this phone"; upd() }
    }
    private fun out(id: Int, c: GC, d: ByteArray) {
        nfy(c, d)
        chost?.let { chid?.sendReport(it, id, d) }
    }

    private fun ro(u: Int, v: ByteArray, enc: Boolean) =
        GC(U(u), GC.PROPERTY_READ, if (enc) GC.PERMISSION_READ_ENCRYPTED else GC.PERMISSION_READ).also { it.setValue(v) }

    private fun report(c: GC, id: Int) {
        c.setValue(ByteArray(if (id == 1) 8 else 2))
        c.addDescriptor(GD(U(0x2908), GD.PERMISSION_READ_ENCRYPTED).also { it.setValue(byteArrayOf(id.toByte(), 1)) })
        c.addDescriptor(GD(U(0x2902), GD.PERMISSION_READ_ENCRYPTED or GD.PERMISSION_WRITE_ENCRYPTED))
    }

    private fun build() {
        report(kbd, 1); report(con, 2)
        val prim = BluetoothGattService.SERVICE_TYPE_PRIMARY
        val dis = BluetoothGattService(U(0x180A), prim).apply {
            addCharacteristic(ro(0x2A29, "Acer".toByteArray(), false))
            addCharacteristic(ro(0x2A50, byteArrayOf(0x02, 0x34, 0x12, 0x78, 0x56, 0x01, 0x00), false))
        }
        val bat = BluetoothGattService(U(0x180F), prim).apply {
            addCharacteristic(GC(U(0x2A19), GC.PROPERTY_READ or GC.PROPERTY_NOTIFY, GC.PERMISSION_READ).also {
                it.setValue(byteArrayOf(100))
                it.addDescriptor(GD(U(0x2902), GD.PERMISSION_READ or GD.PERMISSION_WRITE))
            })
        }
        val hid = BluetoothGattService(U(0x1812), prim).apply {
            addCharacteristic(ro(0x2A4A, byteArrayOf(0x11, 0x01, 0x00, 0x02), true))
            addCharacteristic(ro(0x2A4B, DESC, true))
            addCharacteristic(GC(U(0x2A4C), GC.PROPERTY_WRITE_NO_RESPONSE, GC.PERMISSION_WRITE))
            addCharacteristic(GC(U(0x2A4E), GC.PROPERTY_READ or GC.PROPERTY_WRITE_NO_RESPONSE,
                GC.PERMISSION_READ or GC.PERMISSION_WRITE).also { it.setValue(byteArrayOf(1)) })
            addCharacteristic(kbd); addCharacteristic(con)
        }
        pending.addAll(listOf(dis, bat, hid))
    }

    private fun addNext() {
        val s = pending.removeFirstOrNull()
        if (s != null) server?.addService(s) else advertise()
    }

    private val srv = object : BluetoothGattServerCallback() {
        override fun onServiceAdded(st: Int, service: BluetoothGattService) { addNext() }
        override fun onConnectionStateChange(d: BluetoothDevice, st: Int, ns: Int) {
            if (ns == BluetoothProfile.STATE_CONNECTED) {
                host = d; ble = "connected to ${d.name ?: d.address}"; upd()
            } else {
                if (d == host) host = null
                ble = "disconnected, advertising again"; upd()
                advertise()
            }
        }
        override fun onCharacteristicReadRequest(d: BluetoothDevice, id: Int, off: Int, c: GC) {
            val v = c.value ?: ByteArray(0)
            server?.sendResponse(d, id, BluetoothGatt.GATT_SUCCESS, off, if (off < v.size) v.copyOfRange(off, v.size) else ByteArray(0))
        }
        override fun onDescriptorReadRequest(d: BluetoothDevice, id: Int, off: Int, ds: GD) {
            val v = ds.value ?: ByteArray(2)
            server?.sendResponse(d, id, BluetoothGatt.GATT_SUCCESS, off, if (off < v.size) v.copyOfRange(off, v.size) else ByteArray(0))
        }
        override fun onDescriptorWriteRequest(d: BluetoothDevice, id: Int, ds: GD, prep: Boolean, resp: Boolean, off: Int, v: ByteArray) {
            ds.setValue(v)
            if (resp) server?.sendResponse(d, id, BluetoothGatt.GATT_SUCCESS, 0, null)
        }
        override fun onCharacteristicWriteRequest(d: BluetoothDevice, id: Int, c: GC, prep: Boolean, resp: Boolean, off: Int, v: ByteArray) {
            c.setValue(v)
            if (resp) server?.sendResponse(d, id, BluetoothGatt.GATT_SUCCESS, 0, null)
        }
    }

    private val advCb = object : AdvertiseCallback() {
        override fun onStartSuccess(s: AdvertiseSettings) {
            if (host == null) { ble = "advertising OK"; upd() }
        }
        override fun onStartFailure(e: Int) { if (e != ADVERTISE_FAILED_ALREADY_STARTED) { ble = "advertising FAILED, code $e"; upd() } }
    }

    private fun advertise() {
        val adv = ad?.bluetoothLeAdvertiser ?: return
        adv.stopAdvertising(advCb)
        val set = AdvertiseSettings.Builder().setAdvertiseMode(AdvertiseSettings.ADVERTISE_MODE_LOW_LATENCY)
            .setTxPowerLevel(AdvertiseSettings.ADVERTISE_TX_POWER_HIGH).setConnectable(true).setTimeout(0).build()
        val data = AdvertiseData.Builder().setIncludeDeviceName(true).addServiceUuid(ParcelUuid(U(0x1812))).build()
        val scan = AdvertiseData.Builder().setIncludeDeviceName(true).build()
        adv.startAdvertising(set, data, scan, advCb)
    }

    fun start() {
        version.value++
        try {
            val a = ad ?: run { status.value = "No Bluetooth"; return }
            if (!a.isEnabled) { status.value = "Turn Bluetooth on first"; return }
            if (oldName == null) oldName = a.name
            a.name = "RC-525G Phone"
            startClassic(a)
            if (a.bluetoothLeAdvertiser == null) { ble = "NOT supported by this phone"; upd(); return }
            if (server != null) { advertise(); return }
            server = bm.openGattServer(ctx, srv)
            build(); addNext()
        } catch (e: Throwable) {
            status.value = "Error: ${e.javaClass.simpleName}. Allow “Nearby devices” permission, then tap Make visible"
        }
    }

    fun bonded(): List<BluetoothDevice> =
        try { ad?.bondedDevices?.toList() ?: emptyList() } catch (e: Throwable) { emptyList() }
    fun nameOf(d: BluetoothDevice): String = try { d.name ?: d.address } catch (e: Throwable) { d.address }
    fun connectTo(d: BluetoothDevice) {
        try {
            cls = "connecting to ${nameOf(d)}…"; upd()
            if (chid?.connect(d) != true) { cls = "connect request failed (app not registered?)"; upd() }
        } catch (e: Throwable) { cls = "error: ${e.javaClass.simpleName}"; upd() }
    }

    fun stop() {
        try {
            ad?.bluetoothLeAdvertiser?.stopAdvertising(advCb)
            server?.close(); server = null
            chid?.unregisterApp()
            if (classicStarted) ctx.unregisterReceiver(bondRx)
            oldName?.let { ad?.name = it }
        } catch (e: Throwable) { }
    }

    private fun nfy(c: GC, d: ByteArray) {
        val h = host ?: return
        c.setValue(d); server?.notifyCharacteristicChanged(h, c, false)
    }
    fun cons(u: Int) {
        out(2, con, byteArrayOf(u.toByte(), (u shr 8).toByte()))
        ui.postDelayed({ out(2, con, ByteArray(2)) }, 40)
    }
    fun key(k: Int, mod: Int = 0) {
        out(1, kbd, byteArrayOf(mod.toByte(), 0, k.toByte(), 0, 0, 0, 0, 0))
        ui.postDelayed({ out(1, kbd, ByteArray(8)) }, 40)
    }
    fun type(s: String) {
        Thread {
            for (c in s) {
                val (k, m) = usage(c) ?: continue
                out(1, kbd, byteArrayOf(m.toByte(), 0, k.toByte(), 0, 0, 0, 0, 0)); Thread.sleep(35)
                out(1, kbd, ByteArray(8)); Thread.sleep(35)
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
    override fun onDestroy() { r.stop(); super.onDestroy() }

    override fun onCreate(b: Bundle?) {
        super.onCreate(b)
        val sp = getSharedPreferences("crash", 0)
        val lastCrash = sp.getString("c", null)
        val oldH = Thread.getDefaultUncaughtExceptionHandler()
        Thread.setDefaultUncaughtExceptionHandler { t, e ->
            sp.edit().putString("c", e.stackTraceToString().take(1500)).commit()
            oldH?.uncaughtException(t, e)
        }
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
                crash = lastCrash,
                onPower = { irPower(this) },
                onVisible = {
                    r.start()
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
fun RemoteUi(r: HidRemote, onPower: () -> Unit, onVisible: () -> Unit, onMic: () -> Unit, crash: String? = null) {
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
        crash?.let { Text("Last crash:\n$it", color = Color(0xFFFF8A80), fontSize = 9.sp) }
        Text(r.status.value, color = Color(0xFF9AD), fontSize = 12.sp, textAlign = TextAlign.Center)
        var tick by remember { mutableStateOf(0) }
        val devs = remember(tick, r.version.value) { r.bonded() }
        Button(onClick = { ctx.startActivity(Intent(android.provider.Settings.ACTION_BLUETOOTH_SETTINGS)) }) {
            Text("1. Pair TV from phone Bluetooth settings")
        }
        Row(row, Arrangement.SpaceEvenly) {
            OutlinedButton(onClick = { tick++ }) { Text("2. Refresh list") }
            OutlinedButton(onClick = onVisible) { Text("Make visible") }
        }
        devs.forEach { d ->
            Button(onClick = { r.connectTo(d) }, Modifier.fillMaxWidth()) { Text("3. Connect: ${r.nameOf(d)}") }
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
                B("OK", 84.dp, 84.dp, Color(0xFF111111), rad = 42.dp, fs = 18) { r.key(K_ENTER) }
            }

            Row(row, Arrangement.SpaceEvenly) {
                B("←", fs = 22) { r.cons(C_BACK) }
                B("⌂", bg = light, fg = Color.Black, fs = 22) { r.cons(C_HOME) }
                B("📺") { r.cons(C_GUIDE) }
            }
            Row(row, Arrangement.SpaceEvenly) {
                B("⏮") { r.cons(C_PREV) }
                B("Live TV", 80.dp, 48.dp, Color(0xFF1565C0), fs = 12) { r.cons(C_TV) }
                B("⏭") { r.cons(C_NEXT) }
            }
            Row(row, Arrangement.SpaceEvenly, Alignment.CenterVertically) {
                Rocker("VOL", { r.cons(C_VOLUP) }, { r.cons(C_VOLDN) })
                Column(verticalArrangement = Arrangement.spacedBy(14.dp)) {
                    B("MENU", 76.dp, 40.dp, fs = 11) { r.cons(C_MENU) }
                    B("SOURCE", 76.dp, 40.dp, fs = 11) { r.cons(C_TV) }
                }
                Rocker("CH", { r.cons(C_CHUP) }, { r.cons(C_CHDN) })
            }
        }

        Row(row, Arrangement.spacedBy(8.dp), Alignment.CenterVertically) {
            OutlinedTextField(text, { text = it }, Modifier.weight(1f), singleLine = true, placeholder = { Text("Type to TV") })
            Button(onClick = { r.type(text); text = "" }) { Text("Send") }
            Button(onClick = { r.key(K_BKSP) }) { Text("⌫") }
        }
    }
}
