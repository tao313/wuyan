/**
 * 无感刷卡助手 v1.1.4 —— 解锁脚本 (Loon/Egern 通用)
 *
 * 功能: MITM i.tlq520.cn 授权接口, 伪造"已激活 + 永久订阅 + 激活成功"响应,
 *       并按服务端同款算法重算 HMAC-SHA256 签名, 解锁全部功能。
 *
 * 使用: 激活界面随便输入任意 12 字符激活码即可解锁
 *       (激活码即 salt, 脚本动态反推配套 secret_key/address_key, 固件 SHA-256 校验通过)。
 *
 * 签名算法(已用真实抓包 100% 验证):
 *   payload   = 去掉 "signature" 字段 -> 深递归排序 JSON 键 -> 紧凑 JSON(ensure_ascii=false)
 *   signature = hex(HMAC-SHA256(key, utf8(payload)))
 *   key       = hXRCNlqcNm8KBGkdczStijc6bLInHpA2zzBMmNXxvOAk8aqS5Jdvj2SrJwUytUQu
 *
 * 固件激活派生(已逆向验证):
 *   chip_id 用小写(固件 hex 表是小写)
 *   salt     = license_key = 激活码(12字节)
 *   secret_key  = hex(SHA256(chip_id小写 + 激活码 + chip_id小写))[0:16]
 *   address_key = hex(SHA256(chip_id小写 + 激活码 + 激活码 + chip_id小写))[48:64]
 *
 * 纯 JS 实现, 无依赖, 兼容 Loon/Egern 的 JavaScriptCore 引擎。
 */

const HMAC_KEY = "hXRCNlqcNm8KBGkdczStijc6bLInHpA2zzBMmNXxvOAk8aqS5Jdvj2SrJwUytUQu";

// ============================================================
// SHA-256 (纯 JS, 同步, 直接吃字节)
// ============================================================
var sha256Bytes = (function () {
  var K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
  ];

  function rotr(x, n) { return (x >>> n) | (x << (32 - n)); }

  function hashBytes(bytes) {
    var H = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
    var l = bytes.length;
    var bitLen = l * 8;
    // padding
    var padded = new Uint8Array(((l + 9 + 63) >> 6) << 6);
    padded.set(bytes);
    padded[l] = 0x80;
    var dv = new DataView(padded.buffer);
    // 长度 64-bit big-endian; JS 里 bitLen < 2^32, 高 32 位为 0
    dv.setUint32(padded.length - 8, 0, false);
    dv.setUint32(padded.length - 4, bitLen >>> 0, false);
    // 处理 512-bit 块
    var w = new Int32Array(64);
    for (var off = 0; off < padded.length; off += 64) {
      for (var i = 0; i < 16; i++) {
        w[i] = dv.getUint32(off + i * 4, false);
      }
      for (i = 16; i < 64; i++) {
        var s0 = rotr(w[i-15],7) ^ rotr(w[i-15],18) ^ (w[i-15]>>>3);
        var s1 = rotr(w[i-2],17) ^ rotr(w[i-2],19) ^ (w[i-2]>>>10);
        w[i] = (w[i-16] + s0 + w[i-7] + s1) | 0;
      }
      var a=H[0],b=H[1],c=H[2],d=H[3],e=H[4],f=H[5],g=H[6],h=H[7];
      for (i = 0; i < 64; i++) {
        var S1 = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25);
        var ch = (e & f) ^ (~e & g);
        var t1 = (h + S1 + ch + K[i] + w[i]) | 0;
        var S0 = rotr(a,2) ^ rotr(a,13) ^ rotr(a,22);
        var maj = (a & b) ^ (a & c) ^ (b & c);
        var t2 = (S0 + maj) | 0;
        h=g; g=f; f=e; e=(d+t1)|0; d=c; c=b; b=a; a=(t1+t2)|0;
      }
      H[0]=(H[0]+a)|0; H[1]=(H[1]+b)|0; H[2]=(H[2]+c)|0; H[3]=(H[3]+d)|0;
      H[4]=(H[4]+e)|0; H[5]=(H[5]+f)|0; H[6]=(H[6]+g)|0; H[7]=(H[7]+h)|0;
    }
    var out = "";
    for (i = 0; i < 8; i++) {
      var v = H[i] >>> 0;
      out += ("00000000" + v.toString(16)).slice(-8);
    }
    return out;
  }

  return hashBytes;
})();

function utf8Encode(str) {
  // 返回 Uint8Array
  var bytes = [];
  for (var i = 0; i < str.length; i++) {
    var c = str.codePointAt(i);
    if (c > 0xffff) i++; // 代理对
    if (c < 0x80) {
      bytes.push(c);
    } else if (c < 0x800) {
      bytes.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f));
    } else if (c < 0x10000) {
      bytes.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
    } else {
      bytes.push(0xf0 | (c >> 18), 0x80 | ((c >> 12) & 0x3f), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
    }
  }
  return new Uint8Array(bytes);
}

// ============================================================
// HMAC-SHA256
// ============================================================
function sha256(str) {
  return sha256Bytes(utf8Encode(str));
}

function hmacSha256Hex(keyStr, msgStr) {
  var keyBytes = utf8Encode(keyStr);
  var msgBytes = utf8Encode(msgStr);
  var blockSize = 64;
  var key = new Uint8Array(blockSize);
  if (keyBytes.length > blockSize) {
    // key 过长先 hash(32 字节)
    var hb = hexToBytes(sha256Bytes(keyBytes));
    key.set(hb);
  } else {
    key.set(keyBytes);
  }
  var ipad = new Uint8Array(blockSize);
  var opad = new Uint8Array(blockSize);
  for (var i = 0; i < blockSize; i++) {
    ipad[i] = key[i] ^ 0x36;
    opad[i] = key[i] ^ 0x5c;
  }
  var inner = new Uint8Array(blockSize + msgBytes.length);
  inner.set(ipad);
  inner.set(msgBytes, blockSize);
  var innerBytes = hexToBytes(sha256Bytes(inner));
  var outer = new Uint8Array(blockSize + 32);
  outer.set(opad);
  outer.set(innerBytes, blockSize);
  return sha256Bytes(outer);
}

function hexToBytes(hex) {
  var out = new Uint8Array(hex.length / 2);
  for (var i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(i*2,2),16);
  return out;
}

function bytesToStr(bytes) {
  var s = "";
  for (var i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
  return s;
}

// ============================================================
// JSON 深递归排序 + 紧凑序列化(ensure_ascii=false)
// ============================================================
function deepSort(obj) {
  if (Array.isArray(obj)) {
    return obj.map(deepSort);
  } else if (obj !== null && typeof obj === "object") {
    var keys = Object.keys(obj).sort();
    var out = {};
    for (var i = 0; i < keys.length; i++) {
      out[keys[i]] = deepSort(obj[keys[i]]);
    }
    return out;
  }
  return obj;
}

// 与 Dart jsonEncode(ensure_ascii=false) 对齐的紧凑序列化
function compactJson(obj) {
  if (obj === null) return "null";
  if (typeof obj === "boolean") return obj ? "true" : "false";
  if (typeof obj === "number") {
    if (Number.isFinite(obj)) {
      // 整数直接输出, 浮点用 JS 默认(与 Dart double 一致, IEEE754)
      return obj.toString();
    }
    return "null";
  }
  if (typeof obj === "string") return JSON.stringify(obj); // 保留中文原样
  if (Array.isArray(obj)) {
    var parts = [];
    for (var i = 0; i < obj.length; i++) parts.push(compactJson(obj[i]));
    return "[" + parts.join(",") + "]";
  }
  // object
  var keys = Object.keys(obj).sort();
  var kv = [];
  for (i = 0; i < keys.length; i++) {
    kv.push(JSON.stringify(keys[i]) + ":" + compactJson(obj[keys[i]]));
  }
  return "{" + kv.join(",") + "}";
}

function signPayload(objWithoutSignature) {
  var payload = compactJson(deepSort(objWithoutSignature));
  return hmacSha256Hex(HMAC_KEY, payload);
}

// ============================================================
// 业务逻辑
// ============================================================
function nowUnixSeconds() {
  return Math.floor(Date.now() / 1000);
}

function parseBody(bodyStr) {
  try { return JSON.parse(bodyStr); } catch (e) { return null; }
}

function addSignatureAndTimestamp(obj) {
  var copy = JSON.parse(JSON.stringify(obj));
  if (copy.signature) delete copy.signature;
  copy.timestamp = nowUnixSeconds();
  copy.signature = signPayload(copy);
  return copy;
}

// 根据 chip_id + 激活码(salt) 派生正确的 secret_key/address_key
// 固件校验: secret_key == hex(SHA256(chip_id + salt + chip_id))[0:16]
//           address_key == hex(SHA256(chip_id + salt + salt + chip_id))[48:64]
// 其中 salt = license_key = 激活码(12字节)
function deriveKeys(chipId, code) {
  if (!chipId || !code) {
    return { secret: "0123456789abcdef", address: "fedcba9876543210" };
  }
  // 固件 hex 表是小写, chip_id 必须转小写(APP 显示的大写是 toUpperCase 的结果)
  var c = chipId.toLowerCase();
  var secret = sha256(c + code + c).slice(0, 16);
  var address = sha256(c + code + code + c).slice(48, 64);
  return { secret: secret, address: address };
}

// 各端点响应改造, 返回 null 表示不改(透传)
function transform(path, url, bodyObj, reqBodyStr) {
  if (!bodyObj) return null;

  // 1. 设备注册(record/device): registered true
  if (path.indexOf("/ultra/api/v1/app/record/device") >= 0) {
    var d = bodyObj.data || {};
    d.registered = true;
    bodyObj.data = d;
    bodyObj.success = true;
    if (bodyObj.code !== undefined) bodyObj.code = 200;
    if (bodyObj.message === undefined) bodyObj.message = "设备记录成功";
    return addSignatureAndTimestamp(bodyObj);
  }

  // 2. 订阅授权(device-authorization): 永久
  if (path.indexOf("/geofence/api/subscription/device-authorization") >= 0) {
    var a = bodyObj.data || {};
    a.expires_at = "2099-12-31T23:59:59+08:00";
    a.expiring_soon = false;
    bodyObj.data = a;
    bodyObj.success = true;
    return addSignatureAndTimestamp(bodyObj);
  }

  // 3. 激活码校验(device/register): 伪造成功 + 按 chip_id+激活码 派生 secret/address key
  if (path.indexOf("/ultra/api/v1/device/register") >= 0) {
    var chip = "";
    var code = "";
    try {
      var req = JSON.parse(reqBodyStr || "{}");
      chip = req.chip_id || "";
      code = req.activation_code || "";
    } catch (e) {}
    var keys = deriveKeys(chip, code);
    var fake = {
      code: 200,
      message: "激活成功",
      secret_key: keys.secret,
      address_key: keys.address
    };
    return addSignatureAndTimestamp(fake);
  }

  // 4. 订阅列表(my-subscriptions): 保持 data 数组不变(空数组合法)
  if (path.indexOf("/geofence/api/subscriber/my-subscriptions") >= 0) {
    bodyObj.success = true;
    return addSignatureAndTimestamp(bodyObj);
  }

  // 5. 其它(notice/map/firmware): 透传
  return null;
}

// 计算 device/register 的伪造响应(激活成功 + 派生key)
function fakeActivation(reqBodyStr) {
  var chip = "";
  var code = "";
  try {
    var req = JSON.parse(reqBodyStr || "{}");
    chip = req.chip_id || "";
    code = req.activation_code || "";
  } catch (e) {}
  var keys = deriveKeys(chip, code);
  var fake = { code: 200, message: "激活成功", secret_key: keys.secret, address_key: keys.address };
  return addSignatureAndTimestamp(fake);
}

// ============================================================
// Loon/Egern 入口
// ============================================================
var handler = function () {
  var url = ($request && $request.url) ? $request.url : "";
  var reqBodyStr = ($request && $request.body) ? $request.body : "";
  var path = url.replace(/^https?:\/\/[^\/]+/i, "");

  var isReq = (typeof $response === "undefined" || !$response);

  // http-request 类型($response 不存在): 处理 device/register, 读请求 body 伪造激活响应
  if (typeof $response === "undefined" || !$response) {
    if (path.indexOf("/ultra/api/v1/device/register") >= 0) {
      var fake = fakeActivation(reqBodyStr);
      $done({
        response: {
          status: 200,
          headers: { "Content-Type": "application/json" },
          body: compactJson(fake)
        }
      });
      return;
    }
    $done({});
    return;
  }

  // http-response 类型: 处理 record/device、device-authorization、my-subscriptions 等
  var bodyStr = $response.body;
  if (!bodyStr) {
    $done({});
    return;
  }
  var obj = parseBody(bodyStr);
  if (!obj) {
    $done({});
    return;
  }
  var result = transform(path, url, obj, reqBodyStr);
  if (result) {
    $done({ body: compactJson(result) });
  } else {
    $done({});
  }
};

// 代理环境(Loon/Egern)下 $done/$request 可用; Node 测试环境走 module.exports
if (typeof $done === "function" && typeof $request !== "undefined") {
  handler();
} else {
  module.exports = { transform: transform, signPayload: signPayload, compactJson: compactJson, deepSort: deepSort, hmacSha256Hex: hmacSha256Hex, sha256: sha256 };
}
