module

public import Wychelean.StreamCiphers.ChaCha.Basic
public import RunTests.Basic
public import RunTests.Parser.Hex

/-!
# ChaCha20 RFC 8439 known-answer tests

The ChaCha test vectors of <https://www.rfc-editor.org/rfc/rfc8439.html>: §2.1.1 (quarter round),
§2.2.1 (quarter round on the state), §2.3.2 (block function), §2.4.2 (encryption), §2.6.2 and
Appendix A.4 (the first 32 bytes of block zero, used as the Poly1305 key), and Appendices A.1
(block function) and A.2 (encryption).
-/

namespace Wychelean.StreamCiphers.ChaCha.Tests
open RunTests RunTests.Parser

/-- A state as the RFC prints it, row by row. -/
private def stateList (s : State) : List UInt32 := s.toList

/-- The key `00:01:02:…:1f` of §2.3.2 and §2.4.2. -/
private def seqKey : ByteVec keyBytes :=
  hex! "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"

/-! ## §2.1–§2.3: quarter round and block function -/

private def quarterRoundTests : List Test :=
  let (a, b, c, d) := quarterRound 0x11111111 0x01020304 0x9b8d6f43 0x01234567
  [check "§2.1.1 quarter round" [0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb] [a, b, c, d],
   check "§2.2.1 QUARTERROUND(2, 7, 8, 13)"
     [0x879531e0, 0xc5ecf37d, 0xbdb886dc, 0xc9a62f8a,
      0x44c20ef3, 0x3390af7f, 0xd9fc690b, 0xcfacafd2,
      0xe46bea80, 0xb00a5631, 0x974c541a, 0x359e9963,
      0x5c971061, 0xccc07c79, 0x2098d9d6, 0x91dbd320]
     (stateList <| qround 2 7 8 13 #v[
      0x879531e0, 0xc5ecf37d, 0x516461b1, 0xc9a62f8a,
      0x44c20ef3, 0x3390af7f, 0xd9fc690b, 0x2a5f714c,
      0x53372767, 0xb00a5631, 0x974c541a, 0x359e9963,
      0x5c971061, 0x3d631689, 0x2098d9d6, 0x91dbd320])]

private def blockFunctionTests : List Test :=
  let nonce := hex! "000000090000004a00000000"
  let s := initState seqKey 1 nonce
  [check "§2.3.2 state with the key setup"
     [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
      0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
      0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c,
      0x00000001, 0x09000000, 0x4a000000, 0x00000000] (stateList s),
   check "§2.3.2 state after 20 rounds"
     [0x837778ab, 0xe238d763, 0xa67ae21e, 0x5950bb2f,
      0xc4f2d0c7, 0xfc62bb2f, 0x8fa018fc, 0x3f5ec7b7,
      0x335271c2, 0xf29489f3, 0xeabda8fc, 0x82e46ebd,
      0xd19c12b4, 0xb04e16de, 0x9e83d0cb, 0x4e3c50a2] (stateList (rounds 20 s)),
   check "§2.3.2 state at the end of the ChaCha20 operation"
     [0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3,
      0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3,
      0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9,
      0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2] (stateList (block 20 s)),
   check "§2.3.2 serialized block"
     (hex! "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e\
       d2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e")
     (chacha20Block seqKey 1 nonce),
   check "§2.3.1 ten inner_blocks are 20 rounds"
     (stateList (Nat.repeat doubleRound 10 s)) (stateList (rounds 20 s))]

/-! ## §2.6.2, A.1 and A.4: more block function vectors -/

/-- A block function vector: key, block counter, nonce, and the expected leading output bytes. -/
private structure BlockKat where
  name : String
  key : ByteVec keyBytes
  counter : UInt32
  nonce : ByteVec nonceBytes
  expected : Array UInt8

private def zeroKey : ByteVec keyBytes := Vector.replicate keyBytes 0
private def zeroNonce : ByteVec nonceBytes := Vector.replicate nonceBytes 0

private def blockVectors : List BlockKat := [
  ⟨"A.1 #1", zeroKey, 0, zeroNonce,
    (hex! "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7\
      da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586").toArray⟩,
  ⟨"A.1 #2", zeroKey, 1, zeroNonce,
    (hex! "9f07e7be5551387a98ba977c732d080dcb0f29a048e3656912c6533e32ee7aed\
      29b721769ce64e43d57133b074d839d531ed1f28510afb45ace10a1f4b794d6f").toArray⟩,
  ⟨"A.1 #3", hex! "0000000000000000000000000000000000000000000000000000000000000001", 1,
    zeroNonce,
    (hex! "3aeb5224ecf849929b9d828db1ced4dd832025e8018b8160b82284f3c949aa5a\
      8eca00bbb4a73bdad192b5c42f73f2fd4e273644c8b36125a64addeb006c13a0").toArray⟩,
  ⟨"A.1 #4", hex! "00ff000000000000000000000000000000000000000000000000000000000000", 2,
    zeroNonce,
    (hex! "72d54dfbf12ec44b362692df94137f328fea8da73990265ec1bbbea1ae9af0ca\
      13b25aa26cb4a648cb9b9d1be65b2c0924a66c54d545ec1b7374f4872e99f096").toArray⟩,
  ⟨"A.1 #5", zeroKey, 0, hex! "000000000000000000000002",
    (hex! "c2c64d378cd536374ae204b9ef933fcd1a8b2288b3dfa49672ab765b54ee27c7\
      8a970e0e955c14f3a88e741b97c286f75f8fc299e8148362fa198a39531bed6d").toArray⟩,
  ⟨"§2.6.2 Poly1305 key generation, first 32 bytes",
    hex! "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f", 0,
    hex! "000000000001020304050607",
    (hex! "8ad5a08b905f81cc815040274ab29471a833b637e3fd0da508dbb8e2fdd1a646").toArray⟩,
  ⟨"A.4 #1 Poly1305 key generation, first 32 bytes", zeroKey, 0, zeroNonce,
    (hex! "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7").toArray⟩,
  ⟨"A.4 #2 Poly1305 key generation, first 32 bytes",
    hex! "0000000000000000000000000000000000000000000000000000000000000001", 0,
    hex! "000000000000000000000002",
    (hex! "ecfa254f845f647473d3cb140da9e87606cb33066c447b87bc2666dde3fbb739").toArray⟩,
  ⟨"A.4 #3 Poly1305 key generation, first 32 bytes",
    hex! "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0", 0,
    hex! "000000000000000000000002",
    (hex! "965e3bc6f9ec7ed9560808f4d229f94b137ff275ca9b3fcbdd59deaad23310ae").toArray⟩ ]

private def blockKatTests : List Test :=
  blockVectors.map fun v =>
    check v.name (toHex v.expected.toVector)
      (toHex ((chacha20Block v.key v.counter v.nonce).toArray.extract 0 v.expected.size).toVector)

/-! ## §2.4.2 and A.2: encryption -/

/-- An encryption vector: the plaintext and ciphertext have the same length. -/
private structure EncKat where
  name : String
  key : ByteVec keyBytes
  counter : UInt32
  nonce : ByteVec nonceBytes
  /-- Hex, decoded when the suite runs: literals this long exceed `hex!`'s recursion limit. -/
  plaintext : String
  /-- Hex, as `plaintext`. -/
  ciphertext : String

private def encVectors : List EncKat := [
  ⟨"§2.4.2 sunscreen", seqKey, 1, hex! "000000000000004a00000000",
    "4c616469657320616e642047656e746c656d656e206f662074686520636c6173\
      73206f66202739393a204966204920636f756c64206f6666657220796f75206f\
      6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73\
      637265656e20776f756c642062652069742e",
    "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b\
      f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8\
      07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736\
      5af90bbf74a35be6b40b8eedf2785e42874d"⟩,
  ⟨"A.2 #1", zeroKey, 0, zeroNonce, "".pushn '0' 128,
    "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7\
      da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586"⟩,
  ⟨"A.2 #2", hex! "0000000000000000000000000000000000000000000000000000000000000001", 1,
    hex! "000000000000000000000002",
    "416e79207375626d697373696f6e20746f20746865204945544620696e74656e\
      6465642062792074686520436f6e7472696275746f7220666f72207075626c69\
      636174696f6e20617320616c6c206f722070617274206f6620616e2049455446\
      20496e7465726e65742d4472616674206f722052464320616e6420616e792073\
      746174656d656e74206d6164652077697468696e2074686520636f6e74657874\
      206f6620616e204945544620616374697669747920697320636f6e7369646572\
      656420616e20224945544620436f6e747269627574696f6e222e205375636820\
      73746174656d656e747320696e636c756465206f72616c2073746174656d656e\
      747320696e20494554462073657373696f6e732c2061732077656c6c20617320\
      7772697474656e20616e6420656c656374726f6e696320636f6d6d756e696361\
      74696f6e73206d61646520617420616e792074696d65206f7220706c6163652c\
      207768696368206172652061646472657373656420746f",
    "a3fbf07df3fa2fde4f376ca23e82737041605d9f4f4f57bd8cff2c1d4b7955ec\
      2a97948bd3722915c8f3d337f7d370050e9e96d647b7c39f56e031ca5eb6250d\
      4042e02785ececfa4b4bb5e8ead0440e20b6e8db09d881a7c6132f420e527950\
      42bdfa7773d8a9051447b3291ce1411c680465552aa6c405b7764d5e87bea85a\
      d00f8449ed8f72d0d662ab052691ca66424bc86d2df80ea41f43abf937d3259d\
      c4b2d0dfb48a6c9139ddd7f76966e928e635553ba76c5c879d7b35d49eb2e62b\
      0871cdac638939e25e8a1e0ef9d5280fa8ca328b351c3c765989cbcf3daa8b6c\
      cc3aaf9f3979c92b3720fc88dc95ed84a1be059c6499b9fda236e7e818b04b0b\
      c39c1e876b193bfe5569753f88128cc08aaa9b63d1a16f80ef2554d7189c411f\
      5869ca52c5b83fa36ff216b9c1d30062bebcfd2dc5bce0911934fda79a86f6e6\
      98ced759c3ff9b6477338f3da4f9cd8514ea9982ccafb341b2384dd902f3d1ab\
      7ac61dd29c6f21ba5b862f3730e37cfdc4fd806c22f221"⟩,
  ⟨"A.2 #3", hex! "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0", 42,
    hex! "000000000000000000000002",
    "2754776173206272696c6c69672c20616e642074686520736c6974687920746f\
      7665730a446964206779726520616e642067696d626c6520696e207468652077\
      6162653a0a416c6c206d696d737920776572652074686520626f726f676f7665\
      732c0a416e6420746865206d6f6d65207261746873206f757467726162652e",
    "62e6347f95ed87a45ffae7426f27a1df5fb69110044c0d73118effa95b01e5cf\
      166d3df2d721caf9b21e5fb14c616871fd84c54f9d65b283196c7fe4f60553eb\
      f39c6402c42234e32a356b3e764312a61a5532055716ead6962568f87d3f3f77\
      04c6a8d1bcd1bf4d50d6154b6da731b187b58dfd728afa36757a797ac188d1"⟩ ]

/-- `chacha20` on an array, for vectors whose length is only known at run time. -/
private def run (key : ByteVec keyBytes) (counter : UInt32) (nonce : ByteVec nonceBytes)
    (msg : Array UInt8) : IO (Array UInt8) := do
  if h : counter.toNat + numBlocks msg.size ≤ 2 ^ 32 then
    return (chacha20 key counter nonce msg.toVector h).toArray
  else throw (IO.userError s!"{msg.size} bytes from block {counter} would wrap the counter")

/-- Encrypt and decrypt one vector. -/
private def encTest (v : EncKat) : IO (List Test) := do
  let pt ← IO.ofExcept (parse readHex v.plaintext)
  let ct ← IO.ofExcept (parse readHex v.ciphertext)
  if pt.size != ct.size then
    throw (IO.userError s!"{v.name}: plaintext and ciphertext lengths differ")
  return [
    check s!"{v.name}, encrypt" (toHex ct.toVector)
      (toHex (← run v.key v.counter v.nonce pt).toVector),
    check s!"{v.name}, decrypt" (toHex pt.toVector)
      (toHex (← run v.key v.counter v.nonce ct).toVector)]

/-! ## Suites -/

public def rfc8439 : List Suite := [
  { name := "ChaCha RFC 8439 §2.1–§2.3 quarter round and block function",
    tests := pure (quarterRoundTests ++ blockFunctionTests) },
  { name := "ChaCha20 RFC 8439 §2.6.2, A.1, A.4 block function",
    tests := pure blockKatTests },
  { name := "ChaCha20 RFC 8439 §2.4.2, A.2 encryption",
    tests := List.flatMapM encTest encVectors } ]

end Wychelean.StreamCiphers.ChaCha.Tests
