// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
let sha256_round_constants : FixedArray[UInt] = [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
  0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
  0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
  0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
  0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
  0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
  0xc67178f2,
]

///|
fn sha256_initial_state() -> FixedArray[UInt] {
  [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19,
  ]
}

///|
fn rotate_right(value : UInt, count : Int) -> UInt {
  (value >> count) | (value << (32 - count))
}

///|
fn sha256_compress(state : FixedArray[UInt], block : BytesView) -> Unit {
  let words = FixedArray::make(64, 0U)
  for index in 0..<16 {
    let offset = index * 4
    words[index] = (block[offset].to_uint() << 24) |
      (block[offset + 1].to_uint() << 16) |
      (block[offset + 2].to_uint() << 8) |
      block[offset + 3].to_uint()
  }
  for index in 16..<64 {
    let previous_15 = words[index - 15]
    let sigma0 = rotate_right(previous_15, 7) ^
      rotate_right(previous_15, 18) ^
      (previous_15 >> 3)
    let previous_2 = words[index - 2]
    let sigma1 = rotate_right(previous_2, 17) ^
      rotate_right(previous_2, 19) ^
      (previous_2 >> 10)
    words[index] = words[index - 16] + sigma0 + words[index - 7] + sigma1
  }
  let mut a = state[0]
  let mut b = state[1]
  let mut c = state[2]
  let mut d = state[3]
  let mut e = state[4]
  let mut f = state[5]
  let mut g = state[6]
  let mut h = state[7]
  for index in 0..<64 {
    let sum1 = rotate_right(e, 6) ^ rotate_right(e, 11) ^ rotate_right(e, 25)
    let choose = (e & f) ^ (e.lnot() & g)
    let temporary1 = h +
      sum1 +
      choose +
      sha256_round_constants[index] +
      words[index]
    let sum0 = rotate_right(a, 2) ^ rotate_right(a, 13) ^ rotate_right(a, 22)
    let majority = (a & b) ^ (a & c) ^ (b & c)
    let temporary2 = sum0 + majority
    h = g
    g = f
    f = e
    e = d + temporary1
    d = c
    c = b
    b = a
    a = temporary1 + temporary2
  }
  state[0] = state[0] + a
  state[1] = state[1] + b
  state[2] = state[2] + c
  state[3] = state[3] + d
  state[4] = state[4] + e
  state[5] = state[5] + f
  state[6] = state[6] + g
  state[7] = state[7] + h
}

///|
/// Computes SHA-256 without target-specific intrinsics or external runtimes.
pub fn sha256(input : BytesView) -> Bytes {
  let state = sha256_initial_state()
  let complete_bytes = input.length() / 64 * 64
  for offset = 0; offset < complete_bytes; offset = offset + 64 {
    sha256_compress(state, input[offset:offset + 64])
  }
  let remaining = input.length() - complete_bytes
  let tail_length = if remaining < 56 { 64 } else { 128 }
  let tail = FixedArray::make(tail_length, b'\x00')
  for index in 0..<remaining {
    tail[index] = input[complete_bytes + index]
  }
  tail[remaining] = b'\x80'
  let bit_length = input.length().to_uint64() * 8UL
  let encoded_length = bit_length.to_be_bytes()
  for index in 0..<8 {
    tail[tail_length - 8 + index] = encoded_length[index]
  }
  let tail_bytes = Bytes::from_array(tail)
  sha256_compress(state, tail_bytes[0:64])
  if tail_length == 128 {
    sha256_compress(state, tail_bytes[64:128])
  }
  let digest = FixedArray::make(32, b'\x00')
  for index in 0..<8 {
    let word = state[index]
    let offset = index * 4
    digest[offset] = (word >> 24).to_byte()
    digest[offset + 1] = (word >> 16).to_byte()
    digest[offset + 2] = (word >> 8).to_byte()
    digest[offset + 3] = word.to_byte()
  }
  Bytes::from_array(digest)
}

///|
pub fn sha256_hex(input : BytesView) -> Bytes {
  bytes_to_lower_hex(sha256(input))
}
