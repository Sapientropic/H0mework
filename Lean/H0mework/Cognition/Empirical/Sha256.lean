import Init.Data.BitVec.Basic
import Init.Data.String.Basic

/-!
# Portable SHA-256 for compile-time empirical manifest binding

This small pure implementation avoids host commands and turns an included
manifest's exact UTF-8 bytes into the same lowercase digest used by the
runtime producer and independent consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Closure
namespace Empirical
namespace Manifest
namespace Sha256

abbrev Word := BitVec 32

private def word (value : Nat) : Word := BitVec.ofNat 32 value

private def constants : Array Word := #[
  word 0x428a2f98, word 0x71374491, word 0xb5c0fbcf, word 0xe9b5dba5,
  word 0x3956c25b, word 0x59f111f1, word 0x923f82a4, word 0xab1c5ed5,
  word 0xd807aa98, word 0x12835b01, word 0x243185be, word 0x550c7dc3,
  word 0x72be5d74, word 0x80deb1fe, word 0x9bdc06a7, word 0xc19bf174,
  word 0xe49b69c1, word 0xefbe4786, word 0x0fc19dc6, word 0x240ca1cc,
  word 0x2de92c6f, word 0x4a7484aa, word 0x5cb0a9dc, word 0x76f988da,
  word 0x983e5152, word 0xa831c66d, word 0xb00327c8, word 0xbf597fc7,
  word 0xc6e00bf3, word 0xd5a79147, word 0x06ca6351, word 0x14292967,
  word 0x27b70a85, word 0x2e1b2138, word 0x4d2c6dfc, word 0x53380d13,
  word 0x650a7354, word 0x766a0abb, word 0x81c2c92e, word 0x92722c85,
  word 0xa2bfe8a1, word 0xa81a664b, word 0xc24b8b70, word 0xc76c51a3,
  word 0xd192e819, word 0xd6990624, word 0xf40e3585, word 0x106aa070,
  word 0x19a4c116, word 0x1e376c08, word 0x2748774c, word 0x34b0bcb5,
  word 0x391c0cb3, word 0x4ed8aa4a, word 0x5b9cca4f, word 0x682e6ff3,
  word 0x748f82ee, word 0x78a5636f, word 0x84c87814, word 0x8cc70208,
  word 0x90befffa, word 0xa4506ceb, word 0xbef9a3f7, word 0xc67178f2]

private def initialState : Array Word := #[
  word 0x6a09e667, word 0xbb67ae85, word 0x3c6ef372, word 0xa54ff53a,
  word 0x510e527f, word 0x9b05688c, word 0x1f83d9ab, word 0x5be0cd19]

private def choose (x y z : Word) : Word :=
  (x &&& y) ^^^ ((~~~x) &&& z)

private def majority (x y z : Word) : Word :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def upperSigma0 (x : Word) : Word :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

private def upperSigma1 (x : Word) : Word :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

private def lowerSigma0 (x : Word) : Word :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

private def lowerSigma1 (x : Word) : Word :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

private def wordFromBytes (bytes : Array UInt8) (offset : Nat) : Word :=
  word <| (bytes[offset]!.toNat <<< 24) |||
    (bytes[offset + 1]!.toNat <<< 16) |||
    (bytes[offset + 2]!.toNat <<< 8) |||
    bytes[offset + 3]!.toNat

private def schedule (bytes : Array UInt8) (offset : Nat) : Array Word := Id.run do
  let mut result := Array.replicate 64 (word 0)
  for index in [:16] do
    result := result.set! index (wordFromBytes bytes (offset + 4 * index))
  for index in [16:64] do
    result := result.set! index
      (lowerSigma1 result[index - 2]! + result[index - 7]! +
        lowerSigma0 result[index - 15]! + result[index - 16]!)
  return result

private def compress (state : Array Word) (bytes : Array UInt8)
    (offset : Nat) : Array Word := Id.run do
  let words := schedule bytes offset
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for index in [:64] do
    let first := h + upperSigma1 e + choose e f g + constants[index]! +
      words[index]!
    let second := upperSigma0 a + majority a b c
    h := g
    g := f
    f := e
    e := d + first
    d := c
    c := b
    b := a
    a := first + second
  return #[
    state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

private def paddedBytes (input : ByteArray) : Array UInt8 :=
  let bytes := input.data.push 0x80
  let zeroCount := (56 + 64 - bytes.size % 64) % 64
  let bitLength := input.size * 8
  bytes ++ Array.replicate zeroCount (0 : UInt8) ++ #[
    (bitLength >>> 56).toUInt8, (bitLength >>> 48).toUInt8,
    (bitLength >>> 40).toUInt8, (bitLength >>> 32).toUInt8,
    (bitLength >>> 24).toUInt8, (bitLength >>> 16).toUInt8,
    (bitLength >>> 8).toUInt8, bitLength.toUInt8]

def digestWords (text : String) : Array Word := Id.run do
  let bytes := paddedBytes text.toUTF8
  let mut state := initialState
  for block in [:bytes.size / 64] do
    state := compress state bytes (block * 64)
  return state

def hex (text : String) : String :=
  (digestWords text).foldl (fun output value => output ++ value.toHex) ""

end Sha256
end Manifest
end Empirical
end Closure
end Consciousness
end NoIslandNoMagic
end SaturationMonoid
