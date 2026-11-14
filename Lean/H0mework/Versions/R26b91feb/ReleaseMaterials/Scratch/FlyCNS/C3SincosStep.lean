import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ActuationStep

/-! Pure word/IEEE reification of the captured C7 host's shared libm
binary64 sin/cos operator: the actual range reduction and polynomial, not
an ideal sine oracle or a table of argument→answer values. -/

set_option autoImplicit false
namespace FlyCNS.C3Sincos
open FlyCNS.C3Actuation

structure Material where
  small : Float
  large : Float
  medium : Array Float
  sineCoefficients : Array Float
  cosineCoefficients : Array Float
  piWord : UInt64
  reciprocalWords : Array UInt64

def signBit : UInt64 := 0x8000000000000000
def high (a b : UInt64) : UInt64 := UInt64.ofNat ((a.toNat*b.toNat) / 2^64)
def shiftLeft (a b : UInt64) : UInt64 := a <<< (b &&& 63)
def shiftRight (a b : UInt64) : UInt64 := a >>> (b &&& 63)

def leading (a : UInt64) : UInt64 := Id.run do
  let mut count := 0
  for k in [:64] do
    if ((a >>> UInt64.ofNat (63-k)) &&& 1) == 1 then break
    count := count+1
  return UInt64.ofNat count

def wordSubtract (a : Float) (b : UInt64) : Float := Float.ofBits (a.toBits-b)

def polynomial (coefficients : Array Float) (square : Float) : Float := Id.run do
  let mut p := coefficients[0]!
  for i in [1:coefficients.size] do p := fused square p coefficients[i]!
  return p

def sinePolynomial (m : Material) (head tail : Float) (sign : UInt64) : Float :=
  let x := head+tail
  let square := x*x
  let correction := square*polynomial m.sineCoefficients square
  Float.ofBits ((fused x correction tail + head).toBits ^^^ sign)

def cosinePolynomial (m : Material) (square : Float) (sign : UInt64) : Float :=
  let p := polynomial m.cosineCoefficients square
  Float.ofBits ((fused square p (Float.ofBits 0x3FF0000000000000)).toBits+sign)

def cosineReduced (m : Material) (head tail : Float) (sign : UInt64) : Float :=
  let product := head*tail
  cosinePolynomial m (fused head head (product+product)) sign

def medium (m : Material) (cosine : Bool) (argument : Float) : Float :=
  let x := if cosine then argument.abs else argument
  let scaled := x*m.medium[0]!
  let nearest := FlyCNS.C3Integer.nearestEvenBits scaled.toBits
  let n := nearest.toUInt64
  let rounded := FlyCNS.C3Integer.floatOfI nearest
  let a := rounded*m.medium[1]!
  let b := rounded*m.medium[2]!
  let c := rounded*m.medium[3]!
  let remainder := x-a
  let head := remainder-b
  let tail := ((remainder-head)-b)-c
  let sign := if cosine then ((n ^^^ (n >>> 1)) <<< 63) else ((n <<< 62) &&& signBit)
  let useCosine := if cosine then (n &&& 1) == 0 else (n &&& 1) != 0
  if useCosine then cosineReduced m head tail sign else sinePolynomial m head tail sign

structure Reduction where
  mantissa : UInt64
  normalization : UInt64
  sign : UInt64
  cosine : Bool

def payneHanek (m : Material) (cosine : Bool) (argument : Float) : Reduction :=
  let bits := argument.toBits
  let exponent := ((bits &&& 0x7FFFFFFFFFFFFFFF) >>> 52)-1023
  let mantissa := signBit ||| (bits <<< 11)
  let base := 16-(exponent >>> 6).toNat
  let remainder := exponent &&& 63
  let p := m.reciprocalWords
  let a := if remainder == 0 then p[base+1]! else
    shiftLeft p[base+1]! remainder ||| shiftRight p[base]! (64-remainder)
  let b := if remainder == 0 then p[base+2]! else
    shiftLeft p[base+2]! remainder ||| shiftRight p[base+1]! (64-remainder)
  let c := if remainder == 0 then p[base+3]! else
    shiftLeft p[base+3]! remainder ||| shiftRight p[base+2]! (64-remainder)
  let first := high a mantissa
  let addend := b*mantissa
  let low := first+addend
  let carry : UInt64 := if low < first then 1 else 0
  let upper := high b mantissa + c*mantissa + carry
  let sign := if cosine then (upper ^^^ (upper <<< 1)) &&& signBit else (bits ^^^ upper) &&& signBit
  let zone := ((upper <<< 2) ^^^ (upper <<< 1)) &&& signBit != 0
  let complement := if (upper <<< 2) &&& signBit != 0 then 0xFFFFFFFFFFFFFFFF else 0
  let highFraction := (upper ^^^ complement) &&& 0x1FFFFFFFFFFFFFFF
  let lowFraction := low ^^^ complement
  let normalization := leading highFraction
  let normalized := shiftLeft highFraction normalization ||| shiftRight lowFraction (64-normalization)
  ⟨normalized,normalization,sign,if cosine then !zone else zone⟩

def large (m : Material) (cosine : Bool) (argument : Float) : Float :=
  let r := payneHanek m cosine argument
  let value := high m.piWord r.mantissa
  if r.cosine then
    let squared := high value value
    let square := wordSubtract (squared.toFloat*(Float.ofBits 0x3C50000000000000)) ((r.normalization+r.normalization) <<< 52)
    cosinePolynomial m square r.sign
  else
    let adjust := r.normalization <<< 52
    let x := wordSubtract (value.toFloat*(Float.ofBits 0x3C20000000000000)) adjust
    let head := wordSubtract ((value &&& 0xFFFF000000000000).toFloat*(Float.ofBits 0x3C20000000000000)) adjust
    let tail := wordSubtract ((value &&& 0x0000FFFFFFFFFFFF).toFloat*(Float.ofBits 0x3C20000000000000)) adjust
    let square := x*x
    let correction := square*polynomial m.sineCoefficients square
    Float.ofBits ((fused x correction tail+head).toBits ^^^ r.sign)

def evaluate (m : Material) (cosine : Bool) (argument : Float) : Float :=
  let bits := argument.toBits
  let absolute := argument.abs
  if (bits &&& 0x7FFFFFFFFFFFFFFF) == 0 then
    if cosine then Float.ofBits 0x3FF0000000000000 else argument
  else if ((bits >>> 52) &&& 2047) == 2047 then
    if (bits &&& 0xFFFFFFFFFFFFF) == 0 then Float.ofBits 0x7FF8000000000000
    else Float.ofBits ((if cosine then bits &&& 0x7FFFFFFFFFFFFFFF else bits) ||| 0x8000000000000)
  else if absolute <= m.small then
    if cosine then cosineReduced m absolute zero 0 else sinePolynomial m zero argument 0
  else if absolute < m.large then medium m cosine argument
  else large m cosine argument

end FlyCNS.C3Sincos
