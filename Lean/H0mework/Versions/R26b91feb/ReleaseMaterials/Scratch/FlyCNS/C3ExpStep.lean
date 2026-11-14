import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ActuationStep
set_option autoImplicit false
namespace FlyCNS.C3Exp
open FlyCNS.C3Actuation
structure Material where
  positiveBound : UInt64
  negativeBound : UInt64
  subnormalScale : Float
  overflowScale : Float
  coefficients : Array Float
  table : Array Float

/-- Original actual libm polynomial/table/range scaling. Static table is
instruction data, not an argument/result cache or a future transition table. -/
def evaluate (m : Material) (x : Float) : Float :=
  let bits := x.toBits
  if ((bits >>> 52) &&& 2047) == 2047 && (bits &&& 0xFFFFFFFFFFFFF) != 0 then
    Float.ofBits (bits ||| 0x8000000000000)
  else if bits >= m.positiveBound && bits.toInt64 >= m.negativeBound.toInt64 then
    if x >= zero then x*m.overflowScale
    else
      let word := if bits+0x10000000000000 < bits then (0 : UInt64) else 0x10000000000000
      let tiny := Float.ofBits word
      tiny*tiny
  else
    let c := m.coefficients
    let scaled := x*c[0]!
    let nearest := FlyCNS.C3Integer.nearestEvenBits scaled.toBits
    let n := if FlyCNS.C3Integer.floatOfI nearest > scaled then nearest-1 else nearest
    let nf := FlyCNS.C3Integer.floatOfI n
    let fraction := scaled-nf
    let multiplicationError := fused (-x) c[0]! scaled
    let correction := fused x c[1]! (-multiplicationError)
    let index := (n.toUInt64 &&& 127).toNat
    let base := m.table[2*index]!
    let low := m.table[2*index+1]!+correction
    let reduced := fraction+low
    let a := fraction+c[2]!
    let b := fraction+c[3]!
    let p := fused reduced a c[4]!
    let q := fused reduced b c[5]!
    let value := ((reduced*c[6]!)*p)*q
    let exponent := FlyCNS.C3Integer.floorDiv n 128
    if exponent+1022 >= 0 then
      Float.ofBits ((fused value base base).toBits + (exponent.toUInt64 <<< 52))
    else
      let tiny := Float.ofBits (base.toBits+((exponent+1022).toUInt64 <<< 52))
      let one := Float.ofBits 0x3FF0000000000000
      let head := tiny+one
      let tail := tiny-(head-one)
      let tail := fused tiny value tail
      ((head+tail)-one)*m.subnormalScale
end FlyCNS.C3Exp
