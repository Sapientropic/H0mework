import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SincosROM

/-! Actual __sincos_stret entry in the same captured source image.
Its small sine uses head=x, tail=0; scalar sin uses head=0, tail=x.
Those two FMA sequences are distinct binary64 operators. -/
set_option autoImplicit false
namespace FlyCNS.C3PairedSincos
open FlyCNS.C3Actuation FlyCNS.C3Sincos

def evaluate (x : Float) : Float × Float :=
  let bits := x.toBits
  if (bits &&& 0x7FFFFFFFFFFFFFFF) == 0 then (x,Float.ofBits 0x3FF0000000000000)
  else if ((bits >>> 52) &&& 2047) == 2047 then
    (FlyCNS.C3Sincos.evaluate original false x,FlyCNS.C3Sincos.evaluate original true x)
  else if x.abs <= original.small then
    (sinePolynomial original x zero 0,cosineReduced original x zero 0)
  else (FlyCNS.C3Sincos.evaluate original false x,FlyCNS.C3Sincos.evaluate original true x)

/-- Raw nonfinite words bypass Float's canonical NaN codec. -/
def evaluateBits (bits : UInt64) : UInt64 × UInt64 :=
  if ((bits >>> 52) &&& 2047) == 2047 then
    let result := if bits &&& 0xFFFFFFFFFFFFF == 0 then 0x7FF8000000000000 else bits ||| 0x8000000000000
    (result,result)
  else
    let (s,c) := evaluate (Float.ofBits bits)
    (s.toBits,c.toBits)
end FlyCNS.C3PairedSincos
