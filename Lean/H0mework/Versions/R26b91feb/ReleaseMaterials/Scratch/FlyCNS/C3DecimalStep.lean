import Lean
set_option autoImplicit false
namespace FlyCNS.C3Decimal

structure Rational where
  numerator : Nat
  denominator : Nat

def dyadic (bits : UInt64) : Rational :=
  let exponent := ((bits >>> 52) &&& 2047).toNat
  let fraction := (bits &&& 0xFFFFFFFFFFFFF).toNat
  let mantissa := if exponent==0 then fraction else fraction+2^52
  let power : Int := if exponent==0 then -1074 else (exponent : Int)-1075
  if power≥0 then ⟨mantissa*2^power.toNat,1⟩ else ⟨mantissa,2^(-power).toNat⟩
def midpoint (a b : Rational) : Rational :=
  ⟨a.numerator*b.denominator+b.numerator*a.denominator,2*a.denominator*b.denominator⟩
def scaled (x : Rational) (power : Int) : Rational :=
  if power≥0 then ⟨x.numerator,x.denominator*10^power.toNat⟩
  else ⟨x.numerator*10^(-power).toNat,x.denominator⟩
def nearest (x : Rational) : Nat :=
  let q := x.numerator/x.denominator
  let r := x.numerator%x.denominator
  if 2*r>x.denominator || (2*r==x.denominator && q%2==1) then q+1 else q
def lowerInteger (x : Rational) (closed : Bool) : Nat :=
  let q := x.numerator/x.denominator
  if x.numerator%x.denominator==0 && closed then q else q+1
def upperInteger (x : Rational) (closed : Bool) : Nat :=
  let q := x.numerator/x.denominator
  if x.numerator%x.denominator==0 && !closed then q-1 else q
def decimalOrder (x : Rational) : Int :=
  let rough : Int := ((toString x.numerator).length : Int)-((toString x.denominator).length : Int)
  let value := scaled x rough
  if value.numerator<value.denominator then rough-1 else rough
def shortest (bits : UInt64) : Nat × Int := Id.run do
  let value := dyadic bits
  let low := midpoint (dyadic (bits-1)) value
  let high := midpoint value (dyadic (bits+1))
  let closed := bits &&& 1 == 0
  let order := decimalOrder value
  for digits in [1:18] do
    let power := order-(digits : Int)+1
    let lower := lowerInteger (scaled low power) closed
    let upper := upperInteger (scaled high power) closed
    if lower≤upper then
      let coefficient := min upper (max lower (nearest (scaled value power)))
      return (coefficient,power)
  let power := order-16
  return (nearest (scaled value power),power)
def zeros (n : Nat) : String := String.ofList (List.replicate n '0')
def format (coefficient : Nat) (power : Int) : String := Id.run do
  let mut n := coefficient
  let mut e := power
  for _ in [:17] do
    if n>0 && n%10==0 then
      n:=n/10
      e:=e+1
  let digits := toString n
  let point := (digits.length : Int)+e
  if point≤-4 || point>16 then
    let exponent := point-1
    let suffix := toString exponent.natAbs
    let fractional := if digits.length>1 then "."++String.ofList (digits.toList.drop 1) else ""
    return String.ofList (digits.toList.take 1)++fractional++"e"++
      (if exponent<0 then "-" else "+")++(if suffix.length<2 then "0" else "")++suffix
  else if point≤0 then
    return "0."++zeros (-point).toNat++digits
  else if point≥digits.length then
    return digits++zeros (point.toNat-digits.length)++".0"
  else return String.ofList (digits.toList.take point.toNat)++"."++String.ofList (digits.toList.drop point.toNat)

/-- CPython repr mode0 is the shortest RNE decimal. The operation uses only
original binary64 bits, exact dyadic midpoint intervals and integer division. -/
def encode (bits : UInt64) : String :=
  let negative := bits >>> 63 != 0
  let magnitude := bits &&& 0x7FFFFFFFFFFFFFFF
  if magnitude>0x7FF0000000000000 then "NaN"
  else if magnitude==0x7FF0000000000000 then if negative then "-Infinity" else "Infinity"
  else if magnitude==0 then if negative then "-0.0" else "0.0"
  else
    let (n,e) := shortest magnitude
    (if negative then "-" else "")++format n e

end FlyCNS.C3Decimal
