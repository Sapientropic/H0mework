import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ActuationStep
set_option autoImplicit false
namespace FlyCNS.C3Pow
open FlyCNS.C3Actuation
structure Material where
  exponentOffset : UInt64
  subnormalOffset : UInt64
  headMask : UInt64
  tableMask : UInt64
  multiplier : Float
  overflowScale : Float
  underflowScale : Float
  upperBound : Float
  lowerBound : Float
  logarithm : Array Float
  logarithmTable : Array UInt64
  exponential : Array Float
  exponentialTable : Array Float

def one : Float := Float.ofBits 0x3ff0000000000000
def two : Float := Float.ofBits 0x4000000000000000
def three : Float := Float.ofBits 0x4008000000000000

def floorFloat (x : Float) : FlyCNS.C3Integer.I :=
  let n := FlyCNS.C3Integer.nearestEvenBits x.toBits
  if FlyCNS.C3Integer.floatOfI n > x then n-1 else n

/-- Original positive unit-interval pow(x,3) instruction path. The tables are
source instruction constants. Neither an argument cache nor power output is input. -/
def cubic (m : Material) (x : Float) : Float := Id.run do
  if x == zero || x == one then return x
  let mut bits := x.toBits
  if bits < 0x10000000000000 then
    bits := ((Float.ofBits (bits ||| 0x3ff0000000000000))-one).toBits+m.subnormalOffset
  let fraction := bits &&& 0xfffffffffffff
  let mut high := zero
  let mut low := zero
  if fraction == 0 then
    let signed := (bits-0x3ff0000000000000).toInt64
    let value := FlyCNS.C3Integer.floatOfI signed / (Float.ofBits 0x42c0000000000000)
    high := value*three
    low := fused value three (-high)
  else
    let index := (((fraction+0x100000000000) &&& 0x1fe00000000000) >>> 41).toNat/16
    let exponent := FlyCNS.C3Integer.floorDiv (bits+m.exponentOffset).toInt64 4503599627370496
    let tableBits := m.logarithmTable[2*index]!
    let reciprocal := Float.ofBits ((tableBits &&& 0xffffffff) <<< 32)
    let mantissaBits := fraction ||| 0x3ff0000000000000
    let full := Float.ofBits mantissaBits
    let product := reciprocal*full
    let truncated := Float.ofBits (mantissaBits &&& 0xffffffffffe00000)
    let tail := full-truncated
    let error := fused reciprocal truncated (-product)
    let reduced := product-one
    let remainder := fused reciprocal tail error
    let c := m.logarithm
    let mut polynomial := fused reduced c[0]! c[1]!
    polynomial := fused reduced polynomial c[2]!
    polynomial := fused reduced polynomial c[3]!
    polynomial := fused reduced polynomial c[4]!
    let square := reduced*reduced
    polynomial := (square*square)*polynomial
    let a := fused c[5]! reduced c[7]!
    let b := fused c[6]! reduced c[8]!
    let e := fused c[5]! reduced (-(a-c[7]!))
    let b := fused c[5]! remainder b
    let b := e+b
    let head := fused a reduced c[9]!
    let tail := fused b reduced c[10]!
    let e := fused a reduced (-(head-c[9]!))
    let tail := fused a remainder tail
    let tail := e+tail
    let a := head*reduced
    let b := tail*reduced
    let e := fused head reduced (-a)
    let b := fused head remainder b
    let finalTail := e+b
    let exponentFloat := FlyCNS.C3Integer.floatOfI exponent
    let tableHead := Float.ofBits m.logarithmTable[2*index+1]!
    let head := ((exponentFloat+tableHead)+a)+polynomial
    let head := Float.ofBits (head.toBits &&& m.headMask)
    let tail := (((exponentFloat-head)+tableHead)+a)+polynomial
    let tableTail := Float.ofBits (tableBits &&& m.tableMask)
    let tail := (tableTail+tail)+finalTail
    let scale := three*m.multiplier
    high := scale*head
    low := fused scale head (-high)
    low := fused scale tail low
  if high < m.lowerBound then return m.underflowScale*m.underflowScale
  if high > m.upperBound then return m.overflowScale*m.overflowScale
  let n := floorFloat high
  let fraction := high-FlyCNS.C3Integer.floatOfI n
  let index := (n.toUInt64 &&& 127).toNat
  let base := m.exponentialTable[2*index]!
  let correction := low-m.exponentialTable[2*index+1]!
  let reduced := correction+fraction
  let c := m.exponential
  let mut polynomial := fused fraction c[0]! c[1]!
  polynomial := fused fraction polynomial c[2]!
  polynomial := fused reduced polynomial c[3]!
  polynomial := fused reduced polynomial c[4]!
  polynomial := reduced*polynomial
  let highBits := (n.toUInt64 <<< 44) &&& 0xfff0000000000000
  let lowBits := ((n.toUInt64 <<< 45) &&& 0xfff0000000000000)-highBits
  let value := Float.ofBits (highBits+base.toBits)
  let value := fused value polynomial value
  return value*(Float.ofBits (lowBits+0x3ff0000000000000))
end FlyCNS.C3Pow
