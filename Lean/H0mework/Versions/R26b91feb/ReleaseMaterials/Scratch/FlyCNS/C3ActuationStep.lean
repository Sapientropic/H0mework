import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3IntegerStep

/-! C7's actual 50 stateless fixed-gain actuator primitive. The physical
position/velocity/transmission stage produces the present frame internally;
the pure force computation receives no force, acceleration or physics-after.
The installed arm64 library uses a fused sparse multiply/add. -/

set_option autoImplicit false

namespace FlyCNS.C3Actuation
open Float.Model

def finiteDyadic (x : Float) : Option (Int × Int × Bool) :=
  match x.toModel.unpack with
  | .finite sign mantissa exponent _ =>
      some (if sign == .negative then -(mantissa : Int) else (mantissa : Int), exponent, sign == .negative)
  | .zero sign => some (0,0,sign == .negative)
  | _ => none

/-- Concrete IEEE single rounding; it is not an opaque native FMA. -/
def fused (a b c : Float) : Float :=
  match finiteDyadic a, finiteDyadic b, finiteDyadic c with
  | some (ma,ea,sa),some (mb,eb,sb),some (mc,ec,sc) =>
      let ep := ea+eb
      let exponent := min ep ec
      let mantissa := ma*mb*Int.ofNat (2^(ep-exponent).toNat) + mc*Int.ofNat (2^(ec-exponent).toNat)
      if mantissa == 0 && (ma == 0 || mb == 0) && mc == 0 && sa != sb && sc then
        Float.ofBits 0x8000000000000000
      else Float.ofModel (Float.Model.pack (UnpackedFloat.normalize Format.binary64 mantissa exponent .positive))
  | _,_,_ =>
      if a.toModel.isNaN || b.toModel.isNaN || c.toModel.isNaN then Float.ofBits 0x7FF8000000000000
      else if a.toModel.isInf || b.toModel.isInf then a*b+c
      else c

structure Material where
  gain : Array Float
  bias0 : Array Float
  bias1 : Array Float
  bias2 : Array Float
  affineBias : Array Bool
  ctrlLimited : Array Bool
  ctrlLow : Array Float
  ctrlHigh : Array Float
  forceLimited : Array Bool
  forceLow : Array Float
  forceHigh : Array Float
  dofs : Nat

structure Frame where
  control : Array Float
  length : Array Float
  velocity : Array Float
  rowStart : Array Nat
  rowCount : Array Nat
  columns : Array Nat
  moment : Array Float

structure Result where
  actuatorForce : Array Float
  generalizedForce : Array Float
  badControl : Bool

def zero : Float := Float.ofBits 0
def clip (value low high : Float) : Float := if value < low then low else if value > high then high else value
def bad (value : Float) : Bool :=
  let bits := value.toBits
  (((bits >>> 52) &&& 2047) == 2047 && (bits &&& 0xFFFFFFFFFFFFF) != 0) ||
    value > (UInt64.ofNat 10000000000).toFloat || value < -(UInt64.ofNat 10000000000).toFloat

def forces (m : Material) (frame : Frame) : Result := Id.run do
  let actuators := m.gain.size
  let mut control := frame.control
  for actuator in [:actuators] do
    if m.ctrlLimited[actuator]! then
      control := control.set! actuator (clip control[actuator]! m.ctrlLow[actuator]! m.ctrlHigh[actuator]!)
  let invalid := control.any bad
  if invalid then control := Array.replicate actuators zero
  let mut force := Array.replicate actuators zero
  for actuator in [:actuators] do
    let bias := if m.affineBias[actuator]! then
      fused m.bias2[actuator]! frame.velocity[actuator]!
        (fused m.bias1[actuator]! frame.length[actuator]! m.bias0[actuator]!)
      else zero
    let value := m.gain[actuator]!*control[actuator]! + bias
    force := force.set! actuator (if m.forceLimited[actuator]! then
      clip value m.forceLow[actuator]! m.forceHigh[actuator]! else value)
  let mut generalized := Array.replicate m.dofs zero
  for actuator in [:actuators] do
    let value := force[actuator]!
    if value.toModel.unpack.beq zero.toModel.unpack == false then
      for k in [frame.rowStart[actuator]!:frame.rowStart[actuator]!+frame.rowCount[actuator]!] do
        let dof := frame.columns[k]!
        generalized := generalized.set! dof (fused frame.moment[k]! value generalized[dof]!)
  return ⟨force,generalized,invalid⟩

end FlyCNS.C3Actuation
