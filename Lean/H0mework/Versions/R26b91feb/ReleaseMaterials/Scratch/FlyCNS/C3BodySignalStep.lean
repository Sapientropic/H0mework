import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ExpROM
set_option autoImplicit false
namespace FlyCNS.C3BodySignal
open FlyCNS.C3Actuation

structure Material where
  populations : Array (Array Nat)
  timestep : Float
  motorTau : Float
  feedingTau : Float
  steeringTau : Float
  motorImpulse : Float
  feedingImpulse : Float
  dnaImpulse : Float
  dngImpulse : Float
  maximum : Float
  sharedDrive : Bool

structure State where
  motor : Array Float
  descending : Array Float
  feeding : Float
  steering : Array Float
  controllerEnabled : Bool
  feedingEnabled : Bool

structure Result where
  state : State
  signal : Array Float
  feeding : Float

def one : Float := Float.ofBits 0x3ff0000000000000
def two : Float := Float.ofBits 0x4000000000000000

def pulseFraction (nodes fired : Array Nat) (impulse : Float) : Float :=
  if nodes.isEmpty then zero else
    let count := nodes.foldl (fun n v => if fired.contains v then n+1 else n) 0
    (impulse*(UInt64.ofNat count).toFloat)/(UInt64.ofNat nodes.size).toFloat

/-- Neural spikes generate the actual decaying motor/descending/feeding/steering
traces and the next body inputs. No drive, desired turn or output is supplied. -/
def receive (m : Material) (s : State) (fired : Array Nat) : Result := Id.run do
  let decay := FlyCNS.C3Exp.exponential (-m.timestep/m.motorTau)
  let motor := s.motor.mapIdx fun i v => v*decay+pulseFraction m.populations[i]! fired m.motorImpulse
  let descending := s.descending.mapIdx fun i v => v*decay+pulseFraction m.populations[i+2]! fired m.motorImpulse
  let feeding := s.feeding*(FlyCNS.C3Exp.exponential (-m.timestep/m.feedingTau))+
    pulseFraction m.populations[4]! fired m.feedingImpulse
  let sd := FlyCNS.C3Exp.exponential (-m.timestep/m.steeringTau)
  let steering := s.steering.mapIdx fun i v => v*sd+pulseFraction m.populations[i+5]! fired (if i < 2 then m.dnaImpulse else m.dngImpulse)
  let state := {s with motor,descending,feeding,steering}
  let feedingOutput := if s.feedingEnabled then min feeding one else zero
  if !s.controllerEnabled then return ⟨state,#[zero,zero],feedingOutput⟩
  let mut signal := motor.mapIdx fun i v => min (v+descending[i]!) m.maximum
  if m.sharedDrive then
    let mean := (signal[0]!+signal[1]!)/two
    signal := #[mean,mean]
  signal := signal.mapIdx fun i v =>
    min m.maximum (max zero (v*(FlyCNS.C3Exp.exponential (-steering[i]!))+steering[3-i]!))
  return ⟨state,signal,feedingOutput⟩
end FlyCNS.C3BodySignal
