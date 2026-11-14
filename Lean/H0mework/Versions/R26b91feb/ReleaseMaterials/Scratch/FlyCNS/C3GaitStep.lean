import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3CPGStep
set_option autoImplicit false
namespace FlyCNS.C3Gait
open FlyCNS.C3Actuation

def one : Float := Float.ofBits 0x3ff0000000000000
def two : Float := Float.ofBits 0x4000000000000000
def twoPi : Float := Float.ofBits 0x401921fb54442d18

/-- Exact dyadic fmod followed by NumPy's positive-divisor sign adjustment. -/
def remainder (a b : Float) : Float :=
  match finiteDyadic a, finiteDyadic b with
  | some (ma,ea,sa), some (mb,eb,_) =>
    let exponent := min ea eb
    let numerator := ma.natAbs*2^(ea-exponent).toNat
    let denominator := mb.natAbs*2^(eb-exponent).toNat
    let magnitude := numerator % denominator
    if magnitude == 0 then zero
    else
      let signed := if sa then -(magnitude : Int) else (magnitude : Int)
      let value := Float.ofModel (Float.Model.pack (Float.Model.UnpackedFloat.normalize Float.Model.Format.binary64 signed exponent .positive))
      if sa then value+b else value
  | _,_ => Float.ofBits 0x7ff8000000000000

structure Spline where
  knots : Array Float
  coefficients : Array Float
  neutral : Array Float
  deriving Inhabited

/-- Original SciPy power-basis summation order, followed by the registered
neutral-pose scaling. Coefficients are source ROM, never next-angle outputs. -/
def angles (m : Spline) (phase magnitude : Float) : Array Float := Id.run do
  let period := m.knots[m.knots.size-1]!-m.knots[0]!
  let x := m.knots[0]!+remainder (phase-m.knots[0]!) period
  let mut interval := 0
  for i in [:m.knots.size-1] do
    if x >= m.knots[i]! then interval := i
  let delta := x-m.knots[interval]!
  return (List.range 7).toArray.map fun dof => Id.run do
    let mut power := one
    let mut result := zero
    for degree in [:4] do
      let coefficient := m.coefficients[((3-degree)*(m.knots.size-1)+interval)*7+dof]!
      result := result+coefficient*power
      if degree < 3 then power := power*delta
    return m.neutral[dof]!+magnitude*(result-m.neutral[dof]!)

structure Material where
  oscillator : FlyCNS.C3CPG.Material
  splines : Array Spline
  swing : Array Float
  baseFrequencies : Array Float
  correctionVectors : Array Float
  outputOrder : Array Nat
  retractionHeight : Float
  retractionRates : Array Float
  stumblingThreshold : Float
  stumblingRates : Array Float
  maxCorrection : Float
  extension : Float
  persistenceSteps : Int64
  persistenceThreshold : Float
  adhesionEnabled : Bool

structure State where
  oscillator : FlyCNS.C3CPG.State
  retraction : Array Float
  stumbling : Array Float
  persistence : Array Int64

structure Observation where
  thorax : Float
  tarsi : Array Float
  forces : Array Float
  heading : Array Float

structure Result where
  state : State
  jointAngles : Array Float
  adhesion : Array Bool
  netCorrection : Array Float
  stumblingMask : Array Bool
  selected : Option Nat

/-- NumPy's scalar five-point linear interpolation with the original order. -/
def phaseGain (m : Material) (leg : Nat) (phase : Float) : Float := Id.run do
  let start := m.swing[2*leg]!
  let stop := m.swing[2*leg+1]!
  let points := #[start,(start+stop)/two,stop+m.extension,(stop+twoPi)/two,twoPi]
  let values := #[zero,Float.ofBits 0x3fe999999999999a,zero,Float.ofBits 0xbfb999999999999a,zero]
  if phase < points[0]! then return values[0]!
  if phase >= points[4]! then return values[4]!
  let mut index := 0
  for i in [:4] do if phase >= points[i]! then index := i
  if phase == points[index]! then return values[index]!
  let slope := (values[index+1]!-values[index]!)/(points[index+1]!-points[index]!)
  return slope*(phase-points[index]!)+values[index]!

def advance (m : Material) (s : State) (signal : Array Float) (obs : Observation) : Result := Id.run do
  let heights := obs.tarsi.map fun v => obs.thorax-v
  let mut order := (List.range 6).toArray
  for i in [1:6] do
    let mut j := i
    while j > 0 && heights[order[j-1]!]! > heights[order[j]!]! do
      let previous := order[j-1]!
      order := (order.set! (j-1) order[j]!).set! j previous
      j := j-1
  let selected := if heights[order[5]!]! > heights[order[3]!]!+m.retractionHeight then some order[5]! else none
  let mut persistence := s.persistence
  if let some leg := selected then
    if s.retraction[leg]! > m.persistenceThreshold then persistence := persistence.set! leg 1
  persistence := persistence.map fun v =>
    let next := if v > 0 then v+1 else v
    if next > m.persistenceSteps then 0 else next
  let mask := (List.range 6).toArray.map fun leg => (List.range 3).any fun link =>
    let start := (leg*3+link)*3
    let projection := ((obs.forces[start]!*obs.heading[0]!)+obs.forces[start+1]!*obs.heading[1]!)+obs.forces[start+2]!*obs.heading[2]!
    projection < m.stumblingThreshold
  let oscillators := {s.oscillator with
    amplitudes := (List.range 6).toArray.map fun i => signal[i/3]!.abs
    frequencies := m.baseFrequencies.mapIdx fun i v => v*(if signal[i/3]! >= zero then one else -one)}
  let oscillator := FlyCNS.C3CPG.advance m.oscillator oscillators
  let mut retraction := s.retraction
  let mut stumbling := s.stumbling
  let mut allAngles := #[]
  let mut adhesion := #[]
  let mut corrections := #[]
  for leg in [:6] do
    let retract := selected == some leg || persistence[leg]! > 0
    retraction := retraction.set! leg (if retract then retraction[leg]!+m.retractionRates[0]!*m.oscillator.timestep
      else max zero (retraction[leg]!-m.retractionRates[1]!*m.oscillator.timestep))
    stumbling := stumbling.set! leg (if mask[leg]! then stumbling[leg]!+m.stumblingRates[0]!*m.oscillator.timestep
      else max zero (stumbling[leg]!-m.stumblingRates[1]!*m.oscillator.timestep))
    let net := if retraction[leg]! > zero then retraction[leg]! else stumbling[leg]!
    if retraction[leg]! > zero then stumbling := stumbling.set! leg zero
    let correction := (min m.maxCorrection (max zero net))*phaseGain m leg (remainder oscillator.phases[leg]! twoPi)
    corrections := corrections.push correction
    let base := angles m.splines[leg]! oscillator.phases[leg]! oscillator.magnitudes[leg]!
    allAngles := allAngles ++ base.mapIdx fun i v => v+correction*m.correctionVectors[7*leg+i]!
    let p := remainder oscillator.phases[leg]! twoPi
    adhesion := adhesion.push (m.adhesionEnabled && !(m.swing[2*leg]! < p && p < m.swing[2*leg+1]!+m.extension))
  return ⟨⟨oscillator,retraction,stumbling,persistence⟩,
    m.outputOrder.map (fun i => allAngles[i]!),adhesion,corrections,mask,selected⟩
end FlyCNS.C3Gait
