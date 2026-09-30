import H0mework.Chemistry.LAlaninePropagation.GeneratedNativeClock
import H0mework.Chemistry.LAlanineThermalRuntime.NativeTimedPairCurrent

/-!
# One source-generated electronic effect at an addressed current

The existing source clock acts on the actual current operator. A standing
retains its rational time, source matrices and incoming conjugated density;
it stores no table of future states.
The explicitly prepared thermal branch is carried separately from this
unchanged isolated electronic flow.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Runtime

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Producer

noncomputable section

def electronicAdvance (current : ElectronicOperator) : ElectronicOperator :=
  propagator electronicSource (nativeClockStep : ℝ) * current *
    propagator electronicSource (-(nativeClockStep : ℝ))

theorem electronicAdvance_density (time : ℝ) :
    electronicAdvance (densityEvolution electronicSource time) =
      densityEvolution electronicSource (time + (nativeClockStep : ℝ)) :=
  (nativeElectronicStep_commutes time).symm

theorem electronicAdvance_changes (time : ℝ) :
    electronicAdvance (densityEvolution electronicSource time) ≠
      densityEvolution electronicSource time := by
  rw [electronicAdvance_density]
  exact nativeElectronicStep_changes time

/-- The time index is the generated target time; density retains its incoming update. -/
structure NativeElectronicStandingAt (time : ℚ) : Type where
  sourceMatrices : ElectronicPropagationSource
  sourceMatricesExact : sourceMatrices = electronicSource
  timeStamp : ℚ
  timeStampExact : timeStamp = time
  density : ElectronicOperator
  generated : density = electronicAdvance
    (densityEvolution electronicSource ((time - nativeClockStep : ℚ) : ℝ))
  thermalHistory : Option Thermal.Runtime.ThermalCollisionMaterial
  thermalHistoryExact : thermalHistory = Thermal.Runtime.collisionHistoryAt time
  currentPair : Option (Thermal.Collision.JointMatrix Basis)
  currentPairExact : currentPair = Thermal.Runtime.timedPairCurrentAt time

def nativeElectronicStanding (time : ℚ) : NativeElectronicStandingAt time where
  sourceMatrices := electronicSource
  sourceMatricesExact := rfl
  timeStamp := time
  timeStampExact := rfl
  density := electronicAdvance
    (densityEvolution electronicSource ((time - nativeClockStep : ℚ) : ℝ))
  generated := rfl
  thermalHistory := Thermal.Runtime.collisionHistoryAt time
  thermalHistoryExact := rfl
  currentPair := Thermal.Runtime.timedPairCurrentAt time
  currentPairExact := rfl

theorem NativeElectronicStandingAt.density_eq_source {time : ℚ}
    (standing : NativeElectronicStandingAt time) :
    standing.density = densityEvolution electronicSource (time : ℝ) := by
  rw [standing.generated, electronicAdvance_density, Rat.cast_sub, sub_add_cancel]

def NativeElectronicStandingAt.heldPair {time : ℚ}
    (standing : NativeElectronicStandingAt time) (held : Thermal.Runtime.HoldsCollision time) :
    Thermal.Collision.JointMatrix Basis :=
  standing.currentPair.get (by
    rw [standing.currentPairExact]
    simp only [Thermal.Runtime.timedPairCurrentAt, if_pos held, Option.isSome_some])

theorem NativeElectronicStandingAt.heldPair_exact {time : ℚ}
    (standing : NativeElectronicStandingAt time) (held : Thermal.Runtime.HoldsCollision time) :
    standing.heldPair held =
      Thermal.Producer.rememberedJoint (Thermal.Runtime.timedPairAge time : ℝ) := by
  unfold NativeElectronicStandingAt.heldPair
  simp only [standing.currentPairExact, Thermal.Runtime.timedPairCurrentAt, if_pos held,
    Option.get_some]

instance nativeElectronicStanding_subsingleton (time : ℚ) :
    Subsingleton (NativeElectronicStandingAt time) := by
  constructor
  intro left right
  rcases left with ⟨leftSource, leftSourceEq, leftTime, leftTimeEq, leftDensity, leftDensityEq,
    leftHistory, leftHistoryEq, leftPair, leftPairEq⟩
  rcases right with ⟨rightSource, rightSourceEq, rightTime, rightTimeEq, rightDensity, rightDensityEq,
    rightHistory, rightHistoryEq, rightPair, rightPairEq⟩
  cases leftSourceEq
  cases rightSourceEq
  cases leftTimeEq
  cases rightTimeEq
  cases leftDensityEq
  cases rightDensityEq
  cases leftHistoryEq
  cases rightHistoryEq
  cases leftPairEq
  cases rightPairEq
  rfl

theorem nativeStanding_receives_thermalHistory {time : ℚ}
    (current : NativeElectronicStandingAt time) :
    (nativeElectronicStanding (time + nativeClockStep)).thermalHistory =
      Thermal.Runtime.collisionHistoryUpdate time current.density current.thermalHistory :=
  Thermal.Runtime.collisionHistoryAt_receives_update time current.density
    current.density_eq_source current.thermalHistory current.thermalHistoryExact

/-- The whole-ledger writer runs the local update on its received standing. -/
def nativeElectronicStandingAfter {time : ℚ} (current : NativeElectronicStandingAt time) :
    NativeElectronicStandingAt (time + nativeClockStep) :=
  let collisionWrite := Thermal.Runtime.collisionHistoryUpdate time current.density current.thermalHistory
  let writeExact : collisionWrite = Thermal.Runtime.collisionHistoryAt (time + nativeClockStep) :=
    (Thermal.Runtime.collisionHistoryAt_receives_update time current.density
      current.density_eq_source current.thermalHistory current.thermalHistoryExact).symm
  { sourceMatrices := current.sourceMatrices
    sourceMatricesExact := current.sourceMatricesExact
    timeStamp := current.timeStamp + nativeClockStep
    timeStampExact := by rw [current.timeStampExact]
    density := electronicAdvance current.density
    generated := by rw [current.density_eq_source, add_sub_cancel_right]
    thermalHistory := collisionWrite
    thermalHistoryExact := writeExact
    currentPair := Thermal.Runtime.timedPairCurrentUpdate time collisionWrite current.currentPair
    currentPairExact :=
      (Thermal.Runtime.timedPairCurrentAt_receives_update time collisionWrite writeExact
        current.currentPair current.currentPairExact).symm }

/-- Complete material effect; the target is generated from the received current. -/
structure NativeElectronicStepAt (time : ℚ) : Type where
  sourceMatrices : ElectronicPropagationSource
  sourceMatricesExact : sourceMatrices = electronicSource
  currentTime : ℚ
  currentTimeExact : currentTime = time
  currentDensity : ElectronicOperator
  currentDensityExact : currentDensity = densityEvolution electronicSource (time : ℝ)
  duration : ℚ
  durationExact : duration = nativeClockStep
  durationPositive : 0 < duration
  targetTime : ℚ
  targetTimeExact : targetTime = currentTime + duration
  targetDensity : ElectronicOperator
  generated : targetDensity = electronicAdvance currentDensity
  responds : targetDensity ≠ currentDensity

def nativeElectronicStep (time : ℚ) (current : ElectronicOperator)
    (currentExact : current = densityEvolution electronicSource (time : ℝ)) :
    NativeElectronicStepAt time where
  sourceMatrices := electronicSource
  sourceMatricesExact := rfl
  currentTime := time
  currentTimeExact := rfl
  currentDensity := current
  currentDensityExact := currentExact
  duration := nativeClockStep
  durationExact := rfl
  durationPositive := nativeClockStep_positive
  targetTime := time + nativeClockStep
  targetTimeExact := rfl
  targetDensity := electronicAdvance current
  generated := rfl
  responds := by
    rw [currentExact]
    exact electronicAdvance_changes (time : ℝ)

theorem NativeElectronicStepAt.target_eq_source {time : ℚ}
    (step : NativeElectronicStepAt time) :
    step.targetDensity = densityEvolution electronicSource (step.targetTime : ℝ) := by
  rw [step.generated, step.currentDensityExact, electronicAdvance_density,
    step.targetTimeExact, step.currentTimeExact, step.durationExact, Rat.cast_add]

theorem nativeStanding_receives_step (time : ℚ) (current : ElectronicOperator)
    (currentExact : current = densityEvolution electronicSource (time : ℝ)) :
    (nativeElectronicStanding (time + nativeClockStep)).density =
      (nativeElectronicStep time current currentExact).targetDensity := by
  rw [NativeElectronicStandingAt.density_eq_source,
    NativeElectronicStepAt.target_eq_source]
  rfl

end

end LAlanine40K2025.Propagation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
