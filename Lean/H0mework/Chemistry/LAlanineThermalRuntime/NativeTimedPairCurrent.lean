import H0mework.Chemistry.LAlanineThermalRuntime.NativeThermalHistory
import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedRememberedPair

/-! # The retained joint is the received current of each timed update -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Runtime

open Propagation.Interface Propagation.Producer Preparation Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Producer
open scoped ComplexOrder

noncomputable section

def timedPairInitialTime : ℚ := collisionCurrentTime + nativeClockStep
def timedPairAge (time : ℚ) : ℚ := time - timedPairInitialTime

/-- The canonical law is an output invariant, not the next-state writer. -/
def timedPairCurrentAt (time : ℚ) : Option (JointMatrix Basis) :=
  if HoldsCollision time then some (rememberedJoint (timedPairAge time : ℝ)) else none

/-- Initialization consumes this occurrence's collision write; later steps consume the held joint. -/
def timedPairCurrentUpdate (time : ℚ) (collisionWrite : Option ThermalCollisionMaterial)
    (currentPair : Option (JointMatrix Basis)) : Option (JointMatrix Basis) :=
  if time = collisionCurrentTime then collisionWrite.map ThermalCollisionMaterial.joint
  else currentPair.map timedPairNativeStep

theorem timedPairAge_next (time : ℚ) :
    timedPairAge (time + nativeClockStep) = timedPairAge time + nativeClockStep := by
  unfold timedPairAge
  ring

theorem timedPairCurrentAt_before : timedPairCurrentAt collisionCurrentTime = none := by
  simp only [timedPairCurrentAt, if_neg collision_not_already_held]

theorem timedPairCurrentAt_initial :
    timedPairCurrentAt timedPairInitialTime = some sourceCollisionMaterial.joint := by
  have held : HoldsCollision timedPairInitialTime := collision_next_held
  rw [timedPairCurrentAt, if_pos held]
  simp only [timedPairAge, sub_self, Rat.cast_zero, rememberedJoint_initial,
    sourceCollisionMaterial_joint]

theorem timedPairCurrentAt_receives_update (time : ℚ)
    (collisionWrite : Option ThermalCollisionMaterial)
    (writeExact : collisionWrite = collisionHistoryAt (time + nativeClockStep))
    (currentPair : Option (JointMatrix Basis))
    (currentExact : currentPair = timedPairCurrentAt time) :
    timedPairCurrentAt (time + nativeClockStep) =
      timedPairCurrentUpdate time collisionWrite currentPair := by
  subst collisionWrite currentPair
  by_cases active : time = collisionCurrentTime
  · subst time
    rw [timedPairCurrentUpdate, if_pos rfl]
    change timedPairCurrentAt timedPairInitialTime = _
    rw [timedPairCurrentAt_initial]
    simp only [collisionHistoryAt, if_pos collision_next_held, Option.map_some]
  · rw [timedPairCurrentUpdate, if_neg active]
    have gate : HoldsCollision (time + nativeClockStep) ↔ HoldsCollision time := by
      simp only [holdsCollision_next, active, false_or]
    by_cases held : HoldsCollision time
    · rw [timedPairCurrentAt, if_pos (gate.mpr held), timedPairCurrentAt, if_pos held,
        Option.map_some, timedPairAge_next, Rat.cast_add, rememberedJoint_receives_next]
    · simp only [timedPairCurrentAt, if_neg held, if_neg (mt gate.mp held), Option.map_none]

theorem timedPairCurrentUpdate_receives (time : ℚ) (inactive : time ≠ collisionCurrentTime)
    (collisionWrite : Option ThermalCollisionMaterial) (joint : JointMatrix Basis) :
    timedPairCurrentUpdate time collisionWrite (some joint) = some (timedPairNativeStep joint) := by
  simp only [timedPairCurrentUpdate, if_neg inactive, Option.map_some]

theorem held_not_initializing (time : ℚ) (held : HoldsCollision time) :
    time ≠ collisionCurrentTime := by
  rintro rfl
  exact collision_not_already_held held

/-- The active face retains the received current and the law-generated target together. -/
structure TimedPairStepAt (time : ℚ) : Type where
  sourceHamiltonian : SystemMatrix Basis
  sourceHamiltonianExact : sourceHamiltonian = energyHamiltonian
  coupling : ℝ
  couplingExact : coupling = pairCoupling
  currentTime : ℚ
  currentTimeExact : currentTime = time
  localAge : ℚ
  localAgeExact : localAge = timedPairAge time
  duration : ℚ
  durationExact : duration = nativeClockStep
  durationPositive : 0 < duration
  currentJoint : JointMatrix Basis
  currentExact : currentJoint = rememberedJoint (timedPairAge time : ℝ)
  targetTime : ℚ
  targetTimeExact : targetTime = currentTime + duration
  targetJoint : JointMatrix Basis
  generated : targetJoint = timedPairNativeStep currentJoint

def timedPairStep (time : ℚ) (current : JointMatrix Basis)
    (currentExact : current = rememberedJoint (timedPairAge time : ℝ)) : TimedPairStepAt time where
  sourceHamiltonian := energyHamiltonian
  sourceHamiltonianExact := rfl
  coupling := pairCoupling
  couplingExact := rfl
  currentTime := time
  currentTimeExact := rfl
  localAge := timedPairAge time
  localAgeExact := rfl
  duration := nativeClockStep
  durationExact := rfl
  durationPositive := nativeClockStep_positive
  currentJoint := current
  currentExact := currentExact
  targetTime := time + nativeClockStep
  targetTimeExact := rfl
  targetJoint := timedPairNativeStep current
  generated := rfl

theorem TimedPairStepAt.target_eq_source {time : ℚ} (step : TimedPairStepAt time) :
    step.targetJoint = rememberedJoint (timedPairAge step.targetTime : ℝ) := by
  rw [step.generated, step.currentExact, step.targetTimeExact, step.currentTimeExact,
    step.durationExact, timedPairAge_next, Rat.cast_add, rememberedJoint_receives_next]

theorem TimedPairStepAt.target_positive_normalized {time : ℚ} (step : TimedPairStepAt time) :
    step.targetJoint.PosSemidef ∧ step.targetJoint.trace = 1 := by
  rw [step.target_eq_source]
  exact ⟨rememberedJoint_posSemidef _, rememberedJoint_trace _⟩

end

end LAlanine40K2025.Thermal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
