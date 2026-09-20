import H0mework.Physics.RootRuntime.RuntimeActivation

/-! Five simultaneous readouts of the frozen source law, indexed by
u = physical coordinate time / first dark time. No SI calibration or
empirical outcome enters this source-generated joint block. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Prediction

open ProofFreeRicherAnholonomicSource Stage9DEF.Dynamics Stage9DEF.State
open Stage9DEF.Observation Stage9C.Material.SpinPair

noncomputable section

def jointPoint (slot : Fin 5) : BasePoint :=
  timeDisplacement ((slot.val : ℝ) / 2 * darkTime)

def jointValue : Fin 5 → ℝ := ![1, 1 / 2, 0, 1 / 2, 1]

def nextWeight (slot : Fin 5) : ℝ :=
  (vectorEvaluation (Runtime.nextTick.answer (jointPoint slot))
    (sourceEffect 0).matrix).re

theorem jointPhase (slot : Fin 5) :
    jointPoint slot 0 * frequency = (slot.val : ℝ) * Real.pi / 4 := by
  rw [jointPoint, timeDisplacement_zero]
  unfold darkTime
  field_simp [ne_of_gt frequency_positive]
  ring

private theorem five_cos_squared (slot : Fin 5) :
    Real.cos ((slot.val : ℝ) * Real.pi / 4) ^ 2 = jointValue slot := by
  fin_cases slot
  · norm_num [jointValue]
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.cast_one, one_mul]
    rw [Real.cos_pi_div_four]
    norm_num [jointValue, div_pow, Real.sq_sqrt]
  · have angle : (2 : ℝ) * Real.pi / 4 = Real.pi / 2 := by ring
    change Real.cos (2 * Real.pi / 4) ^ 2 = 0
    rw [angle, Real.cos_pi_div_two]
    norm_num
  · change Real.cos (3 * Real.pi / 4) ^ 2 = 1 / 2
    rw [Real.cos_sq]
    have angle : 2 * (3 * Real.pi / 4) = Real.pi / 2 + Real.pi := by ring
    rw [angle, Real.cos_add_pi, Real.cos_pi_div_two]
    norm_num
  · change Real.cos (4 * Real.pi / 4) ^ 2 = 1
    rw [mul_div_cancel_left₀ Real.pi (by norm_num : (4 : ℝ) ≠ 0), Real.cos_pi]
    norm_num

theorem nextWeight_joint (slot : Fin 5) : nextWeight slot = jointValue slot := by
  rw [nextWeight, Runtime.nextTick_vector]
  change coherentWeight (jointPoint slot) = _
  rw [coherentWeight_cos, jointPhase]
  exact five_cos_squared slot

theorem exclusive_joint (slot : Fin 5) : exclusiveWeight (jointPoint slot) = 1 / 2 :=
  exclusiveWeight_formula _

def JointPrediction : Prop :=
    (∀ slot, nextWeight slot = jointValue slot) ∧
    (∀ slot, exclusiveWeight (jointPoint slot) = 1 / 2) ∧
    frequency ^ 2 = 972 / 3125 ∧ Runtime.SameOccurrenceActivation

theorem sourceClosedJoint : JointPrediction :=
  ⟨nextWeight_joint, exclusive_joint, source_frequency_squared,
    Runtime.sameOccurrenceActivation⟩

end
end SaturationMonoid.PhysicsCore.Stage10.Prediction
