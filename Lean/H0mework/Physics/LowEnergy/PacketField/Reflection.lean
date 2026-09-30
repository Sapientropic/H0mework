import H0mework.Physics.LowEnergy.PacketField.Frame
import Mathlib.Data.Real.Sign

/-! Opposite physical momenta use exactly the same Borel spin frame. Their
signed axial momentum then carries the original Fourier reality relation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open Rotation
noncomputable section

def firstNonzero (momentum : Fin 3 → ℝ) : ℝ :=
  if momentum 2≠0 then momentum 2 else if momentum 1≠0 then momentum 1 else momentum 0

def lineSign (momentum : Fin 3 → ℝ) : ℝ := Real.sign (firstNonzero momentum)
def representative (momentum : Fin 3 → ℝ) : Fin 3 → ℝ := lineSign momentum • momentum
def pairedParameters (momentum : Fin 3 → ℝ) : ℝ×ℝ := borelParameters (representative momentum)

theorem firstNonzero_negative (momentum : Fin 3 → ℝ) : firstNonzero (-momentum)= -firstNonzero momentum := by
  simp only [firstNonzero,Pi.neg_apply,neg_ne_zero]
  split_ifs <;> rfl

theorem firstNonzero_nonzero (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : firstNonzero momentum≠0 := by
  unfold firstNonzero
  split_ifs with last middle
  · exact last
  · exact middle
  · intro first
    apply nonzero
    funext index
    fin_cases index <;> simp_all

theorem lineSign_negative (momentum : Fin 3 → ℝ) : lineSign (-momentum)= -lineSign momentum := by
  rw [lineSign,firstNonzero_negative,Real.sign_neg]
  rfl

theorem lineSign_cases (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    lineSign momentum= -1 ∨ lineSign momentum=1 :=
  Real.sign_apply_eq_of_ne_zero _ (firstNonzero_nonzero momentum nonzero)

theorem lineSign_square (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : (lineSign momentum)^2=1 := by
  rcases lineSign_cases momentum nonzero with negative | positive
  · rw [negative]
    norm_num
  · rw [positive]
    norm_num

theorem representative_negative (momentum : Fin 3 → ℝ) : representative (-momentum)=representative momentum := by
  simp only [representative,lineSign_negative,neg_smul,smul_neg,neg_neg]

theorem representative_nonzero (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : representative momentum≠0 := by
  rcases lineSign_cases momentum nonzero with negative | positive
  · simpa only [representative,negative,neg_one_smul,neg_ne_zero] using nonzero
  · simpa only [representative,positive,one_smul] using nonzero

theorem representative_radius (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    momentumRadius (representative momentum)=momentumRadius momentum := by
  simp only [momentumRadius,representative,Pi.smul_apply,smul_eq_mul,mul_pow,lineSign_square momentum nonzero,one_mul]

theorem pairedParameters_negative (momentum : Fin 3 → ℝ) : pairedParameters (-momentum)=pairedParameters momentum := by
  rw [pairedParameters,representative_negative]
  rfl

theorem firstNonzero_measurable : Measurable firstNonzero := by
  unfold firstNonzero
  apply Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 2) measurable_const).compl (measurable_pi_apply 2)
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 1) measurable_const).compl
    (measurable_pi_apply 1) (measurable_pi_apply 0)

theorem lineSign_measurable : Measurable lineSign := by
  unfold lineSign Real.sign
  apply Measurable.ite (measurableSet_lt firstNonzero_measurable measurable_const) measurable_const
  exact Measurable.ite (measurableSet_lt measurable_const firstNonzero_measurable) measurable_const measurable_const

theorem representative_measurable : Measurable representative := lineSign_measurable.smul measurable_id

theorem pairedParameters_measurable : Measurable pairedParameters :=
  borelParameters_measurable.comp representative_measurable

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
