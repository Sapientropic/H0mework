import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadCurrent
import H0mework.Realization.Fields.FirstOrderRemainder
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.FlowReadout

/-! # Finite-time remainder of the existing source unitary flow -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.FiniteRemainder

open Set

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def interactionPicture (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) : ControllerJoint ι :=
  (flowUnitary H gap 0 hH (Matrix.isHermitian_zero) (-t) : ControllerJoint ι) *
    (flowUnitary H gap V hH hV t : ControllerJoint ι)

def interactionVelocity (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) : ControllerJoint ι :=
  (flowUnitary H gap 0 hH (Matrix.isHermitian_zero) (-t) : ControllerJoint ι) *
    (-Complex.I • V) * (flowUnitary H gap V hH hV t : ControllerJoint ι)

def interactionAcceleration (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) : ControllerJoint ι :=
  (flowUnitary H gap 0 hH (Matrix.isHermitian_zero) (-t) : ControllerJoint ι) *
    (bareHamiltonian H gap * V - V * totalHamiltonian H gap V) *
      (flowUnitary H gap V hH hV t : ControllerJoint ι)

theorem backward_hasDerivAt (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    HasDerivAt (fun s => (flowUnitary H gap V hH hV (-s) : ControllerJoint ι))
      ((flowUnitary H gap V hH hV (-t) : ControllerJoint ι) *
        (Complex.I • totalHamiltonian H gap V)) t := by
  have derivative := (flowUnitary_hasDerivAt H gap V hH hV (-t)).scomp t
    ((hasDerivAt_id t).neg)
  simpa only [Function.comp_def, neg_smul, one_smul, mul_neg, neg_neg] using derivative

theorem interactionPicture_hasDerivAt (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    HasDerivAt (interactionPicture H gap V hH hV) (interactionVelocity H gap V hH hV t) t := by
  have backward := backward_hasDerivAt H gap 0 hH Matrix.isHermitian_zero t
  have derivative := backward.mul (flowUnitary_hasDerivAt H gap V hH hV t)
  apply derivative.congr_deriv
  have commute := (observable_commutes_with_flow H gap V hH hV t
    (totalHamiltonian H gap V) (Commute.refl _)).eq
  simp only [interactionVelocity, mul_smul_comm, smul_mul_assoc, neg_smul,
    neg_mul, mul_neg, mul_assoc]
  rw [← commute]
  simp only [totalHamiltonian, add_zero, add_mul]
  simp only [mul_add, smul_add]
  module

theorem interactionVelocity_hasDerivAt (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    HasDerivAt (interactionVelocity H gap V hH hV) (interactionAcceleration H gap V hH hV t) t := by
  have backward := backward_hasDerivAt H gap 0 hH Matrix.isHermitian_zero t
  have derivative := (backward.mul_const (-Complex.I • V)).mul
    (flowUnitary_hasDerivAt H gap V hH hV t)
  apply derivative.congr_deriv
  have commute := (observable_commutes_with_flow H gap V hH hV t
    (totalHamiltonian H gap V) (Commute.refl _)).eq
  simp only [interactionAcceleration, mul_smul_comm, smul_mul_assoc, neg_smul,
    neg_mul, mul_neg, mul_assoc]
  rw [← commute]
  simp only [totalHamiltonian, add_zero, add_mul, smul_smul, Complex.I_mul_I,
    neg_one_smul, mul_sub, sub_mul]
  simp only [mul_add, mul_assoc, smul_add, smul_neg, smul_smul, Complex.I_mul_I,
    neg_one_smul, neg_neg, add_mul]
  module

theorem interactionAcceleration_norm (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    ‖interactionAcceleration H gap V hH hV t‖ ≤
      2 * ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ ^ 2 := by
  unfold interactionAcceleration
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  calc
    _ ≤ ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ * ‖totalHamiltonian H gap V‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ * (‖bareHamiltonian H gap‖ + ‖V‖) := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

theorem interactionPicture_firstOrder_error (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) (ht : 0 ≤ t) :
    ‖interactionPicture H gap V hH hV t - 1 - t • (-Complex.I • V)‖ ≤
      (2 * ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ ^ 2) * t ^ 2 := by
  have estimate := firstOrder_error_le (interactionPicture H gap V hH hV)
    (interactionVelocity H gap V hH hV) (interactionAcceleration H gap V hH hV) t
    (2 * ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ ^ 2) ht (by positivity)
    (interactionPicture_hasDerivAt H gap V hH hV) (interactionVelocity_hasDerivAt H gap V hH hV)
    (fun s _ => interactionAcceleration_norm H gap V hH hV s)
  simpa only [interactionPicture, interactionVelocity, neg_zero, flowUnitary_zero,
    OneMemClass.coe_one, mul_one, one_mul] using estimate

theorem interactionPicture_quarterStep_error (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    (clock : t ≤ 1 / 2000) (bareBound : ‖bareHamiltonian H gap‖ ≤ 245) (couplingBound : ‖V‖ ≤ 1) :
    ‖interactionPicture H gap V hH hV t - 1 - t • (-Complex.I • V)‖ ≤ t / 4 := by
  have coefficient : 2 * ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ ^ 2 ≤ 500 := by
    calc
      _ ≤ 2 * 245 * 1 + (1 : ℝ) ^ 2 := by gcongr
      _ ≤ _ := by norm_num
  calc
    _ ≤ (2 * ‖bareHamiltonian H gap‖ * ‖V‖ + ‖V‖ ^ 2) * t ^ 2 :=
      interactionPicture_firstOrder_error H gap V hH hV t ht
    _ ≤ 500 * t ^ 2 := mul_le_mul_of_nonneg_right coefficient (sq_nonneg t)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right clock ht]

end

end LAlanine40K2025.Thermal.Load.Producer.FiniteRemainder
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
