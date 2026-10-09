import H0mework.Chemistry.LAlanineThermalDynamics.FiniteControllerFlow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! # Matrix derivative readouts of the existing P257 finite-controller flow -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.StrictThermal

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem flowUnitary_matrix_exp (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    (flowUnitary H gap V hH hV t : ControllerJoint ι) =
      NormedSpace.exp (t • (-Complex.I • totalHamiltonian H gap V)) := by
  let e := Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)
  let : NormedAlgebra ℚ (ControllerSpace ι →L[ℂ] ControllerSpace ι) :=
    .restrictScalars ℚ ℂ _
  change e.symm (NormedSpace.exp _) = _
  rw [NormedSpace.map_exp e.symm
    e.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous]
  congr 1
  simp only [map_smul, controllerOperator, e, StarAlgEquiv.symm_apply_apply]
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul]

theorem flowUnitary_hasDerivAt (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    HasDerivAt (fun s => (flowUnitary H gap V hH hV s : ControllerJoint ι))
      ((flowUnitary H gap V hH hV t : ControllerJoint ι) *
        (-Complex.I • totalHamiltonian H gap V)) t := by
  simp only [flowUnitary_matrix_exp]
  exact hasDerivAt_exp_smul_const _ _

theorem flowUnitary_neg (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    flowUnitary H gap V hH hV (-t) = star (flowUnitary H gap V hH hV t) := by
  apply mul_left_cancel (a := flowUnitary H gap V hH hV t)
  rw [← flowUnitary_add, add_neg_cancel, flowUnitary_zero]
  simp

theorem coupledNext_eq_two_slices (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian)
    (t : ℝ) (rho : ControllerJoint ι) :
    coupledNext H gap V hH hV t rho =
      (flowUnitary H gap V hH hV t : ControllerJoint ι) * rho *
        (flowUnitary H gap V hH hV (-t) : ControllerJoint ι) := by
  rw [coupledNext, Unitary.conjStarAlgAut_apply, flowUnitary_neg]
  rfl

theorem coupledNext_hasDerivAt (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian)
    (t : ℝ) (rho : ControllerJoint ι) :
    HasDerivAt (fun s => coupledNext H gap V hH hV s rho)
      (coupledNext H gap V hH hV t
        (-Complex.I • (totalHamiltonian H gap V * rho -
          rho * totalHamiltonian H gap V))) t := by
  have backward := (flowUnitary_hasDerivAt H gap V hH hV (-t)).scomp t
    ((hasDerivAt_id t).neg)
  have derivative := ((flowUnitary_hasDerivAt H gap V hH hV t).mul_const rho).mul backward
  simp only [Function.comp_apply, neg_smul, one_smul, mul_neg] at derivative
  simp only [coupledNext_eq_two_slices]
  apply derivative.congr_deriv
  have commute : Commute (totalHamiltonian H gap V)
      (flowUnitary H gap V hH hV (-t) : ControllerJoint ι) :=
    observable_commutes_with_flow H gap V hH hV (-t) _ (Commute.refl _)
  simp only [neg_neg, neg_smul, neg_mul, mul_neg, mul_smul_comm, smul_mul_assoc,
    smul_sub, mul_sub, sub_mul]
  simp only [mul_assoc]
  rw [commute.eq]
  module

def energyCLM (O : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.restrictScalars ℝ).comp
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ) O))

theorem energyCLM_apply (O rho : Matrix ι ι ℂ) : energyCLM O rho = Collision.energy O rho := rfl

theorem coupledEnergy_hasDerivAt (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian)
    (t : ℝ) (rho O : ControllerJoint ι) :
    HasDerivAt (fun s => Collision.energy O (coupledNext H gap V hH hV s rho))
      (Collision.energy O (coupledNext H gap V hH hV t
        (-Complex.I • (totalHamiltonian H gap V * rho -
          rho * totalHamiltonian H gap V)))) t :=
  (energyCLM O).hasFDerivAt.comp_hasDerivAt t (coupledNext_hasDerivAt H gap V hH hV t rho)

theorem flowUnitary_sub_one_norm_le (H : Matrix ι ι ℂ) (gap : ℝ)
    (V : ControllerJoint ι) (hH : H.IsHermitian) (hV : V.IsHermitian)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    ‖(flowUnitary H gap V hH hV t : ControllerJoint ι) - 1‖ ≤
      ‖totalHamiltonian H gap V‖ * t := by
  have bound := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := t)
    (fun s _ => (flowUnitary_hasDerivAt H gap V hH hV s).hasDerivWithinAt)
    (C := ‖totalHamiltonian H gap V‖)
    (by
      intro s _
      rw [CStarRing.norm_coe_unitary_mul, norm_smul]
      simp)
    t ⟨nonnegative, le_rfl⟩
  simpa only [flowUnitary_zero, OneMemClass.coe_one, sub_zero] using bound


end

end LAlanine40K2025.Thermal.Load.Producer.StrictThermal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
