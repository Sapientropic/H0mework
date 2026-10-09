import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Producer.SourceRaisingMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.FiniteTimeRemainder

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.ProjectedOrbit

open Powered.Dynamics Load.Producer.StrictThermal Load.Producer.FiniteRemainder
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Space (ι : Type*) := EuclideanSpace ℂ (ι × Fin 2)

def interactionUnitary (V : ControllerJoint ι) (hV : V.IsHermitian) (s : ℝ) :
    Matrix.unitaryGroup (ι × Fin 2) ℂ := flowUnitary 0 0 V Matrix.isHermitian_zero hV s

omit [Fintype ι] in
theorem interactionHamiltonian (V : ControllerJoint ι) : totalHamiltonian 0 0 V = V := by
  have zero : controllerHamiltonian 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [controllerHamiltonian]
  simp [totalHamiltonian, bareHamiltonian, zero, Matrix.kronecker]

theorem interactionUnitary_derivative (V : ControllerJoint ι) (hV : V.IsHermitian) (s : ℝ) :
    HasDerivAt (fun t => (interactionUnitary V hV t : ControllerJoint ι))
      ((interactionUnitary V hV s : ControllerJoint ι) * (-Complex.I • V)) s := by
  simpa only [interactionUnitary, interactionHamiltonian] using
    flowUnitary_hasDerivAt 0 0 V Matrix.isHermitian_zero hV s

abbrev op (A : ControllerJoint ι) : Space ι →L[ℂ] Space ι :=
  Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ) A

theorem interaction_orbit_derivative (V : ControllerJoint ι) (hV : V.IsHermitian)
    (x : Space ι) (s : ℝ) :
    HasDerivAt (fun t => op (interactionUnitary V hV t) x)
      (op (interactionUnitary V hV s) (op (-Complex.I • V) x)) s := by
  let evaluation : ControllerJoint ι →L[ℝ] Space ι :=
    ((ContinuousLinearMap.apply ℂ (Space ι) x).comp
      (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.toContinuousLinearMap).restrictScalars ℝ
  have derivative := evaluation.hasFDerivAt.comp_hasDerivAt s (interactionUnitary_derivative V hV s)
  change HasDerivAt (fun t => op (interactionUnitary V hV t) x)
    (op ((interactionUnitary V hV s : ControllerJoint ι) * (-Complex.I • V)) x) s at derivative
  simpa only [op, map_mul, mul_apply_eq_comp] using derivative

theorem interaction_orbit_norm (V : ControllerJoint ι) (hV : V.IsHermitian)
    (x : Space ι) (s : ℝ) : ‖op (interactionUnitary V hV s) x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    (Unitary.map_mem (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ))
      (interactionUnitary V hV s).property) x

theorem interaction_orbit_remainder (V : ControllerJoint ι) (hV : V.IsHermitian)
    (x : Space ι) (t : ℝ) (ht : 0 ≤ t) :
    ‖op (interactionUnitary V hV t) x - x - t • op (-Complex.I • V) x‖ ≤
      ‖V‖ * ‖op V x‖ * t ^ 2 := by
  have velocityNorm : ‖op (-Complex.I • V) x‖ = ‖op V x‖ := by
    rw [op, map_smul]
    simp only [smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have generatorNorm : ‖op (-Complex.I • V)‖ = ‖V‖ := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, norm_smul]
    simp
  have secondBound (s : ℝ) :
      ‖op (interactionUnitary V hV s) (op (-Complex.I • V) (op (-Complex.I • V) x))‖ ≤
        ‖V‖ * ‖op V x‖ := by
    rw [interaction_orbit_norm]
    simpa only [generatorNorm, velocityNorm] using
      (op (-Complex.I • V)).le_opNorm (op (-Complex.I • V) x)
  have bound := firstOrder_error_le
    (fun s => op (interactionUnitary V hV s) x)
    (fun s => op (interactionUnitary V hV s) (op (-Complex.I • V) x))
    (fun s => op (interactionUnitary V hV s) (op (-Complex.I • V) (op (-Complex.I • V) x)))
    t (‖V‖ * ‖op V x‖) ht (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (interaction_orbit_derivative V hV x)
    (interaction_orbit_derivative V hV (op (-Complex.I • V) x))
    (fun s _ => secondBound s)
  simpa only [op, interactionUnitary, flowUnitary_zero, OneMemClass.coe_one,
    map_one, one_apply_eq_self] using bound

theorem projected_orbit_lower (V : ControllerJoint ι) (hV : V.IsHermitian)
    (Q : ControllerJoint ι) (contractive : ‖Q‖ ≤ 1)
    (x : Space ι) (empty : op Q x = 0) (received : op Q (op V x) = op V x)
    (t : ℝ) (ht : 0 ≤ t) (small : t * ‖V‖ ≤ 1 / 2) :
    t / 2 * ‖op V x‖ ≤ ‖op Q (op (interactionUnitary V hV t) x)‖ := by
  let defect := op (interactionUnitary V hV t) x - x - t • op (-Complex.I • V) x
  have generator : op (-Complex.I • V) x = -Complex.I • op V x := by
    rw [op, map_smul]
    rfl
  have projection : op Q defect =
      op Q (op (interactionUnitary V hV t) x) - t • op (-Complex.I • V) x := by
    have projectedGenerator : op Q (op (-Complex.I • V) x) = op (-Complex.I • V) x := by
      rw [generator, map_smul, received]
    simp only [defect, map_sub, empty, sub_zero]
    rw [(op Q).map_smul_of_tower, projectedGenerator]
  have error : ‖op Q defect‖ ≤ ‖V‖ * ‖op V x‖ * t ^ 2 := by
    calc
      _ ≤ ‖op Q‖ * ‖defect‖ := (op Q).le_opNorm defect
      _ ≤ ‖defect‖ := by
        rw [Matrix.l2_opNorm_toEuclideanCLM]
        exact mul_le_of_le_one_left (norm_nonneg _) contractive
      _ ≤ _ := interaction_orbit_remainder V hV x t ht
  rw [projection] at error
  have triangle := norm_le_norm_add_norm_sub
    (op Q (op (interactionUnitary V hV t) x)) (t • op (-Complex.I • V) x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, generator, norm_smul,
    norm_neg, Complex.norm_I, one_mul] at triangle
  rw [generator] at error
  have scaled := mul_le_mul_of_nonneg_right small (mul_nonneg ht (norm_nonneg (op V x)))
  nlinarith

end
end LAlanine40K2025.Thermal.Recovery.ProjectedOrbit
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
