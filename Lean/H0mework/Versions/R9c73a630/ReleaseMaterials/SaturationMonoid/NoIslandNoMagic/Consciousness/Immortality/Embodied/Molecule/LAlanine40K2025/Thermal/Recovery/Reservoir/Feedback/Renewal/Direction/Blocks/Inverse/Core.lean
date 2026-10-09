import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyTransferSpectatorKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyMeasurementTraceDual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.BasisInverse
open Collision
open scoped Matrix ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dual (t : ι) (c s : ℝ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (c : ℂ)^2 • O + ((s : ℂ)^2 * O t t) • 1 +
    (Complex.I * c * s) • (Spectrum.basisPure t * O - O * Spectrum.basisPure t)

theorem dual_entry (t : ι) (c s : ℝ) (O : Matrix ι ι ℂ) (i j : ι) :
    dual t c s O i j = (c : ℂ)^2 * O i j +
      (s : ℂ)^2 * O t t * (if i = j then 1 else 0) +
      (Complex.I*c*s) * ((if i = t then O i j else 0) - (if j = t then O i j else 0)) := by
  simp [dual, Spectrum.basisPure, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.one_apply, smul_eq_mul, mul_ite, ite_mul]

def inverse (t : ι) (c s : ℝ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j =>
  if i = t then
    if j = t then O i j else O i j / ((c : ℂ)^2 + Complex.I*c*s)
  else if j = t then O i j / ((c : ℂ)^2 - Complex.I*c*s)
  else (O i j - (s : ℂ)^2 * (if i = j then O t t else 0)) / (c : ℂ)^2

theorem denominators (c s : ℝ) (nonzero : c ≠ 0) :
    (c : ℂ)^2 ≠ 0 ∧ (c : ℂ)^2 + Complex.I*c*s ≠ 0 ∧
      (c : ℂ)^2 - Complex.I*c*s ≠ 0 := by
  refine ⟨pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr nonzero), ?_, ?_⟩
  · intro zero
    have re := congrArg Complex.re zero
    simp [pow_two, Complex.mul_re] at re
    exact nonzero re
  · intro zero
    have re := congrArg Complex.re zero
    simp [pow_two, Complex.mul_re] at re
    exact nonzero re

theorem dual_inverse (t : ι) (c s : ℝ) (unit : c^2+s^2 = 1) (nonzero : c ≠ 0)
    (O : Matrix ι ι ℂ) : dual t c s (inverse t c s O) = O := by
  have den := denominators c s nonzero
  have unitC : (c : ℂ)^2+(s : ℂ)^2 = 1 := by exact_mod_cast unit
  ext i j
  rw [dual_entry]
  by_cases left : i = t
  · subst i
    by_cases right : j = t
    · subst j
      simp only [inverse, ite_true, mul_one, sub_self, mul_zero, add_zero]
      rw [← add_mul, unitC, one_mul]
    · simp only [inverse, if_neg right, if_neg (Ne.symm right), ite_true, mul_zero,
        add_zero, sub_zero]
      rw [← add_mul, mul_div_cancel₀ _ den.2.1]
  · by_cases right : j = t
    · subst j
      simp only [inverse, if_neg left, ite_true, mul_zero, add_zero, zero_sub]
      rw [mul_neg, ← sub_eq_add_neg, ← sub_mul, mul_div_cancel₀ _ den.2.2]
    · by_cases same : i = j
      · subst j
        simp only [inverse, if_neg left, ite_true, mul_one, sub_self, mul_zero, add_zero]
        rw [mul_div_cancel₀ _ den.1]
        ring
      · simp only [inverse, if_neg left, if_neg right, if_neg same, ite_true,
          mul_zero, sub_zero, add_zero, sub_self]
        exact mul_div_cancel₀ _ den.1

theorem trace_basis (O : Matrix ι ι ℂ) (t : ι) :
    (O * Spectrum.basisPure t).trace = O t t := by
  simp [Spectrum.basisPure, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

theorem dual_trace (t : ι) (c s : ℝ) (O rho : Matrix ι ι ℂ) :
    (dual t c s O * rho).trace =
      (O * systemNext rho (Spectrum.basisPure t) c s).trace := by
  rw [systemNext_full, Spectrum.basisPure_trace]
  simp only [dual, one_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.one_mul, smul_eq_mul, Matrix.mul_assoc]
  rw [trace_basis]
  have cycle : (O * (rho * Spectrum.basisPure t)).trace = (Spectrum.basisPure t * O * rho).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [cycle]
  simp only [Matrix.mul_assoc]
  ring

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def bodyInverse (t : ι) (c s : ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ := fun i j =>
  inverse t c s (BodyKernel.slice O i.2 j.2) i.1 j.1

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem bodyInverse_slice (t : ι) (c s : ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) (e f : κ) :
    BodyKernel.slice (bodyInverse t c s O) e f = inverse t c s (BodyKernel.slice O e f) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_pair_slices (O rho : Matrix (ι × κ) (ι × κ) ℂ) :
    (O * rho).trace = ∑ e, ∑ f, (BodyKernel.slice O e f * BodyKernel.slice rho f e).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    BodyKernel.slice, Matrix.submatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ i, ∑ j, ∑ f, O (i, e) (j, f) * rho (j, f) (i, e)) =
      ∑ i, ∑ f, ∑ j, O (i, e) (j, f) * rho (j, f) (i, e) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem bodyInverse_trace (t : ι) (angle : ℝ) (nonzero : Real.cos angle ≠ 0)
    (O rho : Matrix (ι × κ) (ι × κ) ℂ) :
    (bodyInverse t (Real.cos angle) (Real.sin angle) O *
      BodyKernel.bodyExchange rho (Spectrum.basisPure t) angle).trace = (O * rho).trace := by
  rw [trace_pair_slices, trace_pair_slices]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  rw [bodyInverse_slice, BodyKernel.bodyExchange_slice, ← dual_trace,
    dual_inverse t _ _ (Real.cos_sq_add_sin_sq angle) nonzero]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.BasisInverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
