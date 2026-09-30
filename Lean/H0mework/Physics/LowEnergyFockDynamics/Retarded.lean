import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Positive damping generates the causal Fourier boundary of the actual finite modes. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open MeasureTheory
open scoped BigOperators
noncomputable section

def retardedMode (E damping rate t : ℝ) : ℂ :=
  Complex.exp ((-(damping : ℂ)+Complex.I*((E-rate : ℝ) : ℂ))*(t : ℂ))

theorem retardedMode_integrable (E damping rate : ℝ) (positive : 0<damping) :
    IntegrableOn (retardedMode E damping rate) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simpa using neg_neg_of_pos positive

theorem retardedMode_transform (E damping rate : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Set.Ioi 0, retardedMode E damping rate t) =
      Complex.I / (((E-rate : ℝ) : ℂ)+Complex.I*(damping : ℂ)) := by
  unfold retardedMode
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos positive) 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have nonzero : ((E-rate : ℝ) : ℂ)+Complex.I*(damping : ℂ) ≠ 0 := by
    intro zero
    have imag := congrArg Complex.im zero
    simp at imag
    exact (ne_of_gt positive) imag
  have identity : -(damping : ℂ)+Complex.I*((E-rate : ℝ) : ℂ) =
      Complex.I*(((E-rate : ℝ) : ℂ)+Complex.I*(damping : ℂ)) := by
    simp only [mul_add,← mul_assoc,Complex.I_mul_I,neg_one_mul]
    ring
  rw [identity]
  field_simp
  simp

theorem finite_retarded_transform {ι : Type*} [Fintype ι]
    (coefficient : ι → ℂ) (rate : ι → ℝ) (E damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Set.Ioi 0, ∑ j, coefficient j*retardedMode E damping (rate j) t) =
      ∑ j, coefficient j*(Complex.I /
        (((E-rate j : ℝ) : ℂ)+Complex.I*(damping : ℂ))) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul,retardedMode_transform E damping (rate j) positive]
  · intro j _
    exact (retardedMode_integrable E damping (rate j) positive).const_mul (coefficient j)

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
