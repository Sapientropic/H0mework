import H0mework.Arithmetic.Mellin.TateInvolution

/-!
# Log-quarter transform of the positive Mellin carrier

The canonical chart

`f(t) ↦ exp(x / 4) * f(exp x)`

turns the weight-`1/2` Tate involution into reflection and the normalized
positive dilation `a^(1/4) D_a` into translation by `log a`.  These are
pointwise identities on the actual positive Mellin function carrier; no
Hilbert completion or bounded Mellin functional is assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex

noncomputable section

def positiveMellinLogQuarterTransform :
    ClozelPositiveMellinFunction →ₗ[ℂ] (ℝ → ℂ) where
  toFun f x := (Real.exp (x / 4) : ℂ) *
    f ⟨Real.exp x, Real.exp_pos x⟩
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem positiveMellinLogQuarterTransform_injective :
    Function.Injective positiveMellinLogQuarterTransform := by
  intro f g equality
  funext t
  have evaluated := congrFun equality (Real.log t.1)
  change
    (Real.exp (Real.log t.1 / 4) : ℂ) *
        f ⟨Real.exp (Real.log t.1), Real.exp_pos _⟩ =
      (Real.exp (Real.log t.1 / 4) : ℂ) *
        g ⟨Real.exp (Real.log t.1), Real.exp_pos _⟩ at evaluated
  have inputEq :
      (⟨Real.exp (Real.log t.1), Real.exp_pos _⟩ :
        PositiveMellinReal) = t := by
    apply Subtype.ext
    exact Real.exp_log t.2
  rw [inputEq] at evaluated
  exact mul_left_cancel₀ (ofReal_ne_zero.mpr (Real.exp_ne_zero _)) evaluated

theorem complexExp_cpow_neg_half (x : ℝ) :
    (Real.exp x : ℂ) ^ (-(1 / 2 : ℂ)) =
      (Real.exp (-x / 2) : ℂ) := by
  calc
    _ = ((Real.exp x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos x).le
        (-(1 / 2 : ℝ)) using 1
      all_goals norm_num
    _ = (Real.exp (-x / 2) : ℂ) := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
      congr 1
      ring

theorem positiveMellinLogQuarterTransform_tate
    (f : ClozelPositiveMellinFunction) (x : ℝ) :
    positiveMellinLogQuarterTransform (positiveTateInvolution f) x =
      positiveMellinLogQuarterTransform f (-x) := by
  change
    (Real.exp (x / 4) : ℂ) *
        ((Real.exp x : ℂ) ^ (-(1 / 2 : ℂ)) *
          f ⟨(Real.exp x)⁻¹, inv_pos.mpr (Real.exp_pos x)⟩) =
      (Real.exp (-x / 4) : ℂ) *
        f ⟨Real.exp (-x), Real.exp_pos (-x)⟩
  rw [complexExp_cpow_neg_half]
  have inputEq :
      (⟨(Real.exp x)⁻¹, inv_pos.mpr (Real.exp_pos x)⟩ :
        PositiveMellinReal) =
        ⟨Real.exp (-x), Real.exp_pos (-x)⟩ := by
    apply Subtype.ext
    exact (Real.exp_neg x).symm
  rw [inputEq, ← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 2
  ring

def positiveMellinRawDilation
    (a : ℝ) (positive : 0 < a) :
    ClozelPositiveMellinFunction →ₗ[ℂ]
      ClozelPositiveMellinFunction where
  toFun f t := f ⟨a * t.1, mul_pos positive t.2⟩
  map_add' f g := by
    funext t
    simp
  map_smul' c f := by
    funext t
    simp

def positiveMellinQuarterDilationWeight (a : ℝ) : ℂ :=
  Real.exp (Real.log a / 4)

def positiveMellinQuarterNormalizedDilation
    (a : ℝ) (positive : 0 < a) :
    ClozelPositiveMellinFunction →ₗ[ℂ]
      ClozelPositiveMellinFunction :=
  positiveMellinQuarterDilationWeight a •
    positiveMellinRawDilation a positive

theorem positiveMellinQuarterDilationWeight_ne_zero
    (a : ℝ) : positiveMellinQuarterDilationWeight a ≠ 0 := by
  exact ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem positiveMellinLogQuarterTransform_normalizedDilation
    (a : ℝ) (positive : 0 < a)
    (f : ClozelPositiveMellinFunction) (x : ℝ) :
    positiveMellinLogQuarterTransform
        (positiveMellinQuarterNormalizedDilation a positive f) x =
      positiveMellinLogQuarterTransform f (x + Real.log a) := by
  change
    (Real.exp (x / 4) : ℂ) *
        ((Real.exp (Real.log a / 4) : ℂ) *
          f ⟨a * Real.exp x, mul_pos positive (Real.exp_pos x)⟩) =
      (Real.exp ((x + Real.log a) / 4) : ℂ) *
        f ⟨Real.exp (x + Real.log a), Real.exp_pos _⟩
  have inputEq :
      (⟨a * Real.exp x, mul_pos positive (Real.exp_pos x)⟩ :
        PositiveMellinReal) =
        ⟨Real.exp (x + Real.log a), Real.exp_pos _⟩ := by
    apply Subtype.ext
    change a * Real.exp x = Real.exp (x + Real.log a)
    rw [Real.exp_add, Real.exp_log positive]
    ring
  rw [inputEq, ← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem positiveMellinQuarterNormalizedDilation_comp
    (a b : ℝ) (aPositive : 0 < a) (bPositive : 0 < b) :
    (positiveMellinQuarterNormalizedDilation a aPositive).comp
        (positiveMellinQuarterNormalizedDilation b bPositive) =
      positiveMellinQuarterNormalizedDilation (b * a)
        (mul_pos bPositive aPositive) := by
  apply LinearMap.ext
  intro f
  apply positiveMellinLogQuarterTransform_injective
  funext x
  rw [LinearMap.comp_apply,
    positiveMellinLogQuarterTransform_normalizedDilation,
    positiveMellinLogQuarterTransform_normalizedDilation,
    positiveMellinLogQuarterTransform_normalizedDilation]
  rw [Real.log_mul bPositive.ne' aPositive.ne']
  ring

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
