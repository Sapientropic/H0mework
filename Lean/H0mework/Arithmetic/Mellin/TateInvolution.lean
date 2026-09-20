import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import H0mework.Arithmetic.Mellin.PositiveDomain

/-!
# Narrow Tate involution on positive Mellin functions

This module owns only the function-level weight-`1/2` involution and its
involutivity.  Convergence, Gaussian, q-rich, endpoint, and zero-occurrence
consumers live above this firewall.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex

noncomputable section

def positiveTateInvolution :
    ClozelPositiveMellinFunction →ₗ[ℂ]
      ClozelPositiveMellinFunction where
  toFun f t :=
    (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      f ⟨t.1⁻¹, inv_pos.mpr t.2⟩
  map_add' := by
    intro f g
    funext t
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro c f
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem positiveHalfWeights_mul_eq_one (t : PositiveMellinReal) :
    (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
        ((t.1⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
  have tNe : (t.1 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr t.2.ne'
  have reciprocalCpow :
      ((t.1⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
        (t.1 : ℂ) ^ (1 / 2 : ℂ) := by
    calc
      _ = (((t.1⁻¹ : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        symm
        convert Complex.ofReal_cpow (inv_nonneg.mpr t.2.le)
          (-(1 / 2 : ℝ)) using 1
        all_goals norm_num
      _ = ((t.1 ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        congr 1
        rw [Real.rpow_neg_eq_inv_rpow, inv_inv]
      _ = _ := by
        convert Complex.ofReal_cpow t.2.le (1 / 2 : ℝ) using 1
        all_goals norm_num
  rw [reciprocalCpow, Complex.cpow_neg]
  exact inv_mul_cancel₀ <| cpow_ne_zero_iff.mpr (Or.inl tNe)

theorem positiveTateInvolution_involutive
    (f : ClozelPositiveMellinFunction) :
    positiveTateInvolution (positiveTateInvolution f) = f := by
  funext t
  change (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((t.1⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        f ⟨(t.1⁻¹)⁻¹, inv_pos.mpr (inv_pos.mpr t.2)⟩) = f t
  rw [← mul_assoc, positiveHalfWeights_mul_eq_one, one_mul]
  congr 1
  exact Subtype.ext (inv_inv t.1)

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
