import H0mework.Versions.Y.Arithmetic.Mellin.PositiveMellinCarrier
import H0mework.Versions.Y.Arithmetic.Mellin.PositiveMellinGaussianTate
import H0mework.Arithmetic.Mellin.TateInvolution

/-!
# Tate involution on the positive Mellin carrier

The weight-`1/2` Tate involution is a literal linear involution on functions
over `Ioi 0`.  It transports convergence from `1/2-z` to `z`, intertwines
Mellin functionals, fixes the generated Gaussian remainder relation, and
conjugates a positive dilation to inverse dilation with the exact half-weight.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set

noncomputable section

def positiveMellinTateMap (z : ℂ) :
    positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z) →ₗ[ℂ]
      positiveMellinConvergentSubmodule z where
  toFun f :=
    ⟨positiveTateInvolution f.1, by
      have rpowInverted : MellinConvergent
          (fun t => positiveMellinExtension f.1 (t ^ (-1 : ℝ)))
          (z - (1 / 2 : ℂ)) := by
        have source : MellinConvergent
            (positiveMellinExtension f.1) ((1 / 2 : ℂ) - z) := f.2
        rw [MellinConvergent.comp_rpow (a := (-1 : ℝ)) (by norm_num)]
        convert source using 1
        norm_num
        ring
      have inverted : MellinConvergent
          (fun t => positiveMellinExtension f.1 t⁻¹)
          (z - (1 / 2 : ℂ)) := by
        unfold MellinConvergent at rpowInverted ⊢
        apply rpowInverted.congr_fun
        · intro t ht
          change 0 < t at ht
          simp only [Real.rpow_neg_one]
        · exact measurableSet_Ioi
      have weighted : MellinConvergent
          (fun t => (t : ℂ) ^ (-(1 / 2 : ℂ)) •
            positiveMellinExtension f.1 t⁻¹) z := by
        rw [MellinConvergent.cpow_smul]
        convert inverted using 1
        ring
      change MellinConvergent
        (positiveMellinExtension (positiveTateInvolution f.1)) z
      unfold MellinConvergent at weighted ⊢
      apply weighted.congr_fun
      · intro t ht
        change 0 < t at ht
        simp [positiveMellinExtension, positiveTateInvolution,
          ht, inv_pos.mpr ht, smul_eq_mul]
      · exact measurableSet_Ioi⟩
  map_add' f g := by
    apply Subtype.ext
    exact positiveTateInvolution.map_add f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact positiveTateInvolution.map_smul c f.1

theorem positiveMellinFunctional_tateMap
    (z : ℂ)
    (f : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z)) :
    positiveMellinFunctional z (positiveMellinTateMap z f) =
      positiveMellinFunctional ((1 / 2 : ℂ) - z) f := by
  unfold positiveMellinFunctional positiveMellinTateMap
  change mellin
      (positiveMellinExtension (positiveTateInvolution f.1)) z =
    mellin (positiveMellinExtension f.1) ((1 / 2 : ℂ) - z)
  calc
    _ = mellin
        (fun t => (t : ℂ) ^ (-(1 / 2 : ℂ)) •
          positiveMellinExtension f.1 t⁻¹) z := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      simp [positiveMellinExtension, positiveTateInvolution,
        ht, inv_pos.mpr ht, smul_eq_mul]
    _ = mellin (fun t => positiveMellinExtension f.1 t⁻¹)
        (z - (1 / 2 : ℂ)) := by
      rw [mellin_cpow_smul]
      congr 2
    _ = mellin (positiveMellinExtension f.1)
        (-(z - (1 / 2 : ℂ))) :=
      mellin_comp_inv (positiveMellinExtension f.1)
        (z - (1 / 2 : ℂ))
    _ = _ := by
      congr 2
      ring

def positiveClozelMellinRelation
    (owner : GlobalGermOwner) (z : ℂ)
    (convergent :
      MellinConvergent
        (generatedClozelGaussianRemainderKernel owner) z) :
    positiveMellinConvergentSubmodule z :=
  restrictPositiveMellin z
    ⟨generatedClozelGaussianRemainderKernel owner, convergent⟩

theorem positiveMellinTateMap_clozelRelation
    (owner : GlobalGermOwner) (z : ℂ)
    (sourceConvergent : MellinConvergent
      (generatedClozelGaussianRemainderKernel owner)
      ((1 / 2 : ℂ) - z))
    (targetConvergent : MellinConvergent
      (generatedClozelGaussianRemainderKernel owner) z) :
    positiveMellinTateMap z
        (positiveClozelMellinRelation owner
          ((1 / 2 : ℂ) - z) sourceConvergent) =
      positiveClozelMellinRelation owner z targetConvergent := by
  apply Subtype.ext
  exact positiveTateInvolution_clozelRelation owner

theorem positiveHalfWeight_dilation
    (a t : PositiveMellinReal) :
    (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) =
      (a.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
        ((t.1 / a.1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have tCast :
      (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) =
        ((t.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_cpow t.2.le (-(1 / 2 : ℝ)) using 1
    all_goals norm_num
  have aCast :
      (a.1 : ℂ) ^ (-(1 / 2 : ℂ)) =
        ((a.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_cpow a.2.le (-(1 / 2 : ℝ)) using 1
    all_goals norm_num
  have divCast :
      ((t.1 / a.1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
        (((t.1 / a.1) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_cpow (div_nonneg t.2.le a.2.le)
      (-(1 / 2 : ℝ)) using 1
    all_goals norm_num
  rw [tCast, aCast, divCast,
    ← ofReal_mul, ofReal_inj, Real.div_rpow t.2.le a.2.le]
  have weightNe : a.1 ^ (-(1 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos a.2 _).ne'
  field_simp [weightNe]

theorem positiveMellinTateMap_dilation
    (z : ℂ) (a : ℝ) (aPositive : 0 < a)
    (f : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z)) :
    positiveMellinTateMap z
        (positiveMellinDilation ((1 / 2 : ℂ) - z)
          a aPositive f) =
      (a : ℂ) ^ (-(1 / 2 : ℂ)) •
        positiveMellinDilation z a⁻¹ (inv_pos.mpr aPositive)
          (positiveMellinTateMap z f) := by
  apply Subtype.ext
  funext t
  change (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      f.1 ⟨a * t.1⁻¹, _⟩ =
    (a : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((a⁻¹ * t.1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        f.1 ⟨(a⁻¹ * t.1)⁻¹, _⟩)
  have inputEq :
      (⟨(a⁻¹ * t.1)⁻¹,
        inv_pos.mpr (mul_pos (inv_pos.mpr aPositive) t.2)⟩ :
          PositiveMellinReal) =
        ⟨a * t.1⁻¹, mul_pos aPositive (inv_pos.mpr t.2)⟩ := by
    apply Subtype.ext
    field_simp [aPositive.ne', t.2.ne']
  rw [inputEq]
  have baseEq : a⁻¹ * t.1 = t.1 / a := by
    field_simp [aPositive.ne']
  rw [baseEq]
  rw [positiveHalfWeight_dilation ⟨a, aPositive⟩ t]
  ring

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
