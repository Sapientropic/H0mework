import H0mework.Fock.HistoryConditional.GWordEnergy
import H0mework.Fock.HistoryConditional.VectorAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords SourceVectorMoment
open scoped InnerProductSpace
noncomputable section
universe u

private theorem affine_norm (a b : Nat) (x y : ℂ) :
    ‖(a : ℂ) * x + (b : ℂ) * y‖ ^ 2 =
      (a : ℝ) ^ 2 * ‖x‖ ^ 2 + (b : ℝ) ^ 2 * ‖y‖ ^ 2 +
        2 * (a : ℝ) * (b : ℝ) * (inner ℂ x y).re := by
  have paid := norm_add_sq (𝕜 := ℂ) ((a : ℂ) • x) ((b : ℂ) • y)
  simp only [norm_smul, inner_smul_left, inner_smul_right] at paid
  convert paid using 1 <;> simp [Complex.mul_re, mul_pow]
  ring

theorem energy_expanded (depth : Nat) (word : List (Fock.Letter depth))
    (value : SourceJointClockGraph.Carrier) :
    ‖effect depth word value‖ ^ 2 = ‖value‖ ^ 2 +
      (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 - 1) *
        ‖SourceJointClockGraph.clock value‖ ^ 2 +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℝ) ^ 2 * ‖massMap value‖ ^ 2 +
      2 * ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) *
        ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℝ) *
          (inner ℂ (SourceJointClockGraph.clock value) (massMap value)).re := by
  rw [energy, affine_norm]
  change ‖value‖ ^ 2 - ‖SourceJointClockGraph.clock value‖ ^ 2 +
    (_ * ‖SourceJointClockGraph.clock value‖ ^ 2 + _ * ‖massMap value‖ ^ 2 +
      _ * (inner ℂ (SourceJointClockGraph.clock value) (massMap value)).re) = _
  ring

variable {ι : Type u} [Fintype ι] (p : PMF ι)

theorem mean_effect (depth : Nat) (word : List (Fock.Letter depth))
    (value : ι → SourceJointClockGraph.Carrier) :
    mean p (effect depth word ∘ value) = effect depth word (mean p value) :=
  mean_map p (effect depth word).toLinearMap value

theorem variance_effect (depth : Nat) (word : List (Fock.Letter depth))
    (value : ι → SourceJointClockGraph.Carrier) :
    variance p (effect depth word ∘ value) = variance p value +
      (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 - 1) *
        variance p (SourceJointClockGraph.clock ∘ value) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℝ) ^ 2 * variance p (massMap ∘ value) +
      2 * ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) *
        ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℝ) * massClockCovariance p value := by
  have clock_mean : mean p (SourceJointClockGraph.clock ∘ value) = SourceJointClockGraph.clock (mean p value) :=
    mean_map p SourceJointClockGraph.clock.toLinearMap value
  calc
    variance p (effect depth word ∘ value) =
        ∑ i, (p i).toReal * ‖effect depth word (value i - mean p value)‖ ^ 2 := by
      simp only [variance, error, Function.comp_apply, mean_effect, map_sub]
    _ = _ := by
      simp_rw [energy_expanded]
      simp only [variance, error, massClockCovariance,
        clock_mean, mean_map, Function.comp_apply,
        map_sub, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem constant_mass_variance (depth : Nat) (word : List (Fock.Letter depth))
    (value : ι → SourceJointClockGraph.Carrier) (constant : ℂ)
    (source : ∀ i, massMap (value i) = constant) :
    variance p (effect depth word ∘ value) = variance p value +
      (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 - 1) *
        variance p (SourceJointClockGraph.clock ∘ value) := by
  rw [variance_effect]
  have mass : variance p (massMap ∘ value) = 0 := by
    simp only [variance, error, mean_map, mass_const p value constant source, Function.comp_apply,
      source, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
  have cross : massClockCovariance p value = 0 := by
    simp only [massClockCovariance, map_sub, mass_const p value constant source, source,
      sub_self, inner_zero_right, Complex.zero_re, mul_zero, Finset.sum_const_zero]
  rw [mass, cross]
  ring

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
