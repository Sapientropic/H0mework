import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Source.Sieve
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.Residue

/-! The original source gap generates the exact finite prime-depleted inventory on every physical cutoff. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem prime_three_source_window_cover (X : ℝ) (K : ℕ) (covers : 4 * (X / Real.sqrt 3) ≤ K) :
    4 * (Real.sqrt 3 * X) ≤ (3 * K : ℕ) := by
  have positive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  rw [← mul_div_assoc] at covers
  have bound := (div_le_iff₀ positive).mp covers
  calc
    4 * (Real.sqrt 3 * X) = Real.sqrt 3 * (4 * X) := by ring
    _ ≤ Real.sqrt 3 * ((K : ℝ) * Real.sqrt 3) := mul_le_mul_of_nonneg_left bound positive.le
    _ = (3 * K : ℕ) := by push_cast; nlinarith [square]

theorem primeThreePhysicalResidue_finite_window
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (X : ℝ) (K : ℕ) (covers : 4 * (X / Real.sqrt 3) ≤ K) :
    (primeThreePhysicalResidue (p : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (symmetricInterval X)] fun x =>
        (Real.sqrt 3 : ℂ) * finitePrimeThreeSourceCoSum (burnolMobiusSourceL2 p) K x +
          ((Real.sqrt 3 : ℂ) - (Real.sqrt 3 : ℂ)⁻¹) *
            burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p := by
  have positive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have forward := (ae_restrict_iff' (measurableSet_symmetricInterval (Real.sqrt 3 * X))).mp
    (original_pa_finite_source_window p inside (Real.sqrt 3 * X) (3 * K)
      (prime_three_source_window_cover X K covers))
  have backward := (ae_restrict_iff' (measurableSet_symmetricInterval (X / Real.sqrt 3))).mp
    (original_pa_finite_source_window p inside (X / Real.sqrt 3) K covers)
  have forwardQmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := Real.sqrt 3) positive.ne'
  have backwardQmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := (Real.sqrt 3)⁻¹) (inv_ne_zero positive.ne')
  filter_upwards [ae_restrict_of_ae (primeThreePhysicalResidue_coeFn (p : BurnolL2)),
    ae_restrict_of_ae (forwardQmp.ae forward), ae_restrict_of_ae (backwardQmp.ae backward),
    ae_restrict_mem (measurableSet_symmetricInterval X)] with x physical forwardRead backwardRead window
  have bound : |x| ≤ X := abs_le.mpr window
  have forwardWindow : Real.sqrt 3 * x ∈ symmetricInterval (Real.sqrt 3 * X) := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos positive]
    exact mul_le_mul_of_nonneg_left bound positive.le
  have backwardWindow : (Real.sqrt 3)⁻¹ * x ∈ symmetricInterval (X / Real.sqrt 3) := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (inv_pos.mpr positive), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positive.le)
  have plus := forwardRead forwardWindow
  have minus := backwardRead backwardWindow
  simp only [smul_eq_mul, inv_mul_eq_div] at plus minus
  rw [physical, plus, minus]
  have sieve := finiteSourceCoSum_prime_three (burnolMobiusSourceL2 p : ℝ → ℂ) K x
  linear_combination sieve

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
