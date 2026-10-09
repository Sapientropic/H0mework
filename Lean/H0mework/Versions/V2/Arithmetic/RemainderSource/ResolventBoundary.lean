import H0mework.Versions.V2.Arithmetic.RemainderSource.Continuity

/-! The actual source resolvent emits its full oriented finite boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolMultiplicativeDilation_add (left right : ℝ) (value : BurnolL2) :
    burnolMultiplicativeDilation left (burnolMultiplicativeDilation right value) =
      burnolMultiplicativeDilation (left + right) value := by
  apply DenseRange.induction_on (p := fun value : BurnolL2 =>
      burnolMultiplicativeDilation left (burnolMultiplicativeDilation right value) =
        burnolMultiplicativeDilation (left + right) value)
    (SchwartzMap.denseRange_toLpCLM (by norm_num : (2 : ENNReal) ≠ ⊤)) value
  · exact isClosed_eq ((burnolMultiplicativeDilation left).continuous.comp
      (burnolMultiplicativeDilation right).continuous)
      (burnolMultiplicativeDilation (left + right)).continuous
  · intro test
    simp only [SchwartzMap.toLpCLM_apply, burnolMultiplicativeDilation_schwartz]
    exact congrArg (fun source : SchwartzMap ℝ ℂ => source.toLp 2 volume)
      (LinearMap.congr_fun (coPoissonSchwartzEnergyTranslation_add left right) test)

private theorem directIntegrand_action (z : ℂ) (value : BurnolL2) (base shift : ℝ) :
    burnolMultiplicativeDilation (-shift / 2)
        (burnolDirectRightResolventIntegrand z value base) =
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolDirectRightResolventIntegrand z value (base + shift) := by
  unfold burnolDirectRightResolventIntegrand
  rw [map_smul, burnolMultiplicativeDilation_add]
  have parameter : -shift / 2 + -base / 2 = -(base + shift) / 2 := by ring
  rw [parameter, smul_smul]
  exact congrArg (fun scalar : ℂ => scalar •
    burnolMultiplicativeDilation (-(base + shift) / 2) value)
      (positiveMellinQuarterRightResolventCharacter_mul_weight_add z base shift).symm

private theorem directIntegrand_tailShift (z : ℂ) (value : BurnolL2) (shift : ℝ) :
    (∫ base : ℝ in Ioi 0, burnolDirectRightResolventIntegrand z value (base + shift)) =
      ∫ base : ℝ in Ioi shift, burnolDirectRightResolventIntegrand z value base := by
  let integrand := burnolDirectRightResolventIntegrand z value
  have translated := (measurePreserving_add_left (volume : Measure ℝ) shift).integral_comp
    (Homeomorph.addLeft shift).measurableEmbedding ((Ioi shift).indicator integrand)
  rw [integral_indicator measurableSet_Ioi] at translated
  calc
    _ = ∫ base : ℝ, (Ioi shift).indicator integrand (shift + base) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with base
      by_cases positive : 0 < base
      · have shifted : shift < shift + base := by linarith
        simp [positive, shifted, add_comm, integrand]
      · have shifted : ¬ shift < shift + base := by linarith
        simp [positive, shifted, integrand]
    _ = _ := translated

/-- Oriented finite source current emitted by the same orbit integral. -/
def burnolDirectRightResolventSignedBoundary (z : ℂ) (value : BurnolL2) (shift : ℝ) : BurnolL2 :=
  ∫ base : ℝ in (0 : ℝ)..shift, burnolDirectRightResolventIntegrand z value base

theorem burnolDirectRightResolvent_sourceBoundary (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : BurnolL2) (shift : ℝ) :
    burnolMultiplicativeDilation (-shift / 2) (burnolDirectRightResolvent z value) -
        positiveMellinQuarterRightResolventCharacter z shift •
          burnolDirectRightResolvent z value =
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolDirectRightResolventSignedBoundary z value shift := by
  let integrand := burnolDirectRightResolventIntegrand z value
  let character := positiveMellinQuarterRightResolventCharacter z shift
  have integrable := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value
  have continuous : Continuous integrand := by
    exact (positiveMellinQuarterRightResolventWeight_continuous z).smul
      ((burnolMultiplicativeDilation_stronglyContinuous value).comp (by fun_prop))
  have split : (∫ base : ℝ in Ioi 0, integrand base) =
      (∫ base : ℝ in (0 : ℝ)..shift, integrand base) +
        ∫ base : ℝ in Ioi shift, integrand base := by
    have native := intervalIntegral.integral_interval_add_Ioi'
      (continuous.intervalIntegrable shift 0) integrable
    rw [← native, intervalIntegral.integral_symm]
    module
  have transformed : (∫ base : ℝ in Ioi 0,
      burnolMultiplicativeDilation (-shift / 2) (integrand base)) =
      character • ∫ base : ℝ in Ioi shift, integrand base := by
    calc
      _ = ∫ base : ℝ in Ioi 0, character • integrand (base + shift) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro base _
        exact directIntegrand_action z value base shift
      _ = _ := by rw [integral_smul, directIntegrand_tailShift]
  unfold burnolDirectRightResolvent burnolDirectRightResolventSignedBoundary
  change burnolMultiplicativeDilation (-shift / 2) (-(∫ base : ℝ in Ioi 0, integrand base)) -
      character • (-(∫ base : ℝ in Ioi 0, integrand base)) =
    character • ∫ base : ℝ in (0 : ℝ)..shift, integrand base
  have mapped : burnolMultiplicativeDilation (-shift / 2)
      (∫ base : ℝ in Ioi 0, integrand base) =
        ∫ base : ℝ in Ioi 0, burnolMultiplicativeDilation (-shift / 2) (integrand base) :=
    (LinearIsometry.integral_comp_comm
      (burnolMultiplicativeDilation (-shift / 2)).toLinearIsometry integrand).symm
  rw [map_neg, mapped, transformed, split]
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
