import H0mework.Arithmetic.RiemannSpectral.ClozelBurnolOwnerGeneratedPhysicalReceiptOccurrence

/-! # Direct consumer of the theta--Burnol common-action receipt -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open RootedAccountedUnfolding AllPlaceOriginDefect
open scoped SchwartzMap

noncomputable section

/-- One root exposes the theta cofinal fold, owner action naturality, annulus
generation, action-determined additive state, and nonzero Fourier-fixed state.
-/
theorem generatedBurnolThetaCommonActionReceipt_directConsumer :
    let generated := generatedBurnolThetaCommonActionReceiptOccurrence.root
    generated.1 = generatedRiemannAnalyticContinuationOccurrence.root ∧
      generated.2.action = ownerArithmeticCounterterm generated.1.1 ∧
      (∀ test, generated.2.action test = clozelTemperedRemainder test) ∧
      (∀ (t : ℝ), 0 < t →
        generated.1.2.thetaPair.pair.f t =
          ((∑' stage,
            generatedRiemannThetaTerm generated.1.1 t stage : ℝ) : ℂ)) ∧
      GaussianActionCommutingAt generated.2.action
        generated.1.2.thetaPair.pair ∧
      (∀ (t : ℝ) (positive : 0 < t),
        generated.2.action
            (ClozelEndpointSourceEffect.scaledSchwartzTest t⁻¹
              (inv_ne_zero positive.ne') burnolEvenAnnulusSchwartz) =
          (((2 * t : ℝ) : ℂ) * burnolAdditiveCoSum t)) ∧
      (generated.2.additiveState : BurnolL2) ≠ 0 ∧
      generated.2.fixedState.1 = (1 / 2 : ℂ) •
        (generated.2.additiveState +
          evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            generated.2.additiveState) ∧
      generated.2.fixedState ≠ 0 := by
  let generated := generatedBurnolThetaCommonActionReceiptOccurrence.root
  refine ⟨rfl, generated.2.action_eq, generated.2.action_naturality,
    generated.2.thetaFoldRead, generated.2.gaussianActionRead,
    generated.2.annulusActionRead, generated.2.additiveState_ne_zero,
    generated.2.fixedState_generated, generated.2.fixedState_ne_zero⟩

/-- Direct hostile consumer: a changed positive theta coordinate cannot be
silently attached to the same owner action. -/
theorem generatedBurnolThetaCommonActionReceipt_changedTheta_hostile
    (replacement : WeakFEPair ℂ) {t : ℝ} (positive : 0 < t)
    (changed : replacement.f t ≠
      generatedBurnolThetaCommonActionReceiptOccurrence.root.1.2.thetaPair.pair.f t) :
    ¬ GaussianActionCommutingAt
      generatedBurnolThetaCommonActionReceiptOccurrence.root.2.action
      replacement :=
  GeneratedBurnolThetaCommonActionReceiptAt.changedThetaPair_cannot_commute
    generatedBurnolThetaCommonActionReceiptOccurrence.root.2 replacement
    positive changed

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
