import H0mework.Arithmetic.SonineSource.StageZeroSonineDilation
import H0mework.Arithmetic.RiemannSpectral.ClozelBurnolThetaCommonActionReceiptConsumer

/-!
# Burnol physical-action dependent face

The certified theta--Burnol common-action receipt supplies the occupied
Fourier-fixed state.  This file evaluates the true multiplicative compression
at the already generated first Sonine scale.  It creates no second occurrence
and contains no spectral coordinate or zero event.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open scoped InnerProductSpace

noncomputable section

abbrev BurnolPhysicalActionCarrier :=
  EvenBurnolFourierFixedCarrier burnolUnscaledCommonGapRadius

/-- The occupied state is read literally from the common-action receipt. -/
def burnolPhysicalActionState : BurnolPhysicalActionCarrier :=
  generatedBurnolThetaCommonActionReceiptOccurrence.root.2.fixedState

theorem burnolPhysicalActionState_generated :
    (burnolPhysicalActionState :
      EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) =
      (1 / 2 : ℂ) •
        (generatedBurnolThetaCommonActionReceiptOccurrence.root.2.additiveState +
          evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            generatedBurnolThetaCommonActionReceiptOccurrence.root.2.additiveState) :=
  generatedBurnolThetaCommonActionReceiptOccurrence.root.2.fixedState_generated

theorem burnolPhysicalActionState_ne_zero :
    burnolPhysicalActionState ≠ 0 :=
  generatedBurnolThetaCommonActionReceiptOccurrence.root.2.fixedState_ne_zero

/-- True multiplicative compression at the source-owned common gap and the
first generated q-rich scale. -/
def burnolPhysicalActionCompression :
    BurnolPhysicalActionCarrier →L[ℂ] BurnolPhysicalActionCarrier :=
  evenBurnolFourierFixedCompression burnolUnscaledCommonGapRadius
    (Real.log stageZeroSonineQ)

theorem burnolPhysicalActionCompression_symmetric
    (left right : BurnolPhysicalActionCarrier) :
    inner ℂ (burnolPhysicalActionCompression left) right =
      inner ℂ left (burnolPhysicalActionCompression right) :=
  evenBurnolFourierFixedCompression_symmetric
    burnolUnscaledCommonGapRadius (Real.log stageZeroSonineQ) left right

theorem burnolPhysicalActionCompression_contractive
    (state : BurnolPhysicalActionCarrier) :
    ‖burnolPhysicalActionCompression state‖ ≤ ‖state‖ :=
  evenBurnolFourierFixedCompression_contractive
    burnolUnscaledCommonGapRadius (Real.log stageZeroSonineQ) state

theorem burnolPhysicalAction_shift_ne_zero :
    Real.log stageZeroSonineQ ≠ 0 := by
  apply (Real.log_pos ?_).ne'
  have square : stageZeroSonineQ ^ 2 = 3 := by
    unfold stageZeroSonineQ
    rw [sq, Real.mul_self_sqrt]
    norm_num
  have nonnegative : 0 ≤ stageZeroSonineQ := Real.sqrt_nonneg _
  nlinarith

/-- Direct provenance/physics consumer. -/
theorem burnolPhysicalActionFace_directConsumer :
    generatedBurnolThetaCommonActionReceiptOccurrence.map Sigma.fst =
        generatedRiemannAnalyticContinuationOccurrence ∧
      burnolPhysicalActionState ≠ 0 ∧
      (∀ left right,
        inner ℂ (burnolPhysicalActionCompression left) right =
          inner ℂ left (burnolPhysicalActionCompression right)) ∧
      (∀ state, ‖burnolPhysicalActionCompression state‖ ≤ ‖state‖) :=
  ⟨generatedBurnolThetaCommonActionReceiptOccurrence_projects,
    burnolPhysicalActionState_ne_zero,
    burnolPhysicalActionCompression_symmetric,
    burnolPhysicalActionCompression_contractive⟩

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
