import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRResponse.Forcing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRResponse
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance boundaryAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The literal original B/character debt receives the whole actual native
source update, rather than independent endpoint prices. -/
theorem actual_original_residual_update (h nextShift : ℝ) (nonnegative : 0≤h)
    (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    ((2*Full.upperSeedFactor nextShift) • OP (burnolZeroPairedFixedAnnulusBoundary
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) observation.mathlibZero nextShift)-
      (2*Full.upperSeedFactor nextShift*(pairedMellinTranslationCharacter observation.coordinate nextShift-
        pairedMellinTranslationCharacter (star observation.coordinate) nextShift)) •
        burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))-
    ((2*Full.upperSeedFactor h) • OP (burnolZeroPairedFixedAnnulusBoundary
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) observation.mathlibZero h)-
      (2*Full.upperSeedFactor h*(pairedMellinTranslationCharacter observation.coordinate h-
        pairedMellinTranslationCharacter (star observation.coordinate) h)) •
        burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))=
      Paid.Q (completeNativeUpdate observation nontrivial half h nextShift) := by
  rw [←actual_source_Q_boundary_residual observation nontrivial half nextShift (nonnegative.trans ordered) bounded,
    ←actual_source_Q_boundary_residual observation nontrivial half h nonnegative (ordered.trans bounded),
    ←map_sub,actual_complete_native_update observation nontrivial half h nextShift nonnegative ordered]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

