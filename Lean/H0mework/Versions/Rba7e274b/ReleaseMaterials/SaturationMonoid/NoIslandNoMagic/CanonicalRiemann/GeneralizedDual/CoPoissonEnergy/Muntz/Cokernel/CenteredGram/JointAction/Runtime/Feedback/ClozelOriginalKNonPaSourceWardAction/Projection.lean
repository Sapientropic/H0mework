import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Character

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNonPaSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance nonPaProjectionSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half




open OriginalKWholePaSourceRankAction
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

/-- The actual nonPa source is a dependent complement of the same complete source. Its physical projection is exactly the old Q source. -/
theorem actual_nonPa_source_physical (h : ℝ) :
    P (actualNonPaSource observation nontrivial half h) =
      Q (OriginalKFullSourceRResponse.completeSource observation nontrivial half h) := by
  let source := OriginalKFullSourceRResponse.completeSource observation nontrivial half h
  have pa := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (P source)
  have paP : P (actualWholePaSource observation nontrivial half h : BurnolL2) =
      actualWholePaSource observation nontrivial half h :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  unfold actualNonPaSource
  rw [map_sub,paP]
  change P source - E source = Q source
  change E source + Q source = P source at pa
  linear_combination (norm := module) -pa

/-- The Pa-orthogonal boundary forcing was already generated from the original source. No generic right trace is supplied. -/
theorem actual_nonPa_source_boundary_forcing (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    P (actualNonPaSource observation nontrivial half h) =
      (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) •
        OriginalKPairedResponseGramAction.originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded -
      (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
        (pairedMellinTranslationCharacter observation.coordinate h - pairedMellinTranslationCharacter (star observation.coordinate) h)) •
        burnolCompletedMellinRieszVector c := by
  rw [actual_nonPa_source_physical]
  exact OriginalKPairedResponseGramAction.actual_original_boundary_forcing observation nontrivial half h nonnegative bounded

/-- The source's original Fourier sibling is projected after the actual raw action. -/
theorem actual_nonPa_source_fourier (h : ℝ) :
    P (fourierL2 (actualNonPaSource observation nontrivial half h)) =
      Fphysical (Q (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) := by
  have source : P (fourierL2 (actualNonPaSource observation nontrivial half h)) =
      Fphysical (P (actualNonPaSource observation nontrivial half h)) := by
    apply Subtype.ext
    exact (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius _).symm
  rw [source,actual_nonPa_source_physical]

/-- The same actual source complement is invisible to Pa; this does not grant the whole complement physical membership. -/
theorem actual_nonPa_source_Pa_zero (h : ℝ) :
    E (actualNonPaSource observation nontrivial half h) = 0 := by
  unfold actualNonPaSource actualWholePaSource
  rw [map_sub,OriginalKCombCofinalPaAction.E_retract,sub_self]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNonPaSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
