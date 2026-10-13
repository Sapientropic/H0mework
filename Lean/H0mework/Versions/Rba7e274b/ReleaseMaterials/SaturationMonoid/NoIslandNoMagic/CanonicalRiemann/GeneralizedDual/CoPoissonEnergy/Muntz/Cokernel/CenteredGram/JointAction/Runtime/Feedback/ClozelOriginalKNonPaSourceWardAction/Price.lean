import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Ward

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
local instance nonPaBoundaryPriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half





open OriginalKWholePaSourceRankAction
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

private theorem original_Fourier_Q_covariance (value : BurnolPaAmbientCarrier) :
    OP (Fphysical value) = Fphysical (OP value) :=
  (congrArg (fun result : SourceGeneratedHilbertCokernel.OrthogonalResidual
    burnolCompactCoPoissonLanding => (result : BurnolPaAmbientCarrier))
    (burnolCompactCoPoissonActionSquare.orthogonalAction_residual value)).symm

private theorem original_Q_boundary_reader (x y : BurnolL2) (b : BurnolPaAmbientCarrier) (factor : ℂ) :
    inner ℂ (P x) (factor • (OP b + Fphysical (OP b))) +
      inner ℂ (factor • (OP b - Fphysical (OP b))) (P y) =
    factor * (inner ℂ (Q x) b + inner ℂ (Fphysical (Q x)) b) +
      star factor * star (inner ℂ (Q y) b - inner ℂ (Fphysical (Q y)) b) := by
  rw [←original_Fourier_Q_covariance]
  have pair : inner ℂ (P x) (OP b + OP (Fphysical b)) = inner ℂ (Q x) (b+Fphysical b) := by
    rw [←map_add]
    exact (burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_starProjection_left_eq_right _ _).symm
  have sibling : inner ℂ (OP b - OP (Fphysical b)) (P y) = inner ℂ (b-Fphysical b) (Q y) := by
    rw [←map_sub]
    exact burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_starProjection_left_eq_right _ _
  simp only [inner_smul_left,inner_smul_right,starRingEnd_apply]
  rw [pair,sibling]
  simp only [inner_add_right,inner_sub_left]
  have pairF := OriginalRieszFiniteSynthesis.fourier_pairing b (Q x)
  have siblingF := OriginalRieszFiniteSynthesis.fourier_pairing b (Q y)
  have pairFright : inner ℂ (Q x) (Fphysical b) = inner ℂ (Fphysical (Q x)) b := by
    simpa only [Complex.star_def,inner_conj_symm] using congrArg star pairF
  rw [pairFright,siblingF]
  rw [←inner_conj_symm b (Q y), ←inner_conj_symm b (Fphysical (Q y))]
  simp only [star_sub,starRingEnd_apply]

def actualNonPaBoundarySourcePrice (h : ℝ) : ℂ :=
  let pair := Q (actualNonPaPairedR observation nontrivial half h)
  let sibling := Q (actualNonPaSiblingR observation nontrivial half h)
  let factor := 2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
  factor * (OriginalKBoundarySourceAction.actualBoundaryIntegralRead c pair h +
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c (Fphysical pair) h) +
  star factor * star (OriginalKBoundarySourceAction.actualBoundaryIntegralRead c sibling h -
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c (Fphysical sibling) h)

/-- Both nonPa-only boundary feet consume the existing whole correctedC source programme; all Cvel and two contact windows remain literal. -/
theorem actual_nonPa_boundary_source_price (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    actualNonPaBoundaryCross observation nontrivial half h nonnegative bounded =
      actualNonPaBoundarySourcePrice observation nontrivial half h := by
  unfold actualNonPaBoundaryCross OriginalKPairedResponseGramAction.originalGeneratedPaBoundary
  dsimp only
  rw [original_Q_boundary_reader]
  rw [OriginalKPairedResponseGramAction.BoundarySource.generated_boundary_realizes_original c observation.mathlibZero h nonnegative bounded]
  rw [OriginalKBoundarySourceAction.actual_boundary_integral_read c observation.mathlibZero,
    OriginalKBoundarySourceAction.actual_boundary_integral_read c observation.mathlibZero,
    OriginalKBoundarySourceAction.actual_boundary_integral_read c observation.mathlibZero,
    OriginalKBoundarySourceAction.actual_boundary_integral_read c observation.mathlibZero]
  rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNonPaSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
