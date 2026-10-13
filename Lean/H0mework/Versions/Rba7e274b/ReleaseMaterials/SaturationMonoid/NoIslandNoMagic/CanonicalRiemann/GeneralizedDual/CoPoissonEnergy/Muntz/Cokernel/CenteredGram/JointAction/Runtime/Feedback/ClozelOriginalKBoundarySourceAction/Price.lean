import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Integral
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance boundaryPriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Source
export OriginalKConstantContactSourceAction.ConstantSource (value velocity seed)
end Source
local notation "P" => burnolEvenAmbientProjection


local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualFullBoundaryPairPrice (h : ℝ) : ℂ :=
  let acted := P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
  (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) *
    (actualBoundaryIntegralRead c acted h + actualBoundaryIntegralRead c (Fphysical acted) h)

def actualFullBoundarySiblingPrice (h : ℝ) : ℂ :=
  let acted := P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)
  star (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) *
    star (actualBoundaryIntegralRead c acted h - actualBoundaryIntegralRead c (Fphysical acted) h)

def actualFullBoundarySourcePrice (h : ℝ) : ℂ :=
  actualFullBoundaryPairPrice observation nontrivial half h +
    actualFullBoundarySiblingPrice observation nontrivial half h

/-- Both literal original full-P boundary cotests are paid by the same generated vector programme. -/
theorem actual_full_physical_boundary_source_price (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    OriginalKWholeWardSource.actualWholePhysicalBoundaryCross observation nontrivial half h nonnegative bounded =
      actualFullBoundarySourcePrice observation nontrivial half h := by
  unfold OriginalKWholeWardSource.actualWholePhysicalBoundaryCross actualFullBoundarySourcePrice
    actualFullBoundaryPairPrice actualFullBoundarySiblingPrice
  dsimp only
  rw [OriginalKPairedResponseGramAction.BoundarySource.generated_boundary_realizes_original c observation.mathlibZero h nonnegative bounded]
  simp only [inner_add_right, inner_sub_left, inner_smul_right, inner_smul_left, starRingEnd_apply]
  have pairF := OriginalRieszFiniteSynthesis.fourier_pairing
    (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero h)
    (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
  have siblingF := OriginalRieszFiniteSynthesis.fourier_pairing
    (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero h)
    (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
  have pairFright :
      inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
        (Fphysical (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero h)) =
      inner ℂ (Fphysical (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)))
        (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero h) := by
    simpa only [Complex.star_def, inner_conj_symm] using congrArg star pairF
  rw [pairFright, siblingF]
  rw [← inner_conj_symm (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero h)
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)),
    ← inner_conj_symm (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero h)
      (Fphysical (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)))]
  rw [actual_boundary_integral_read c observation.mathlibZero, actual_boundary_integral_read c observation.mathlibZero,
    actual_boundary_integral_read c observation.mathlibZero, actual_boundary_integral_read c observation.mathlibZero]
  simp only [star_sub, starRingEnd_apply]


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
