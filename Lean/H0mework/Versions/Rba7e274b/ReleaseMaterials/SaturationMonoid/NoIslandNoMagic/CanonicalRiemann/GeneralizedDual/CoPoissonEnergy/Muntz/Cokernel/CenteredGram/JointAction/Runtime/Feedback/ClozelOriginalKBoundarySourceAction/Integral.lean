import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Feet
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
local instance boundaryIntegralComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Source
export OriginalKConstantContactSourceAction.ConstantSource (value velocity seed)
end Source
local notation "P" => burnolEvenAmbientProjection


def actualCorrectedVelocityPrice (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) : ℂ :=
  (∫ t : ℝ in (0 : ℝ)..h, inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (Source.velocity coordinate))) +
  (∫ t : ℝ in (0 : ℝ)..(-h), inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (Source.velocity coordinate)))

/-- The original corrected full-vector source integral is read only after its complete source action is paid. -/
theorem actual_corrected_velocity_integral_price (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) :
    inner ℂ (test : BurnolL2) (actualCorrectedVelocityIntegral coordinate h) =
      actualCorrectedVelocityPrice coordinate test h := by
  unfold actualCorrectedVelocityIntegral actualCorrectedVelocityPrice
  rw [inner_add_right]
  have first : IntervalIntegrable (fun t : ℝ => burnolMultiplicativeDilation t (Source.velocity coordinate)) volume 0 h :=
    (burnolMultiplicativeDilation_stronglyContinuous (Source.velocity coordinate)).intervalIntegrable 0 h
  have second : IntervalIntegrable (fun t : ℝ => burnolMultiplicativeDilation t (Source.velocity coordinate)) volume 0 (-h) :=
    (burnolMultiplicativeDilation_stronglyContinuous (Source.velocity coordinate)).intervalIntegrable 0 (-h)
  exact congrArg₂ (fun x y : ℂ => x+y)
    ((innerSL ℂ (test : BurnolL2)).intervalIntegral_comp_comm first).symm
    ((innerSL ℂ (test : BurnolL2)).intervalIntegral_comp_comm second).symm

local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

def actualBoundaryIntegralRead (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) : ℂ :=
  (pairedMellinTranslationCharacter coordinate.value h - 1) * inner ℂ test (burnolCompletedMellinRieszVector coordinate) -
    (1 / 2 : ℂ) * actualCorrectedVelocityPrice coordinate test h -
    OriginalRieszSource.Kernel.A coordinate * actualSeedWindowPrice test h +
    OriginalRieszSource.Kernel.beta coordinate * actualSeedWindowPrice (Fphysical test) h

/-- Whole B is priced by the exact literal source velocity integrals and both moving contact windows. -/
theorem actual_boundary_integral_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (test : BurnolPaAmbientCarrier) (h : ℝ) :
    inner ℂ test (burnolZeroPairedFixedAnnulusBoundary coordinate zero h) =
      actualBoundaryIntegralRead coordinate test h := by
  rw [actual_boundary_source_read]
  unfold actualBoundarySourceRead actualBoundaryIntegralRead
  rw [actual_corrected_velocity_integral_price]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
