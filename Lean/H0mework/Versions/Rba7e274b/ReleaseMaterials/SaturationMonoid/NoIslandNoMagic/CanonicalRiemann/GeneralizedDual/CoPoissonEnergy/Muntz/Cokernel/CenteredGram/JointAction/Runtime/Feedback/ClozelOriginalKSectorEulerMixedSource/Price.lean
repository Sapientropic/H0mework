import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Mixed
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierSectorRGramSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance sectorPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualKKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (Sector.actualPlusPrice c+Sector.actualMinusPrice c+actualMixedLeftPrice c+actualMixedRightPrice c)/4
def actualKFKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (Sector.actualPlusPrice c-Sector.actualMinusPrice c-actualMixedLeftPrice c+actualMixedRightPrice c)/4
def actualFKKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (Sector.actualPlusPrice c-Sector.actualMinusPrice c+actualMixedLeftPrice c-actualMixedRightPrice c)/4
def actualFKFKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (Sector.actualPlusPrice c+Sector.actualMinusPrice c-actualMixedLeftPrice c-actualMixedRightPrice c)/4

/-- All four original response feet now consume both actual source-generated mixed laws. -/
theorem actual_coupled_source_response_matrix (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c:BurnolL2) (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2))=actualKKPrice c ∧
 inner ℂ (K c:BurnolL2) (burnolDirectRightResolvent (c.value/2) (fourierL2 (K c:BurnolL2)))=actualKFKPrice c ∧
 inner ℂ (fourierL2 (K c:BurnolL2)) (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2))=actualFKKPrice c ∧
 inner ℂ (fourierL2 (K c:BurnolL2)) (burnolDirectRightResolvent (c.value/2) (fourierL2 (K c:BurnolL2)))=actualFKFKPrice c :=by
 have source:=OriginalKFourierSectorRGramSource.actual_source_response_matrix c
 have generated:=actual_two_mixed_R_source_prices c
 unfold OriginalKFourierSectorRGramSource.actualKKPrice OriginalKFourierSectorRGramSource.actualKFKPrice
  OriginalKFourierSectorRGramSource.actualFKKPrice OriginalKFourierSectorRGramSource.actualFKFKPrice at source
 rw [generated.1,generated.2] at source
 exact source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualCoupledKMeanPrice (h : ℝ) : ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 OriginalKFourierSectorRGramSource.actualCommonInputStock c h (K c)+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h*actualKKPrice c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h*actualKFKPrice c

def actualCoupledFKMeanPrice (h : ℝ) : ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 OriginalKFourierSectorRGramSource.actualCommonInputStock c h (Fphysical (K c))+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h*actualFKKPrice c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h*actualFKFKPrice c

/-- Complete original M consumes the generated coupled responses on its own K/F K feet. -/
theorem actual_coupled_complete_M_prices (h : ℝ) :
 OriginalKFourierSectorRGramSource.actualSectorKMeanPrice observation nontrivial half h=actualCoupledKMeanPrice observation nontrivial half h ∧
 OriginalKFourierSectorRGramSource.actualSectorFKMeanPrice observation nontrivial half h=actualCoupledFKMeanPrice observation nontrivial half h :=by
 have generated:=actual_two_mixed_R_source_prices (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 unfold OriginalKFourierSectorRGramSource.actualSectorKMeanPrice OriginalKFourierSectorRGramSource.actualSectorFKMeanPrice
  OriginalKFourierSectorRGramSource.actualKKPrice OriginalKFourierSectorRGramSource.actualKFKPrice
  OriginalKFourierSectorRGramSource.actualFKKPrice OriginalKFourierSectorRGramSource.actualFKFKPrice
 unfold actualCoupledKMeanPrice actualCoupledFKMeanPrice actualKKPrice actualKFKPrice actualFKKPrice actualFKFKPrice
 dsimp only
 rw [generated.1,generated.2]
 exact ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
