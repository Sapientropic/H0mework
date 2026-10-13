import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierSectorRGramSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierSectorRGramSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance sectorMatrixPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The same complete original K and F K material is acted on before diagonal or mixed price is read. -/
theorem actual_two_source_R_fields (coordinate : BurnolCompletedMellinCoordinate) :
 burnolDirectRightResolvent (coordinate.value/2) (actualPlusSource coordinate:BurnolL2)=
 burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2)+
 burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)) ∧
 burnolDirectRightResolvent (coordinate.value/2) (actualMinusSource coordinate:BurnolL2)=
 burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2)-
 burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)) :=by
 constructor
 · change burnolDirectRightResolventCLM coordinate ((K coordinate:BurnolL2)+fourierL2 (K coordinate:BurnolL2))=_
   rw [map_add]
   rfl
 · change burnolDirectRightResolventCLM coordinate ((K coordinate:BurnolL2)-fourierL2 (K coordinate:BurnolL2))=_
   rw [map_sub]
   rfl

def actualMixedLeft (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 inner ℂ (actualPlusSource coordinate:BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (actualMinusSource coordinate:BurnolL2))
def actualMixedRight (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 inner ℂ (actualMinusSource coordinate:BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (actualPlusSource coordinate:BurnolL2))

def actualKKPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 (actualPlusPrice coordinate+actualMinusPrice coordinate+actualMixedLeft coordinate+actualMixedRight coordinate)/4
def actualKFKPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 (actualPlusPrice coordinate-actualMinusPrice coordinate-actualMixedLeft coordinate+actualMixedRight coordinate)/4
def actualFKKPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 (actualPlusPrice coordinate-actualMinusPrice coordinate+actualMixedLeft coordinate-actualMixedRight coordinate)/4
def actualFKFKPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 (actualPlusPrice coordinate+actualMinusPrice coordinate-actualMixedLeft coordinate-actualMixedRight coordinate)/4

/-- The complete four original response feet consume the two generated complex diagonals and retain the actual mixed pair. -/
theorem actual_source_response_matrix (coordinate : BurnolCompletedMellinCoordinate) :
 inner ℂ (K coordinate:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))=actualKKPrice coordinate ∧
 inner ℂ (K coordinate:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)))=actualKFKPrice coordinate ∧
 inner ℂ (fourierL2 (K coordinate:BurnolL2)) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))=actualFKKPrice coordinate ∧
 inner ℂ (fourierL2 (K coordinate:BurnolL2)) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)))=actualFKFKPrice coordinate :=by
 have source:=actual_two_sector_R_prices coordinate
 have fields:=actual_two_source_R_fields coordinate
 have plus:=source.1
 have minus:=source.2
 rw [fields.1] at plus
 rw [fields.2] at minus
 change inner ℂ ((K coordinate:BurnolL2)+fourierL2 (K coordinate:BurnolL2)) _=_ at plus
 change inner ℂ ((K coordinate:BurnolL2)-fourierL2 (K coordinate:BurnolL2)) _=_ at minus
 simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right] at plus minus
 have mixedLeft:actualMixedLeft coordinate=
  inner ℂ (K coordinate:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))-
  inner ℂ (K coordinate:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)))+
  inner ℂ (fourierL2 (K coordinate:BurnolL2)) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))-
  inner ℂ (fourierL2 (K coordinate:BurnolL2)) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2))) :=by
  unfold actualMixedLeft
  rw [fields.2]
  change inner ℂ ((K coordinate:BurnolL2)+fourierL2 (K coordinate:BurnolL2)) _=_
  rw [inner_add_left,inner_sub_right,inner_sub_right]
  ring
 have mixedRight:actualMixedRight coordinate=
  inner ℂ (K coordinate:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))+
  inner ℂ (K coordinate:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)))-
  inner ℂ (fourierL2 (K coordinate:BurnolL2)) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))-
  inner ℂ (fourierL2 (K coordinate:BurnolL2)) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2))) :=by
  unfold actualMixedRight
  rw [fields.1]
  change inner ℂ ((K coordinate:BurnolL2)-fourierL2 (K coordinate:BurnolL2)) _=_
  rw [inner_sub_left,inner_add_right,inner_add_right]
  ring
 unfold actualKKPrice actualKFKPrice actualFKKPrice actualFKFKPrice
 rw [mixedLeft,mixedRight]
 constructor
 · linear_combination (plus+minus)/4
 constructor
 · linear_combination (plus-minus)/4
 constructor
 · linear_combination (plus-minus)/4
 · linear_combination (plus+minus)/4

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierSectorRGramSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
