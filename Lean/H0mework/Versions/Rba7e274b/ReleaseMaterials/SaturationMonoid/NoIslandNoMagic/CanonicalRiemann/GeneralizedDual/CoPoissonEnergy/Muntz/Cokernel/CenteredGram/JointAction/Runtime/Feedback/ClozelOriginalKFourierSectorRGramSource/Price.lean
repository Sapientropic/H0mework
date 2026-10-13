import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierSectorRGramSource.Matrix
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
local instance sectorPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualCommonInputStock (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
 (left : BurnolPaAmbientCarrier) : ℂ:=
 let p:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x
 let f:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x
 let d:=OriginalKCommonGapKernelSource.actualCommonFirst coordinate
 let e:=OriginalKCommonGapKernelSource.actualCommonSecond coordinate
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant coordinate
 let Kself:=inner ℂ (left:BurnolL2) (K coordinate:BurnolL2)
 let Kcross:=inner ℂ (left:BurnolL2) (fourierL2 (K coordinate:BurnolL2))
 (p*((coordinate.value-1)⁻¹*2))*(d*Kself+e*Kcross-D*star (OriginalKGapProjectionEulerSource.Paid.actualMean (left:BurnolL2)))+
 (f*(coordinate.value⁻¹*2))*(e*Kself+d*Kcross-D*star (OriginalKGapProjectionEulerSource.Paid.actualMean
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left:BurnolL2)))

def actualFirstRWeight (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ:=
 let p:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x
 let f:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x
 (coordinate.value-star coordinate.value)*(p*(coordinate.value-1)⁻¹*OriginalKCommonGapKernelSource.actualCommonFirst coordinate+
  f*coordinate.value⁻¹*OriginalKCommonGapKernelSource.actualCommonSecond coordinate)

def actualSecondRWeight (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ:=
 let p:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x
 let f:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x
 (coordinate.value+star coordinate.value-1)*(p*(coordinate.value-1)⁻¹*OriginalKCommonGapKernelSource.actualCommonSecond coordinate+
  f*coordinate.value⁻¹*OriginalKCommonGapKernelSource.actualCommonFirst coordinate)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualSectorKMeanPrice (h : ℝ) : ℂ:=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 actualCommonInputStock coordinate h (K coordinate)+
 actualFirstRWeight coordinate h*actualKKPrice coordinate+
 actualSecondRWeight coordinate h*actualKFKPrice coordinate

def actualSectorFKMeanPrice (h : ℝ) : ℂ:=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 actualCommonInputStock coordinate h (Fphysical (K coordinate))+
 actualFirstRWeight coordinate h*actualFKKPrice coordinate+
 actualSecondRWeight coordinate h*actualFKFKPrice coordinate

/-- The actual original complete M prices consume both generated complex response diagonals and the retained mixed source feet. -/
theorem actual_sector_complete_M_prices (h : ℝ) :
 OriginalKCommonGapKernelSource.actualCommonKMeanPrice observation nontrivial half h=actualSectorKMeanPrice observation nontrivial half h ∧
 OriginalKCommonGapKernelSource.actualCommonFKMeanPrice observation nontrivial half h=actualSectorFKMeanPrice observation nontrivial half h :=by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have source:=actual_source_response_matrix coordinate
 have c:inner ℂ (Fphysical (K coordinate):BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))=actualFKKPrice coordinate:=source.2.2.1
 have d:inner ℂ (Fphysical (K coordinate):BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)))=actualFKFKPrice coordinate:=source.2.2.2
 constructor
 · unfold OriginalKCommonGapKernelSource.actualCommonKMeanPrice OriginalKCommonGapKernelSource.actualCommonMSourcePrice
   unfold actualSectorKMeanPrice actualCommonInputStock actualFirstRWeight actualSecondRWeight
   dsimp only
   rw [source.1,source.2.1]
 · unfold OriginalKCommonGapKernelSource.actualCommonFKMeanPrice OriginalKCommonGapKernelSource.actualCommonMSourcePrice
   unfold actualSectorFKMeanPrice actualCommonInputStock actualFirstRWeight actualSecondRWeight
   dsimp only
   rw [c,d]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierSectorRGramSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
