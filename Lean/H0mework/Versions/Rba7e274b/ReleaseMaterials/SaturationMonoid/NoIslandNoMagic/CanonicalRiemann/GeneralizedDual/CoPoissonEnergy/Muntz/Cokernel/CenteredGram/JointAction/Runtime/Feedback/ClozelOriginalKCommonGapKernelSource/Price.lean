import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCommonGapKernelSource.MSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "K" => burnolCompletedMellinRieszVector
local notation "E" => OriginalRieszSource.GapEuler.euler
local notation "FT" => (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
local instance commonPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- H's literal source stock is read only on the receiver's own original physical face. -/
theorem actual_common_field_input_price (coordinate : BurnolCompletedMellinCoordinate)
 (left : BurnolPaAmbientCarrier) :
 inner ℂ (left:BurnolL2) (actualCommonField coordinate)=
 actualCommonFirst coordinate*inner ℂ (left:BurnolL2) (K coordinate:BurnolL2)+
 actualCommonSecond coordinate*inner ℂ (left:BurnolL2) (fourierL2 (K coordinate:BurnolL2))-
 actualCommonDeterminant coordinate*star (OriginalKGapProjectionEulerSource.Paid.actualMean (left:BurnolL2)) :=by
 have read:inner ℂ (left:BurnolL2) (G:BurnolL2)=star (OriginalKGapProjectionEulerSource.Paid.actualMean (left:BurnolL2)) :=by
  rw [←inner_conj_symm,OriginalKGapProjectionEulerSource.actual_gap_physical_input_price]
  rfl
 unfold actualCommonField
 rw [inner_sub_right,inner_add_right,inner_smul_right,inner_smul_right,inner_smul_right,read]

/-- The Fourier H input retains the true opposite mean face, with no physical qualification of R left. -/
theorem actual_Fourier_common_field_input_price (coordinate : BurnolCompletedMellinCoordinate)
 (left : BurnolPaAmbientCarrier) :
 inner ℂ (left:BurnolL2) (actualFourierCommonField coordinate)=
 actualCommonSecond coordinate*inner ℂ (left:BurnolL2) (K coordinate:BurnolL2)+
 actualCommonFirst coordinate*inner ℂ (left:BurnolL2) (fourierL2 (K coordinate:BurnolL2))-
 actualCommonDeterminant coordinate*star (OriginalKGapProjectionEulerSource.Paid.actualMean
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left:BurnolL2)) :=by
 have Fourier:=OriginalKGapProjectionEulerSource.actual_source_fourier_input (G:BurnolL2) left
 rw [OriginalKGapProjectionEulerSource.actual_gap_physical_input_price] at Fourier
 have read:inner ℂ (left:BurnolL2) (fourierL2 (G:BurnolL2))=
  star (OriginalKGapProjectionEulerSource.Paid.actualMean (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left:BurnolL2)) :=by
  rw [←inner_conj_symm,Fourier]
  rfl
 rw [(actual_Fourier_common_inventory coordinate).1,inner_sub_right,inner_add_right,
  inner_smul_right,inner_smul_right,inner_smul_right,read]

def actualCommonMSourcePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
 (left : BurnolPaAmbientCarrier) : ℂ:=
 let p:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x
 let f:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x
 let d:=actualCommonFirst coordinate
 let e:=actualCommonSecond coordinate
 let D:=actualCommonDeterminant coordinate
 let Kself:=inner ℂ (left:BurnolL2) (K coordinate:BurnolL2)
 let Kcross:=inner ℂ (left:BurnolL2) (fourierL2 (K coordinate:BurnolL2))
 (p*((coordinate.value-1)⁻¹*2))*(d*Kself+e*Kcross-D*star (OriginalKGapProjectionEulerSource.Paid.actualMean (left:BurnolL2)))+
 (f*(coordinate.value⁻¹*2))*(e*Kself+d*Kcross-D*star (OriginalKGapProjectionEulerSource.Paid.actualMean
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left:BurnolL2)))+
 ((coordinate.value-star coordinate.value)*(p*(coordinate.value-1)⁻¹*d+f*coordinate.value⁻¹*e))*
  inner ℂ (left:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2))+
 ((coordinate.value+star coordinate.value-1)*(p*(coordinate.value-1)⁻¹*e+f*coordinate.value⁻¹*d))*
  inner ℂ (left:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)))

/-- The complete weighted M price consumes the new whole source field; no U/V response or target price is supplied. -/
theorem actual_common_M_source_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
 (left : BurnolPaAmbientCarrier) :
 actualCommonDeterminant coordinate*inner ℂ (left:BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h:BurnolL2))=
 actualCommonMSourcePrice coordinate h left :=by
 have source:=congrArg (fun field:BurnolL2=>inner ℂ (left:BurnolL2) field) (actual_common_M_R_source coordinate h)
 rw [inner_smul_right] at source
 unfold actualCommonMField at source
 dsimp only at source
 rw [inner_add_right,inner_add_right,inner_add_right,inner_smul_right,inner_smul_right,
  inner_smul_right,inner_smul_right,actual_common_field_input_price,actual_Fourier_common_field_input_price] at source
 exact source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualCommonKMeanPrice (h : ℝ) : ℂ:=
 actualCommonMSourcePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
  (K (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
def actualCommonFKMeanPrice (h : ℝ) : ℂ:=
 actualCommonMSourcePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
   (K (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))

/-- Original K/F K responses meet the complete weighted source through the exact same physical feet and material. -/
theorem actual_common_original_M_prices (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 actualCommonDeterminant coordinate*OriginalKGapProjectionEulerSource.actualGapSourceKMeanPrice observation nontrivial half h=
 actualCommonKMeanPrice observation nontrivial half h ∧
 actualCommonDeterminant coordinate*OriginalKGapProjectionEulerSource.actualGapSourceFKMeanPrice observation nontrivial half h=
 actualCommonFKMeanPrice observation nontrivial half h :=by
 have old:=OriginalKGapProjectionEulerSource.actual_original_K_FK_mean_source_price observation nontrivial half h
 dsimp only at old ⊢
 rw [←old.1,←old.2,OriginalKCombCofinalRAction.original_R_direct]
 constructor
 · exact actual_common_M_source_price
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
    (K (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
 · exact actual_common_M_source_price
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
     (K (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
