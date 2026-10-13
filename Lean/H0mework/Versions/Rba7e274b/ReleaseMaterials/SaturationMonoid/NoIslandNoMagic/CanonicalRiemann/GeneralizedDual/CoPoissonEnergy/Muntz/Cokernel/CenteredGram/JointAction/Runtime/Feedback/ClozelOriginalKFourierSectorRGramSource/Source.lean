import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCommonGapKernelSource.Consumer
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
local instance sectorPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualPlusSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=K coordinate+Fphysical (K coordinate)
def actualMinusSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=K coordinate-Fphysical (K coordinate)

theorem actual_source_two_Fourier_faces (coordinate : BurnolCompletedMellinCoordinate) :
 (Fphysical (actualPlusSource coordinate):BurnolL2)=(actualPlusSource coordinate:BurnolL2) ∧
 (Fphysical (actualMinusSource coordinate):BurnolL2)=(-1:ℂ) • (actualMinusSource coordinate:BurnolL2) :=by
 have twice:fourierL2 (fourierL2 (K coordinate:BurnolL2))=(K coordinate:BurnolL2):=by
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp (K coordinate).property.2
 change fourierL2 ((K coordinate:BurnolL2)+fourierL2 (K coordinate:BurnolL2))=
  (K coordinate:BurnolL2)+fourierL2 (K coordinate:BurnolL2) ∧
  fourierL2 ((K coordinate:BurnolL2)-fourierL2 (K coordinate:BurnolL2))=
  (-1:ℂ) • ((K coordinate:BurnolL2)-fourierL2 (K coordinate:BurnolL2))
 rw [map_add,map_sub,twice]
 constructor <;> module

/-- The actual R/Fourier pair generates the full complex diagonal, including its own imaginary price. -/
private theorem actual_complex_Fourier_source_price (coordinate : BurnolCompletedMellinCoordinate)
 (value : BurnolPaAmbientCarrier) (sign : ℝ) (unit : sign^2=1)
 (fixed : (Fphysical value:BurnolL2)=(sign:ℂ) • (value:BurnolL2)) :
 let response:=burnolDirectRightResolvent (coordinate.value/2) (value:BurnolL2)
 inner ℂ (value:BurnolL2) response=
 -((coordinate.value+star coordinate.value-1)/4)*(‖response‖:ℂ)^2+
 ((sign:ℂ)*(coordinate.value-star coordinate.value)/4)*inner ℂ (fourierL2 response) response :=by
 dsimp only
 let z:=coordinate.value/2
 let response:=burnolDirectRightResolvent z (value:BurnolL2)
 have right:1/4<z.re:=by
  dsimp only [z];rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have original:=burnolDirectRightResolventOrbit_hasDerivAt z right (value:BurnolL2)
 have opposite:=burnolFourierOrbit_hasDerivAt _ _ original
 have generated:=opposite.inner ℂ original
 have constant:(fun time:ℝ=>inner ℂ (burnolMultiplicativeDilation (-time/2) (fourierL2 response))
  (burnolMultiplicativeDilation (-time/2) response))=fun _=>inner ℂ (fourierL2 response) response:=
 funext fun time=>(burnolMultiplicativeDilation (-time/2)).inner_map_map _ _
 change HasDerivAt (fun time:ℝ=>inner ℂ (burnolMultiplicativeDilation (-time/2) (fourierL2 response))
  (burnolMultiplicativeDilation (-time/2) response)) _ 0 at generated
 rw [constant] at generated
 have source:=generated.unique (hasDerivAt_const (0:ℝ) (inner ℂ (fourierL2 response) response))
 simp only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] at source
 have read:=OriginalKGapProjectionEulerSource.actual_source_fourier_input response value
 rw [fixed,inner_smul_right] at read
 have fixedRaw:fourierL2 (value:BurnolL2)=(sign:ℂ) • (value:BurnolL2):=fixed
 change inner ℂ (fourierL2 response) ((z-1/4) • response+(value:BurnolL2))+
  inner ℂ (-fourierL2 ((z-1/4) • response+(value:BurnolL2))) response=0 at source
 simp only [map_add,map_smul,inner_add_right,inner_add_left,inner_neg_left,inner_smul_right,
  inner_smul_left,starRingEnd_apply] at source
 rw [read,fixedRaw,inner_smul_left] at source
 simp only [starRingEnd_apply,star_sub,star_div₀,star_ofNat,star_one] at source
 rw [show star (sign:ℂ)=(sign:ℂ) by exact Complex.conj_ofReal sign] at source
 have symmetry:inner ℂ response (value:BurnolL2)=star (inner ℂ (value:BurnolL2) response):=(inner_conj_symm response (value:BurnolL2)).symm
 rw [symmetry] at source
 have signUnit:(sign:ℂ)^2=1:=by exact_mod_cast unit
 have normGram:=burnolDirectRightResolvent_gram z z right right (value:BurnolL2)
 rw [inner_self_eq_norm_sq_to_K] at normGram
 change inner ℂ (value:BurnolL2) response=
  -((coordinate.value+star coordinate.value-1)/4)*(‖response‖:ℂ)^2+
  ((sign:ℂ)*(coordinate.value-star coordinate.value)/4)*inner ℂ (fourierL2 response) response
 dsimp only [z] at source normGram
 simp only [star_div₀,star_ofNat] at source normGram
 linear_combination (1/2:ℂ)*normGram-(sign:ℂ)/2*source-
  ((inner ℂ (value:BurnolL2) response-star (inner ℂ (value:BurnolL2) response))/2)*signUnit

def actualPlusPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 let response:=burnolDirectRightResolvent (coordinate.value/2) (actualPlusSource coordinate:BurnolL2);
 -((coordinate.value+star coordinate.value-1)/4)*(‖response‖:ℂ)^2+
 ((coordinate.value-star coordinate.value)/4)*inner ℂ (fourierL2 response) response

def actualMinusPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 let response:=burnolDirectRightResolvent (coordinate.value/2) (actualMinusSource coordinate:BurnolL2);
 -((coordinate.value+star coordinate.value-1)/4)*(‖response‖:ℂ)^2-
 ((coordinate.value-star coordinate.value)/4)*inner ℂ (fourierL2 response) response

theorem actual_two_sector_R_prices (coordinate : BurnolCompletedMellinCoordinate) :
 inner ℂ (actualPlusSource coordinate:BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (actualPlusSource coordinate:BurnolL2))=actualPlusPrice coordinate ∧
 inner ℂ (actualMinusSource coordinate:BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (actualMinusSource coordinate:BurnolL2))=actualMinusPrice coordinate :=by
 have qualified:=actual_source_two_Fourier_faces coordinate
 constructor
 · have fixed:(Fphysical (actualPlusSource coordinate):BurnolL2)=((1:ℝ):ℂ) • (actualPlusSource coordinate:BurnolL2):=by
    simpa only [Complex.ofReal_one,one_smul] using qualified.1
   have generated:=actual_complex_Fourier_source_price coordinate (actualPlusSource coordinate) 1 (by norm_num) fixed
   unfold actualPlusPrice
   simpa only [Complex.ofReal_one,one_mul] using generated
 · have fixed:(Fphysical (actualMinusSource coordinate):BurnolL2)=((-1:ℝ):ℂ) • (actualMinusSource coordinate:BurnolL2):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one] using qualified.2
   have generated:=actual_complex_Fourier_source_price coordinate (actualMinusSource coordinate) (-1) (by norm_num) fixed
   unfold actualMinusPrice
   simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,neg_div,one_mul,sub_eq_add_neg] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierSectorRGramSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
