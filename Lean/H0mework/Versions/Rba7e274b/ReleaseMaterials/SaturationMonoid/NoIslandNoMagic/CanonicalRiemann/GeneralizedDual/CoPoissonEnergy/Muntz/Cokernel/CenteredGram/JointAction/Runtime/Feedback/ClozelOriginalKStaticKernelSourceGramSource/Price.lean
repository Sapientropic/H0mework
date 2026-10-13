import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKStaticKernelSourceGramSource.Feet
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoupledPhysicalRFieldSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKStaticKernelSourceGramSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance staticKernelPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean

def actualWeightedKKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (star c.value+c.value-1)/2*(actualKPlusUpdatePrice c+actualKMinusUpdatePrice c)
def actualWeightedKFKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (star c.value-c.value)/2*(actualKMinusUpdatePrice c-actualKPlusUpdatePrice c)
def actualWeightedFKKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (star c.value+c.value-1)/2*(actualFKPlusUpdatePrice c+actualFKMinusUpdatePrice c)
def actualWeightedFKFKPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (star c.value-c.value)/2*(actualFKMinusUpdatePrice c-actualFKPlusUpdatePrice c)

/-- Four generated whole response fields consume the paid static original self/dual Gram feet. -/
theorem actual_generated_weighted_Gram_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c) (Field.actualWeightedKResponseField c)=actualWeightedKKPrice c ∧
 inner ℂ (K c) (Field.actualWeightedFKResponseField c)=actualWeightedKFKPrice c ∧
 inner ℂ (Fphysical (K c)) (Field.actualWeightedKResponseField c)=actualWeightedFKKPrice c ∧
 inner ℂ (Fphysical (K c)) (Field.actualWeightedFKResponseField c)=actualWeightedFKFKPrice c :=by
 have read:=actual_static_projected_update_prices c
 unfold Field.actualWeightedKResponseField Field.actualWeightedFKResponseField
  OriginalKCoupledPhysicalRFieldSource.actualWeightedPlusRField OriginalKCoupledPhysicalRFieldSource.actualWeightedMinusRField
 simp only [inner_add_right,inner_sub_right,inner_smul_right]
 rw [read.1,read.2.1,read.2.2.1,read.2.2.2]
 unfold actualWeightedKKPrice actualWeightedKFKPrice actualWeightedFKKPrice actualWeightedFKFKPrice
 exact ⟨by ring,by ring,by ring,by ring⟩

def actualPaidKCommonInputPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ:=
 let p:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed c h x
 let f:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed c h x
 let d:=OriginalKCommonGapKernelSource.actualCommonFirst c
 let e:=OriginalKCommonGapKernelSource.actualCommonSecond c
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 (p*((c.value-1)⁻¹*2))*(d*actualSelfKernelGram c+e*actualFourierSelfGram c-D*star (μ (K c:BurnolL2)))+
 (f*(c.value⁻¹*2))*(e*actualSelfKernelGram c+d*actualFourierSelfGram c-D*star (μ (fourierL2 (K c:BurnolL2))))
def actualPaidFKCommonInputPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ:=
 let p:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed c h x
 let f:=∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed c h x
 let d:=OriginalKCommonGapKernelSource.actualCommonFirst c
 let e:=OriginalKCommonGapKernelSource.actualCommonSecond c
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 (p*((c.value-1)⁻¹*2))*(d*actualFourierSelfGram c+e*actualSelfKernelGram c-D*star (μ (fourierL2 (K c:BurnolL2))))+
 (f*(c.value⁻¹*2))*(e*actualFourierSelfGram c+d*actualSelfKernelGram c-D*star (μ (K c:BurnolL2)))

/-- Complete common input stock is read on the same K/F K feet, consuming the already-paid original Gram. -/
theorem actual_two_static_common_input_prices (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 inner ℂ (K c) (OriginalKCoupledPhysicalRFieldSource.actualProjectedMInputField c h)=actualPaidKCommonInputPrice c h ∧
 inner ℂ (Fphysical (K c)) (OriginalKCoupledPhysicalRFieldSource.actualProjectedMInputField c h)=actualPaidFKCommonInputPrice c h :=by
 have Gram:=actual_original_static_source_Gram_feet c
 have means:=actual_static_G_FG_input_prices c
 unfold OriginalKCoupledPhysicalRFieldSource.actualProjectedMInputField
  OriginalKCoupledPhysicalRFieldSource.actualProjectedCommonField OriginalKCoupledPhysicalRFieldSource.actualProjectedFourierCommonField
 simp only [inner_add_right,inner_sub_right,inner_smul_right]
 rw [means.1,means.2.1,means.2.2.1,means.2.2.2]
 have self:inner ℂ (K c) (K c)=actualSelfKernelGram c:=Gram.1
 have selfF:inner ℂ (Fphysical (K c)) (Fphysical (K c))=actualSelfKernelGram c:=Gram.2.2.1
 have crossF:inner ℂ (Fphysical (K c)) (K c)=actualFourierSelfGram c:=Gram.2.2.2
 have cross:inner ℂ (K c) (Fphysical (K c))=actualFourierSelfGram c:=rfl
 rw [self,selfF,crossF,cross]
 unfold actualPaidKCommonInputPrice actualPaidFKCommonInputPrice
 exact ⟨rfl,rfl⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualStaticKMeanPrice (h : ℝ) : ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*actualPaidKCommonInputPrice c h+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h*actualWeightedKKPrice c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h*actualWeightedKFKPrice c
def actualStaticFKMeanPrice (h : ℝ) : ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*actualPaidFKCommonInputPrice c h+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h*actualWeightedFKKPrice c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h*actualWeightedFKFKPrice c

/-- First direct consumer: the actual complete whole M price consumes both paid original self/dual Gram feet while retaining Fourier-cross/Tate/mean inventory. -/
theorem actual_static_source_complete_M_prices (h : ℝ) :
 OriginalKCoupledPhysicalRFieldSource.actualWeightedKMeanPrice observation nontrivial half h=actualStaticKMeanPrice observation nontrivial half h ∧
 OriginalKCoupledPhysicalRFieldSource.actualWeightedFKMeanPrice observation nontrivial half h=actualStaticFKMeanPrice observation nontrivial half h :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have fields:=actual_generated_weighted_Gram_prices c
 have input:=actual_two_static_common_input_prices c h
 unfold OriginalKCoupledPhysicalRFieldSource.actualWeightedKMeanPrice OriginalKCoupledPhysicalRFieldSource.actualWeightedFKMeanPrice
  OriginalKCoupledPhysicalRFieldSource.actualWeightedMResponseField
 dsimp only
 simp only [inner_add_right,inner_smul_right]
 rw [fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,input.1,input.2]
 exact ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKStaticKernelSourceGramSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
