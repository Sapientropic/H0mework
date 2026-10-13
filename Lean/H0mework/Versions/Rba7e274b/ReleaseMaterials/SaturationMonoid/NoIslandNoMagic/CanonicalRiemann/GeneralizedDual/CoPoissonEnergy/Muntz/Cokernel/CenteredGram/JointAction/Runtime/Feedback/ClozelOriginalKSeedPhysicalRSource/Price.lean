import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSeedPhysicalRSource.Feet
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSeedPhysicalRSource.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance seedPhysicalPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
def actualKPlusSeedNativeUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*
 (-(Static.actualCompactKPrice c U+Static.actualCompactKPrice c V)+(1-c.value)*actualNativeKSeedPrice c+star (μ (fourierL2 (K c:BurnolL2))))+
 2*(Static.actualSelfKernelGram c+Static.actualFourierSelfGram c)-(OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*(star (μ (K c:BurnolL2))+star (μ (fourierL2 (K c:BurnolL2))))
def actualKMinusSeedNativeUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*
 (Static.actualCompactKPrice c U-Static.actualCompactKPrice c V+(1-c.value)*actualNativeKSeedPrice c-star (μ (fourierL2 (K c:BurnolL2))))+
 2*(Static.actualSelfKernelGram c-Static.actualFourierSelfGram c)-(OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*(star (μ (K c:BurnolL2))-star (μ (fourierL2 (K c:BurnolL2))))

def actualFKPlusSeedNativeUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*
 (-(Static.actualCompactFKPrice c U+Static.actualCompactFKPrice c V)+(1-c.value)*actualNativeFKSeedPrice c+star (μ (K c:BurnolL2)))+
 2*(Static.actualFourierSelfGram c+Static.actualSelfKernelGram c)-(OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*(star (μ (fourierL2 (K c:BurnolL2)))+star (μ (K c:BurnolL2)))
def actualFKMinusSeedNativeUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*
 (Static.actualCompactFKPrice c U-Static.actualCompactFKPrice c V+(1-c.value)*actualNativeFKSeedPrice c-star (μ (K c:BurnolL2)))+
 2*(Static.actualFourierSelfGram c-Static.actualSelfKernelGram c)-(OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*(star (μ (fourierL2 (K c:BurnolL2)))-star (μ (K c:BurnolL2)))


/-- All four actual update prices consume the same source-generated native seed field. -/
theorem actual_seed_native_update_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c) (actualPlusSeedNativeProjectedUpdate c)=actualKPlusSeedNativeUpdatePrice c ∧
 inner ℂ (K c) (actualMinusSeedNativeProjectedUpdate c)=actualKMinusSeedNativeUpdatePrice c ∧
 inner ℂ (Fphysical (K c)) (actualPlusSeedNativeProjectedUpdate c)=actualFKPlusSeedNativeUpdatePrice c ∧
 inner ℂ (Fphysical (K c)) (actualMinusSeedNativeProjectedUpdate c)=actualFKMinusSeedNativeUpdatePrice c :=by
 have source:=OriginalKStaticKernelSourceGramSource.actual_static_projected_update_prices c
 have fields:=actual_two_seed_native_projected_updates c
 have seeds:=actual_compact_seed_native_prices c
 rw [fields.1,fields.2] at source
 unfold OriginalKStaticKernelSourceGramSource.actualKPlusUpdatePrice OriginalKStaticKernelSourceGramSource.actualKMinusUpdatePrice
  OriginalKStaticKernelSourceGramSource.actualFKPlusUpdatePrice OriginalKStaticKernelSourceGramSource.actualFKMinusUpdatePrice at source
 rw [seeds.1,seeds.2] at source
 exact source

def actualNativeWeightedKKPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (star c.value+c.value-1)/2*(actualKPlusSeedNativeUpdatePrice c+actualKMinusSeedNativeUpdatePrice c)
def actualNativeWeightedKFKPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (star c.value-c.value)/2*(actualKMinusSeedNativeUpdatePrice c-actualKPlusSeedNativeUpdatePrice c)
def actualNativeWeightedFKKPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (star c.value+c.value-1)/2*(actualFKPlusSeedNativeUpdatePrice c+actualFKMinusSeedNativeUpdatePrice c)
def actualNativeWeightedFKFKPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (star c.value-c.value)/2*(actualFKMinusSeedNativeUpdatePrice c-actualFKPlusSeedNativeUpdatePrice c)

theorem actual_seed_native_weighted_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c) (actualSeedNativeWeightedKField c)=actualNativeWeightedKKPrice c ∧
 inner ℂ (K c) (actualSeedNativeWeightedFKField c)=actualNativeWeightedKFKPrice c ∧
 inner ℂ (Fphysical (K c)) (actualSeedNativeWeightedKField c)=actualNativeWeightedFKKPrice c ∧
 inner ℂ (Fphysical (K c)) (actualSeedNativeWeightedFKField c)=actualNativeWeightedFKFKPrice c :=by
 have source:=actual_seed_native_update_prices c
 unfold actualSeedNativeWeightedKField actualSeedNativeWeightedFKField
 simp only [inner_smul_right,inner_add_right,inner_sub_right]
 rw [source.1,source.2.1,source.2.2.1,source.2.2.2]
 exact ⟨rfl,rfl,rfl,rfl⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualSeedNativeKMeanPrice (h : ℝ) : ℂ :=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKStaticKernelSourceGramSource.actualPaidKCommonInputPrice c h+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h*actualNativeWeightedKKPrice c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h*actualNativeWeightedKFKPrice c
def actualSeedNativeFKMeanPrice (h : ℝ) : ℂ :=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKStaticKernelSourceGramSource.actualPaidFKCommonInputPrice c h+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h*actualNativeWeightedFKKPrice c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h*actualNativeWeightedFKFKPrice c

/-- The whole original M consumes the native seed field, eliminating its independent Tate/quarter-mean inventory in both prices. -/
theorem actual_complete_seed_native_M_prices (h : ℝ) :
 OriginalKStaticKernelSourceGramSource.actualStaticKMeanPrice observation nontrivial half h=actualSeedNativeKMeanPrice observation nontrivial half h ∧
 OriginalKStaticKernelSourceGramSource.actualStaticFKMeanPrice observation nontrivial half h=actualSeedNativeFKMeanPrice observation nontrivial half h :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have old:=OriginalKStaticKernelSourceGramSource.actual_static_source_complete_M_prices observation nontrivial half h
 have newprices:OriginalKCoupledPhysicalRFieldSource.actualWeightedKMeanPrice observation nontrivial half h=actualSeedNativeKMeanPrice observation nontrivial half h ∧
  OriginalKCoupledPhysicalRFieldSource.actualWeightedFKMeanPrice observation nontrivial half h=actualSeedNativeFKMeanPrice observation nontrivial half h :=by
  have fields:=actual_seed_native_weighted_prices c
  have input:=OriginalKStaticKernelSourceGramSource.actual_two_static_common_input_prices c h
  unfold OriginalKCoupledPhysicalRFieldSource.actualWeightedKMeanPrice OriginalKCoupledPhysicalRFieldSource.actualWeightedFKMeanPrice
  dsimp only
  rw [actual_complete_seed_native_M_field]
  unfold actualSeedNativeWholeMField
  simp only [inner_smul_right,inner_add_right]
  rw [fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,input.1,input.2]
  exact ⟨rfl,rfl⟩
 exact ⟨old.1.symm.trans newprices.1,old.2.symm.trans newprices.2⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
