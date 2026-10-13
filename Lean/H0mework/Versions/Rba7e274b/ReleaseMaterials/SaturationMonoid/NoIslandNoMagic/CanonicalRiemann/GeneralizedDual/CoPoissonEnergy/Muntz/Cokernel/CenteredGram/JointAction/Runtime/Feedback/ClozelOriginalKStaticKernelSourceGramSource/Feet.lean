import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKStaticKernelSourceGramSource.Source
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
local instance staticKernelFeetComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

namespace Field
export OriginalKCoupledPhysicalRFieldSource (actualCompactProjectedRField actualPlusProjectedUpdate actualMinusProjectedUpdate actualWeightedKResponseField actualWeightedFKResponseField actualWeightedMResponseField)
end Field
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "q" => (1/4:ℝ)
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed

def actualCompactGapWeight (c : BurnolCompletedMellinCoordinate) (source : BurnolL2) : ℂ:=
 (1/2:ℂ)*((OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source*
  (((2*q:ℝ):ℂ)*(q:ℂ)^(-c.value))-μ source)/(c.value/2-1/2))+
 (2:ℂ)*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source*
  star (burnolMellinGapMoment (OriginalKQuarterTailPhysicalSource.actualStarSource c).value)
def actualCompactKPrice (c : BurnolCompletedMellinCoordinate) (source : BurnolL2) : ℂ:=
 -(2*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source)*actualDualKernelGram c+
 actualCompactGapWeight c source*star (μ (K c:BurnolL2))
def actualCompactFKPrice (c : BurnolCompletedMellinCoordinate) (source : BurnolL2) : ℂ:=
 -(2*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source)*actualFourierDualGram c+
 actualCompactGapWeight c source*star (μ (fourierL2 (K c:BurnolL2)))

/-- Both original G faces retain the actual same K/F K source means on their own physical feet. -/
theorem actual_static_G_FG_input_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c) G=star (μ (K c:BurnolL2)) ∧
 inner ℂ (Fphysical (K c)) G=star (μ (fourierL2 (K c:BurnolL2))) ∧
 inner ℂ (K c) (Fphysical G)=star (μ (fourierL2 (K c:BurnolL2))) ∧
 inner ℂ (Fphysical (K c)) (Fphysical G)=star (μ (K c:BurnolL2)) :=by
 have first:=congrArg star (OriginalKGapProjectionEulerSource.actual_gap_physical_input_price (K c))
 have second:=congrArg star (OriginalKGapProjectionEulerSource.actual_gap_physical_input_price (Fphysical (K c)))
 have Kread:inner ℂ (K c) G=star (μ (K c:BurnolL2)):=
  ((inner_conj_symm (K c:BurnolL2) (G:BurnolL2)).symm).trans first
 have FKread:inner ℂ (Fphysical (K c)) G=star (μ (fourierL2 (K c:BurnolL2))):=
  ((inner_conj_symm (Fphysical (K c):BurnolL2) (G:BurnolL2)).symm).trans second
 have moved:=OriginalKGapProjectionEulerSource.actual_source_fourier_input (K c:BurnolL2) G
 change inner ℂ (Fphysical (K c)) G=inner ℂ (K c) (Fphysical G) at moved
 have unitary:inner ℂ (Fphysical (K c)) (Fphysical G)=inner ℂ (K c) G:=
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map _ _
 exact ⟨Kread,FKread,moved.symm.trans FKread,unitary.trans Kread⟩

/-- The literal whole compact source fields consume the paid self/dual original K Gram; Fourier-dual inventory remains literal. -/
theorem actual_compact_static_Gram_prices (c : BurnolCompletedMellinCoordinate) (source : BurnolL2) :
 inner ℂ (K c) (Field.actualCompactProjectedRField c source)=actualCompactKPrice c source ∧
 inner ℂ (Fphysical (K c)) (Field.actualCompactProjectedRField c source)=actualCompactFKPrice c source :=by
 have Gram:=actual_original_static_source_Gram_feet c
 have Gprices:=actual_static_G_FG_input_prices c
 unfold Field.actualCompactProjectedRField actualCompactKPrice actualCompactFKPrice actualCompactGapWeight
 simp only [inner_add_right,inner_smul_right]
 change _*inner ℂ (K c:BurnolL2) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c):BurnolL2)+_= _ ∧
  _*inner ℂ (fourierL2 (K c:BurnolL2)) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c):BurnolL2)+_= _
 rw [Gram.2.1,Gprices.1,Gprices.2.1]
 exact ⟨rfl,rfl⟩

def actualKPlusUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*
 (-(actualCompactKPrice c U+actualCompactKPrice c V)+(1-c.value)*actualCompactKPrice c s+star (μ (fourierL2 (K c:BurnolL2))))+
 2*(actualSelfKernelGram c+actualFourierSelfGram c)-(OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*(star (μ (K c:BurnolL2))+star (μ (fourierL2 (K c:BurnolL2))))
def actualKMinusUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*
 (actualCompactKPrice c U-actualCompactKPrice c V+(1-c.value)*actualCompactKPrice c s-star (μ (fourierL2 (K c:BurnolL2))))+
 2*(actualSelfKernelGram c-actualFourierSelfGram c)-(OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*(star (μ (K c:BurnolL2))-star (μ (fourierL2 (K c:BurnolL2))))

def actualFKPlusUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*
 (-(actualCompactFKPrice c U+actualCompactFKPrice c V)+(1-c.value)*actualCompactFKPrice c s+star (μ (K c:BurnolL2)))+
 2*(actualFourierSelfGram c+actualSelfKernelGram c)-(OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*(star (μ (fourierL2 (K c:BurnolL2)))+star (μ (K c:BurnolL2)))
def actualFKMinusUpdatePrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*
 (actualCompactFKPrice c U-actualCompactFKPrice c V+(1-c.value)*actualCompactFKPrice c s-star (μ (K c:BurnolL2)))+
 2*(actualFourierSelfGram c-actualSelfKernelGram c)-(OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*(star (μ (fourierL2 (K c:BurnolL2)))-star (μ (K c:BurnolL2)))

/-- All four update feet directly consume the generated whole fields and paid same-source Gram values. -/
theorem actual_static_projected_update_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c) (Field.actualPlusProjectedUpdate c)=actualKPlusUpdatePrice c ∧
 inner ℂ (K c) (Field.actualMinusProjectedUpdate c)=actualKMinusUpdatePrice c ∧
 inner ℂ (Fphysical (K c)) (Field.actualPlusProjectedUpdate c)=actualFKPlusUpdatePrice c ∧
 inner ℂ (Fphysical (K c)) (Field.actualMinusProjectedUpdate c)=actualFKMinusUpdatePrice c :=by
 have Gram:=actual_original_static_source_Gram_feet c
 have Gprices:=actual_static_G_FG_input_prices c
 have up:=actual_compact_static_Gram_prices c U
 have vp:=actual_compact_static_Gram_prices c V
 have seed:=actual_compact_static_Gram_prices c s
 have plus:OriginalKFourierSectorRGramSource.actualPlusSource c=K c+Fphysical (K c):=rfl
 have minus:OriginalKFourierSectorRGramSource.actualMinusSource c=K c-Fphysical (K c):=rfl
 unfold Field.actualPlusProjectedUpdate Field.actualMinusProjectedUpdate
  OriginalKCoupledPhysicalRFieldSource.actualPlusProjectedForcing OriginalKCoupledPhysicalRFieldSource.actualMinusProjectedForcing
 rw [plus,minus]
 simp only [inner_add_right,inner_sub_right,inner_neg_right,inner_smul_right]
 rw [up.1,up.2,vp.1,vp.2,seed.1,seed.2,Gprices.1,Gprices.2.1,Gprices.2.2.1,Gprices.2.2.2]
 have self:inner ℂ (K c) (K c)=actualSelfKernelGram c:=Gram.1
 have selfF:inner ℂ (Fphysical (K c)) (Fphysical (K c))=actualSelfKernelGram c:=Gram.2.2.1
 have crossF:inner ℂ (Fphysical (K c)) (K c)=actualFourierSelfGram c:=Gram.2.2.2
 have cross:inner ℂ (K c) (Fphysical (K c))=actualFourierSelfGram c:=rfl
 rw [self,selfF,crossF,cross]
 unfold actualKPlusUpdatePrice actualKMinusUpdatePrice actualFKPlusUpdatePrice actualFKMinusUpdatePrice
 exact ⟨rfl,rfl,rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKStaticKernelSourceGramSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
