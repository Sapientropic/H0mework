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
local instance staticKernelSourceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualKernelGramPrice (left right : BurnolCompletedMellinCoordinate) : ℂ:=
 (star (OriginalRieszSource.Kernel.A left)*OriginalRieszSource.Kernel.A right-
  star (OriginalRieszSource.Kernel.beta left)*OriginalRieszSource.Kernel.beta right)/
 (2*(left.value+star right.value-1))

/-- The already-generated original whole K Green form is consumed with its own admitted source rate. -/
theorem actual_paid_original_K_Gram_price (left right : BurnolCompletedMellinCoordinate) :
 inner ℂ (K left:BurnolL2) (K right:BurnolL2)=actualKernelGramPrice left right :=by
 have source:=OriginalRieszSourceGreen.original_kernel_gram left right
 have unit:=OriginalRieszSourceGreen.source_cross_parameter_ne_zero left right
 unfold actualKernelGramPrice
 apply (eq_div_iff (mul_ne_zero (by norm_num:(2:ℂ)≠0) unit)).mpr
 linear_combination (2:ℂ)*source

def actualSelfKernelGram (c : BurnolCompletedMellinCoordinate) : ℂ:=actualKernelGramPrice c c
def actualDualKernelGram (c : BurnolCompletedMellinCoordinate) : ℂ:=
 actualKernelGramPrice c (OriginalKQuarterTailPhysicalSource.actualStarSource c)
def actualFourierSelfGram (c : BurnolCompletedMellinCoordinate) : ℂ:=
 inner ℂ (K c:BurnolL2) (fourierL2 (K c:BurnolL2))
def actualFourierDualGram (c : BurnolCompletedMellinCoordinate) : ℂ:=
 inner ℂ (fourierL2 (K c:BurnolL2))
  (K (OriginalKQuarterTailPhysicalSource.actualStarSource c):BurnolL2)

/-- Original self and dual feet consume paid source Green; Fourier feet retain the actual same-source cross inventory. -/
theorem actual_original_static_source_Gram_feet (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c:BurnolL2) (K c:BurnolL2)=actualSelfKernelGram c ∧
 inner ℂ (K c:BurnolL2) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c):BurnolL2)=actualDualKernelGram c ∧
 inner ℂ (fourierL2 (K c:BurnolL2)) (fourierL2 (K c:BurnolL2))=actualSelfKernelGram c ∧
 inner ℂ (fourierL2 (K c:BurnolL2)) (K c:BurnolL2)=actualFourierSelfGram c :=by
 constructor
 · exact actual_paid_original_K_Gram_price c c
 constructor
 · exact actual_paid_original_K_Gram_price c _
 constructor
 · rw [fourierL2.inner_map_map]
   exact actual_paid_original_K_Gram_price c c
 · exact OriginalKGapProjectionEulerSource.actual_source_fourier_input (K c:BurnolL2) (K c)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKStaticKernelSourceGramSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
