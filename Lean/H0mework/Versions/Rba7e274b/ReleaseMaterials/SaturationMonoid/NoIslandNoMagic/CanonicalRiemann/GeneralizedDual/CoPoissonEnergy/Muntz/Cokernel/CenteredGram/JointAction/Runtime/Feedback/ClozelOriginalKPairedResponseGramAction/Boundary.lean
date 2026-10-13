import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Gram
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance boundaryAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
theorem actual_inventory_forcing_balance (h : ℝ) :
 (observation.coordinate/2-1/4)*inner ℂ (Q (ActionSource.pairedResponse observation nontrivial half h)) (Q (ActionSource.pairedResponse observation nontrivial half h))+
 star (observation.coordinate/2-1/4)*inner ℂ (Q (ActionSource.siblingResponse observation nontrivial half h)) (Q (ActionSource.siblingResponse observation nontrivial half h))+
 (1/2:ℂ)*(inner ℂ (Q (ActionSource.pairedResponse observation nontrivial half h)) (Q (ActionSource.completeSource observation nontrivial half h)+Q (fourierL2 (ActionSource.completeSource observation nontrivial half h)))+
 inner ℂ (Q (ActionSource.completeSource observation nontrivial half h)-Q (fourierL2 (ActionSource.completeSource observation nontrivial half h))) (Q (ActionSource.siblingResponse observation nontrivial half h)))+
 actualOutsideFlux observation nontrivial half h+actualPaFlux observation nontrivial half h=0 := by
 have generated := actual_projected_forcing_price observation nontrivial half h
 rw [actual_generated_flux_inventory] at generated
 unfold pairedVelocity siblingVelocity at generated
 simp only [map_add,map_sub,map_smul,inner_add_left,inner_add_right,inner_sub_left,inner_smul_left,inner_smul_right,map_div₀,map_ofNat,map_one,starRingEnd_apply] at generated
 simp only [inner_add_right,inner_sub_left,star_sub,star_div₀,star_ofNat,star_one]
 linear_combination generated

namespace BoundarySource
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint.FullStock
 (generatedBoundary generated_boundary_realizes_original)
end BoundarySource

def originalGeneratedPaBoundary (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolPaAmbientCarrier :=
 OP (BoundarySource.generatedBoundary (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded)

theorem actual_original_boundary_forcing (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Q (ActionSource.completeSource observation nontrivial half h)=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)) •
 burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) := by
 unfold originalGeneratedPaBoundary
 rw [BoundarySource.generated_boundary_realizes_original _ observation.mathlibZero h nonnegative bounded]
 exact OriginalKFullSourceRResponse.actual_source_Q_boundary_residual observation nontrivial half h nonnegative bounded

theorem actual_source_fourier_face (h : ℝ) :
 Q (fourierL2 (ActionSource.completeSource observation nontrivial half h))=
 Fphysical (Q (ActionSource.completeSource observation nontrivial half h)) := by
 exact OriginalKFullSourceRResponse.source_fourier_restriction observation nontrivial half h

def originalBoundaryCross (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : ℂ :=
 let b:=originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded
 let factor:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 inner ℂ (Q (ActionSource.pairedResponse observation nontrivial half h)) (factor • (b+Fphysical b))+
 inner ℂ (factor • (b-Fphysical b)) (Q (ActionSource.siblingResponse observation nontrivial half h))

def originalKernelCross (h : ℝ) : ℂ :=
 let k:=burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let factor:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 inner ℂ (Q (ActionSource.pairedResponse observation nontrivial half h)) (factor • (k+Fphysical k))+
 inner ℂ (factor • (k-Fphysical k)) (Q (ActionSource.siblingResponse observation nontrivial half h))

theorem actual_original_character_inventory_ward (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 (observation.coordinate/2-1/4)*inner ℂ (Q (ActionSource.pairedResponse observation nontrivial half h)) (Q (ActionSource.pairedResponse observation nontrivial half h))+
 star (observation.coordinate/2-1/4)*inner ℂ (Q (ActionSource.siblingResponse observation nontrivial half h)) (Q (ActionSource.siblingResponse observation nontrivial half h))+
 (1/2:ℂ)*(originalBoundaryCross observation nontrivial half h nonnegative bounded-originalKernelCross observation nontrivial half h)+
 actualOutsideFlux observation nontrivial half h+actualPaFlux observation nontrivial half h=0 := by
 have generated := actual_inventory_forcing_balance observation nontrivial half h
 rw [actual_source_fourier_face,actual_original_boundary_forcing observation nontrivial half h nonnegative bounded] at generated
 simp only [map_sub,map_smul] at generated
 unfold originalBoundaryCross originalKernelCross
 dsimp only
 simp only [smul_add,smul_sub,inner_add_right,inner_sub_right,inner_sub_left] at generated ⊢
 linear_combination generated

private theorem actual_generated_boundary_kernel_read (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
 (originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded)=
 OriginalRieszFinitePairing.evaluatorSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have kernelMember:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero
 have read:=burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left
   ⟨burnolCompletedMellinRieszVector coordinate,kernelMember⟩
   (BoundarySource.generatedBoundary coordinate h nonnegative bounded)
 change inner ℂ (burnolCompletedMellinRieszVector coordinate) (OP (BoundarySource.generatedBoundary coordinate h nonnegative bounded))=
   inner ℂ (burnolCompletedMellinRieszVector coordinate) (BoundarySource.generatedBoundary coordinate h nonnegative bounded) at read
 unfold originalGeneratedPaBoundary
 rw [read,BoundarySource.generated_boundary_realizes_original coordinate observation.mathlibZero h nonnegative bounded,
   burnolCompletedMellinRieszVector_readback]
 exact OriginalRieszFinitePairing.original_evaluator_source coordinate observation.mathlibZero h nonnegative

/-- The original K reads the complete same-source forcing via its paid finite Ward action. -/
theorem actual_original_kernel_source_ward (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
   (Q (ActionSource.completeSource observation nontrivial half h))=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*
 ((pairedMellinTranslationCharacter (star observation.coordinate) h-1)*
   OriginalRieszFinitePairing.kernelSelfSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)+
 (1/2:ℂ)*OriginalKFiniteWardGram.sourceEnergy (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have originalSelf:=OriginalRieszFinitePairing.original_kernel_self_source coordinate
 change inner ℂ (burnolCompletedMellinRieszVector coordinate) (burnolCompletedMellinRieszVector coordinate)=_ at originalSelf
 rw [actual_original_boundary_forcing observation nontrivial half h nonnegative bounded,
   inner_sub_right,inner_smul_right,inner_smul_right,actual_generated_boundary_kernel_read,originalSelf,
   OriginalKFiniteWardGram.source_evaluator_energy_ward coordinate h nonnegative,
   OriginalKCombCofinalTwoDirection.coordinate_value]
 ring

def actualPaSourceStock (h : ℝ) : BurnolPaAmbientCarrier :=
 OriginalKCombCofinalPaAction.E (ActionSource.completeSource observation nontrivial half h)
def actualOutsideSourceStock (h : ℝ) : BurnolL2 :=
 originalOutside (ActionSource.completeSource observation nontrivial half h)

theorem actual_source_stock_read (h : ℝ) :
 ActionSource.completeSource observation nontrivial half h=
 (Q (ActionSource.completeSource observation nontrivial half h) : BurnolL2)+
 (actualPaSourceStock observation nontrivial half h : BurnolL2)+actualOutsideSourceStock observation nontrivial half h := by
 let value:=ActionSource.completeSource observation nontrivial half h
 have physical:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal value
 change (P value : BurnolL2)+originalOutside value=value at physical
 have inside:=congrArg (fun material : BurnolPaAmbientCarrier=>(material : BurnolL2))
   (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (P value))
 change (OriginalKCombCofinalPaAction.E value : BurnolL2)+(Q value : BurnolL2)=(P value : BurnolL2) at inside
 calc
  value=(P value : BurnolL2)+originalOutside value := physical.symm
  _ = ((OriginalKCombCofinalPaAction.E value : BurnolL2)+(Q value : BurnolL2))+originalOutside value := congrArg (fun material : BurnolL2=>material+originalOutside value) inside.symm
  _ = _ := by unfold actualPaSourceStock actualOutsideSourceStock; dsimp only [value]; abel

def originalBoundaryRResponse (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded : BurnolL2)
def originalKernelRResponse : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
def actualPaRResponseStock (h : ℝ) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualPaSourceStock observation nontrivial half h : BurnolL2)
def actualOutsideRResponseStock (h : ℝ) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualOutsideSourceStock observation nontrivial half h)

/-- Original R acts on the complete same-source inventory, before any paired read. -/
theorem actual_original_R_source_coupling (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (ActionSource.completeSource observation nontrivial half h)=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • originalBoundaryRResponse observation nontrivial half h nonnegative bounded-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)) • originalKernelRResponse observation nontrivial half+
 actualPaRResponseStock observation nontrivial half h+actualOutsideRResponseStock observation nontrivial half h := by
 have input:=congrArg (fun value : BurnolL2=>OriginalKFullSourceRResponse.Op.R observation nontrivial half value)
   (actual_source_stock_read observation nontrivial half h)
 rw [map_add,map_add] at input
 have boundary:=congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2))
   (actual_original_boundary_forcing observation nontrivial half h nonnegative bounded)
 simp only [Submodule.coe_sub,Submodule.coe_smul] at boundary
 rw [boundary,map_sub,map_smul,map_smul] at input
 exact input

theorem actual_Pa_R_kernel_inventory (h : ℝ) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (actualPaRResponseStock observation nontrivial half h)=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualPaSourceStock observation nontrivial half h)*
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have inside : actualPaSourceStock observation nontrivial half h ∈ burnolCompactCoPoissonClosedRange :=
   burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_apply_mem _
 have kernelMember:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero
 have paid:=burnolPaResolvent_source_pairing coordinate (actualPaSourceStock observation nontrivial half h) inside
   ⟨burnolCompletedMellinRieszVector coordinate,kernelMember⟩
 unfold actualPaRResponseStock
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rw [OriginalKCombCofinalTwoDirection.coordinate_value] at paid
 exact paid

theorem actual_Pa_R_fourier_kernel_inventory (h : ℝ) :
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (actualPaRResponseStock observation nontrivial half h)=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualPaSourceStock observation nontrivial half h)*
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have inside : actualPaSourceStock observation nontrivial half h ∈ burnolCompactCoPoissonClosedRange :=
   burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_apply_mem _
 have kernelMember:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero
 let originalK : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector coordinate,kernelMember⟩
 have paid:=burnolPaResolvent_source_pairing coordinate (actualPaSourceStock observation nontrivial half h) inside
   (burnolCompactCoPoissonActionSquare.orthogonalAction originalK)
 change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
   (burnolDirectRightResolvent (coordinate.value/2) (actualPaSourceStock observation nontrivial half h : BurnolL2))=_ at paid
 unfold actualPaRResponseStock
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rw [OriginalKCombCofinalTwoDirection.coordinate_value] at paid
 exact paid

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
