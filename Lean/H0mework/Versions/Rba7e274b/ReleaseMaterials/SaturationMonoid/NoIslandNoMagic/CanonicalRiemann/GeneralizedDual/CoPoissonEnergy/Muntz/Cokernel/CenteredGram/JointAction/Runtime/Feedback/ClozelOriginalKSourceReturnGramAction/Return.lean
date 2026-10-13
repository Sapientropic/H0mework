import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Cross
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Defect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
open OriginalRieszSource
namespace Paid
export OriginalKPairedResponseGramAction
 (originalKernelRResponse actualMovedOutsideRStock actualOriginalWaveRStock actualOutsideRResponseStock actual_original_complete_response_evolution originalKernelCross originalPairKernelRead originalSiblingKernelRead)
end Paid
namespace Return
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (sourceA primitiveSource original_return_source_equation)
end Return
namespace Src
export OriginalKFullSourceRResponse (completeSource)
end Src
local instance returnAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def closedKernelSource : BurnolL2 :=
 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)+
 Return.primitiveSource observation nontrivial half

/-- The actual source return generates the K response; no nonzero source scalar is supplied. -/
theorem actual_original_K_return :
 Return.sourceA observation • Paid.originalKernelRResponse observation nontrivial half=
 closedKernelSource observation nontrivial half := by
 have actual:=Return.original_return_source_equation observation nontrivial half
 unfold closedKernelSource
 rw [add_comm]
 exact sub_eq_iff_eq_add.mp actual

theorem actual_sourceA_star : star (Return.sourceA observation)=-Return.sourceA observation := by
 unfold Return.sourceA
 simp only [star_div₀,star_sub,star_star,star_ofNat]
 ring

/-- sourceA acts on the maximal actual source equation and consumes its original K return law. -/
theorem actual_scaled_complete_response (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Return.sourceA observation • OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h)=
 ((2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*pairedMellinTranslationCharacter (star observation.coordinate) h) • closedKernelSource observation nontrivial half-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • pairedBurnolMultiplicativeDilation h (closedKernelSource observation nontrivial half)+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
 Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
 Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h := by
 have actual:=congrArg (fun material : BurnolL2=>Return.sourceA observation • material)
   (Paid.actual_original_complete_response_evolution observation nontrivial half h nonnegative bounded)
 calc
  _ = _ := actual
  _ = ((2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*pairedMellinTranslationCharacter (star observation.coordinate) h) •
      (Return.sourceA observation • Paid.originalKernelRResponse observation nontrivial half)-
    (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • pairedBurnolMultiplicativeDilation h
      (Return.sourceA observation • Paid.originalKernelRResponse observation nontrivial half)+
    (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
    Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
    Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h := by
      rw [map_smul]
      module
  _ = _ := by rw [actual_original_K_return]

/-- The ordinary zero source scalar keeps its exact returned primitive debt. -/
theorem actual_zero_sourceA_return (zero : Return.sourceA observation=0) :
 Return.primitiveSource observation nontrivial half=
 -(burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) := by
 have actual:=Return.original_return_source_equation observation nontrivial half
 rw [zero,zero_smul,zero_sub] at actual
 exact actual.symm

def scaledMaximalSource (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolL2 :=
 ((2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*pairedMellinTranslationCharacter (star observation.coordinate) h) • closedKernelSource observation nontrivial half-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • pairedBurnolMultiplicativeDilation h (closedKernelSource observation nontrivial half)+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
 Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
 Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h

private theorem actual_sourceA_pair_read (material : BurnolL2) :
 Paid.originalPairKernelRead observation nontrivial half (Return.sourceA observation • material)=
 -Return.sourceA observation*Paid.originalPairKernelRead observation nontrivial half material := by
 rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
 simp only [inner_smul_right,star_add,star_mul]
 rw [actual_sourceA_star]
 ring

private theorem actual_sourceA_sibling_read (material : BurnolL2) :
 Paid.originalSiblingKernelRead observation nontrivial half (Return.sourceA observation • material)=
 Return.sourceA observation*Paid.originalSiblingKernelRead observation nontrivial half material := by
 rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
 simp only [inner_smul_right]
 ring

theorem actual_kernel_cross_response_read (h : ℝ) :
 let characterPrice:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
   (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 Paid.originalKernelCross observation nontrivial half h=
 characterPrice*Paid.originalPairKernelRead observation nontrivial half
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))+
 star characterPrice*Paid.originalSiblingKernelRead observation nontrivial half
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h)) := by
 unfold OriginalKPairedResponseGramAction.originalKernelCross
   OriginalKPairedResponseGramAction.originalPairKernelRead OriginalKPairedResponseGramAction.originalSiblingKernelRead
 dsimp only
 unfold OriginalKFullSourceRResponse.pairedResponse OriginalKFullSourceRResponse.siblingResponse
 simp only [inner_smul_left,inner_smul_right,starRingEnd_apply]

/-- The scaled original character price is generated by the actual returned primitive, with both star directions retained. -/
theorem actual_scaled_original_kernel_cross (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let characterPrice:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
   (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 Return.sourceA observation*Paid.originalKernelCross observation nontrivial half h=
 -characterPrice*Paid.originalPairKernelRead observation nontrivial half (scaledMaximalSource observation nontrivial half h nonnegative bounded)+
 star characterPrice*Paid.originalSiblingKernelRead observation nontrivial half (scaledMaximalSource observation nontrivial half h nonnegative bounded) := by
 dsimp only
 have actual:=actual_scaled_complete_response observation nontrivial half h nonnegative bounded
 change Return.sourceA observation • OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h)=
   scaledMaximalSource observation nontrivial half h nonnegative bounded at actual
 rw [←actual,actual_sourceA_pair_read,actual_sourceA_sibling_read,actual_kernel_cross_response_read]
 ring

def originalForcingPair (h : ℝ) : BurnolL2 :=
 OriginalRieszFiniteSource.forcingIntegral (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h+
 OriginalRieszFiniteSource.forcingIntegral (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (-h)

def primitiveFiniteAction (h : ℝ) : BurnolL2 :=
 pairedMellinTranslationCharacter (star observation.coordinate) h • Return.primitiveSource observation nontrivial half-
 pairedBurnolMultiplicativeDilation h (Return.primitiveSource observation nontrivial half)

/-- Both actual original K finite actions are consumed before the primitive action is read. -/
theorem actual_original_K_finite_pair (h : ℝ) :
 pairedBurnolMultiplicativeDilation h
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)=
 pairedMellinTranslationCharacter (star observation.coordinate) h •
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)+
 (1/2:ℂ) • originalForcingPair observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have plus:=OriginalRieszFiniteSource.original_finite_action coordinate h
 have minus:=OriginalRieszFiniteSource.original_finite_action coordinate (-h)
 unfold pairedBurnolMultiplicativeDilation originalForcingPair pairedMellinTranslationCharacter
 simp only [smul_apply,add_apply]
 change (1/2:ℂ) • (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2)+
   burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector coordinate : BurnolL2))=_
 rw [plus,minus,OriginalKCombCofinalTwoDirection.coordinate_value,
   reciprocalMellinTranslationCharacter_eq_negativeShift]
 module

/-- The K finite forcing is generated by its source; the remaining primitive and projection stocks are retained. -/
theorem actual_scaled_source_finite_inventory (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 scaledMaximalSource observation nontrivial half h nonnegative bounded=
 -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • originalForcingPair observation nontrivial half h+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • primitiveFiniteAction observation nontrivial half h+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
 Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
 Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h := by
 unfold scaledMaximalSource closedKernelSource primitiveFiniteAction
 rw [map_add,actual_original_K_finite_pair]
 module


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
