import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Cross
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeRuntimeFace.Consumer
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRResponse.BoundaryUpdate
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
local instance consumerAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
namespace NF
export OriginalKNativeRuntimeFace (stoppingOffset frontier consume_actual_native_runtime)
end NF
local instance consumerNativeGroups (grade : Nat) (target : Unit) :
 AddCommGroup (OriginalKNativeRuntimeFace.L.Value (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
 OriginalKNativeRuntimeFace.L.groups (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade target

/-- Retain the actual paid proposition once, without reopening each dependent slot. -/
private def retain_paid_native {claim : Prop} (paid : claim) : PSigma (fun proposition : Prop=>proposition) := ⟨claim,paid⟩

def nativeReceipt (depth ordinal offset : Nat)
 (within : offset≤NF.stoppingOffset observation nontrivial half depth ordinal)
 (index : Fin ((NF.frontier observation nontrivial half depth ordinal).stageCount+1)) (shift : ℝ) :=
 retain_paid_native (NF.consume_actual_native_runtime observation nontrivial half depth ordinal offset within index shift)

theorem actual_native_receipt_scope (depth ordinal offset : Nat)
 (within : offset≤NF.stoppingOffset observation nontrivial half depth ordinal)
 (index : Fin ((NF.frontier observation nontrivial half depth ordinal).stageCount+1)) (shift : ℝ) :
 (nativeReceipt observation nontrivial half depth ordinal offset within index shift).1=
 (type_of% (NF.consume_actual_native_runtime observation nontrivial half depth ordinal offset within index shift)) := rfl

/-- The maximal source equation is consumed by Cross before this same-source native receipt is retained. -/
theorem consume_actual_response_evolution
 (depth ordinal offset : Nat)
 (within : offset≤NF.stoppingOffset observation nontrivial half depth ordinal)
 (index : Fin ((NF.frontier observation nontrivial half depth ordinal).stageCount+1)) (shift : ℝ)
 (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
 (type_of% (actual_original_complete_response_evolution observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_maximal_kernel_cross observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_original_character_inventory_ward observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_original_kernel_source_ward observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_original_wave_pair_price observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_original_wave_sibling_price observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_generated_flux_inventory observation nontrivial half h)) ∧
 (type_of% (OriginalKFullSourceRResponse.actual_complete_residual_forcing observation nontrivial half h)) ∧
 (type_of% (OriginalKFullSourceRResponse.actual_complete_native_update observation nontrivial half h nextShift nonnegative ordered)) ∧
 (type_of% (OriginalKFullSourceRResponse.actual_R_response_update observation nontrivial half h nextShift nonnegative ordered)) ∧
 (type_of% (OriginalKFullSourceRResponse.actual_original_residual_update observation nontrivial half h nextShift nonnegative ordered bounded)) ∧
 (nativeReceipt observation nontrivial half depth ordinal offset within index shift).1 :=
 ⟨actual_original_complete_response_evolution _ _ _ h nonnegative (ordered.trans bounded),
 actual_maximal_kernel_cross _ _ _ h nonnegative (ordered.trans bounded),
 actual_original_character_inventory_ward _ _ _ h nonnegative (ordered.trans bounded),
 actual_original_kernel_source_ward _ _ _ h nonnegative (ordered.trans bounded),
 actual_original_wave_pair_price _ _ _ h nonnegative (ordered.trans bounded),
 actual_original_wave_sibling_price _ _ _ h nonnegative (ordered.trans bounded),
 actual_generated_flux_inventory _ _ _ h,
 OriginalKFullSourceRResponse.actual_complete_residual_forcing _ _ _ h,
 OriginalKFullSourceRResponse.actual_complete_native_update _ _ _ h nextShift nonnegative ordered,
 OriginalKFullSourceRResponse.actual_R_response_update _ _ _ h nextShift nonnegative ordered,
 OriginalKFullSourceRResponse.actual_original_residual_update _ _ _ h nextShift nonnegative ordered bounded,
 (nativeReceipt _ _ _ depth ordinal offset within index shift).2⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPairedResponseGramAction"
