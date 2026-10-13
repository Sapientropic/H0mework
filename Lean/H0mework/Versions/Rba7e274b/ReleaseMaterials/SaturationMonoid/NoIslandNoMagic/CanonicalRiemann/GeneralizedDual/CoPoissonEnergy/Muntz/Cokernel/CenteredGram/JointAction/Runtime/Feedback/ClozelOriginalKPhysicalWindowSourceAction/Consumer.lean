import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Character
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance projectionConsumerComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local instance physicalWindowNativeGroups (grade : Nat) (target : Unit) :
  AddCommGroup (OriginalKNativeRuntimeFace.L.Value (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  OriginalKNativeRuntimeFace.L.groups (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade target


/-- The actual physical moving-window action feeds the complete original prices and current Cross; prior whole/native source proofs are retained. -/
theorem consume_actual_original_physical_window_source_action
 (depth ordinal offset : Nat)
 (within : offset ≤ OriginalKNativeRuntimeFace.stoppingOffset observation nontrivial half depth ordinal)
 (index : Fin ((OriginalKNativeRuntimeFace.frontier observation nontrivial half depth ordinal).stageCount+1))
 (n : Nat) (shift : ℝ) (shiftPositive : 0 < shift)
 (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) (bounded : nextShift ≤ Real.log 2)
 (test : SchwartzMap ℝ ℂ)
 (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice : ℂ) :
 (type_of% (actual_original_R_source_raw observation nontrivial half h)) ∧
 (type_of% (actual_original_R_raw_continuous observation nontrivial half h)) ∧
 (type_of% (actual_original_F_R_source observation nontrivial half h)) ∧
 (type_of% (actual_original_pair_sibling_full_source_raw observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_physical_pair_sibling_source_raw observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_physical_source_outer_continuous observation nontrivial half h)) ∧
 (type_of% (actual_physical_moving_window_action observation nontrivial half h nonnegative (ordered.trans bounded) shift shiftPositive)) ∧
 (type_of% (actual_physical_moving_window_finite_action observation nontrivial half h nonnegative (ordered.trans bounded) shift shiftPositive.le)) ∧
 (type_of% (actual_physical_moving_window_read observation nontrivial half h nonnegative (ordered.trans bounded) shift)) ∧
 (type_of% (actual_physical_seed_window_price observation nontrivial half h nonnegative (ordered.trans bounded) shift shiftPositive.le)) ∧
 (type_of% (actual_physical_pair_sibling_fourier observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_physical_four_contact_window_price observation nontrivial half h nonnegative (ordered.trans bounded) h nonnegative)) ∧
 (type_of% (actual_physical_four_generated_contact_price observation nontrivial half h nonnegative (ordered.trans bounded) h nonnegative)) ∧
 (type_of% (actual_boundary_integral_consumes_physical_windows observation nontrivial half h nonnegative (ordered.trans bounded) h nonnegative)) ∧
 (type_of% (actual_full_boundary_consumes_physical_windows observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_original_cross_consumes_physical_window_action observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (actual_current_character_consumes_physical_window_action observation nontrivial half h nonnegative (ordered.trans bounded) n)) ∧
 (type_of% (actual_physical_window_source_character_closure observation nontrivial half h nonnegative (ordered.trans bounded))) ∧
 (type_of% (OriginalKBoundarySourceAction.consume_actual_original_boundary_source_action observation nontrivial half depth ordinal offset within index n shift shiftPositive.le h nextShift nonnegative ordered bounded test kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice)) :=
 ⟨actual_original_R_source_raw observation nontrivial half h,
 actual_original_R_raw_continuous observation nontrivial half h,
 actual_original_F_R_source observation nontrivial half h,
 actual_original_pair_sibling_full_source_raw observation nontrivial half h nonnegative (ordered.trans bounded),
 actual_physical_pair_sibling_source_raw observation nontrivial half h nonnegative (ordered.trans bounded),
 actual_physical_source_outer_continuous observation nontrivial half h,
 actual_physical_moving_window_action observation nontrivial half h nonnegative (ordered.trans bounded) shift shiftPositive,
 actual_physical_moving_window_finite_action observation nontrivial half h nonnegative (ordered.trans bounded) shift shiftPositive.le,
 actual_physical_moving_window_read observation nontrivial half h nonnegative (ordered.trans bounded) shift,
 actual_physical_seed_window_price observation nontrivial half h nonnegative (ordered.trans bounded) shift shiftPositive.le,
 actual_physical_pair_sibling_fourier observation nontrivial half h nonnegative (ordered.trans bounded),
 actual_physical_four_contact_window_price observation nontrivial half h nonnegative (ordered.trans bounded) h nonnegative,
 actual_physical_four_generated_contact_price observation nontrivial half h nonnegative (ordered.trans bounded) h nonnegative,
 actual_boundary_integral_consumes_physical_windows observation nontrivial half h nonnegative (ordered.trans bounded) h nonnegative,
 actual_full_boundary_consumes_physical_windows observation nontrivial half h nonnegative (ordered.trans bounded),
 actual_original_cross_consumes_physical_window_action observation nontrivial half h nonnegative (ordered.trans bounded),
 actual_current_character_consumes_physical_window_action observation nontrivial half h nonnegative (ordered.trans bounded) n,
 actual_physical_window_source_character_closure observation nontrivial half h nonnegative (ordered.trans bounded),
 OriginalKBoundarySourceAction.consume_actual_original_boundary_source_action observation nontrivial half depth ordinal offset within index n shift shiftPositive.le h nextShift nonnegative ordered bounded test kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
