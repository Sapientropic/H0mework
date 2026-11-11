import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Controls
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalCalculatedSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision.DirectRDivisionControls
open Complex MeasureTheory Set Filter BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKDirectRCofinalMaterial
open OriginalKCombCofinalRAction
open scoped InnerProductSpace Topology
local instance sourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance sourceGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 Parent.L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

namespace FR
export OriginalKCombFullResidualAction.FR (jointCode joint_eval sourceInput completeInput physicalInput residualInput)
end FR
namespace Full
export OriginalKCombFullResidualAction (joint_source_value original_effect)
end Full
namespace CF
export OriginalKCombFullResidualAction.CF (codeAt collapseValue)
end CF
namespace P
export OriginalKCombFullResidualAction.P (code)
end P
namespace Calc
export OriginalKDirectRCofinalCalculatedSource
  (source_payload_literal actual_material_source_payload calculated_full_R_action
   calculated_target_raw_successor)
end Calc
namespace Pricing
export BurnolPhysicalState.CombSource.Pricing (ambient_R_scalar_action)
end Pricing

/-- The selected cofinal material carries the literal FullResidual source code at its exact D.raw occurrence. -/
theorem actual_source_action_code :
 let packet := Parent.D.packet observation nontrivial half depth ordinal
 let material := R.actualMaterial packet.2.1.1 packet.2.2.1
 HEq material.raw (CF.codeAt (FR.jointCode (P.code observation nontrivial half)) packet.1) := by
 have payload := Calc.source_payload_literal observation nontrivial half depth ordinal
 have material := Calc.actual_material_source_payload observation nontrivial half depth ordinal
 exact (heq_of_eq material.1).trans payload.1

/-- The original R scalar equation is generated from the same D.raw successor and the actual resolvent action. -/
theorem actual_source_scalar_action_generated (w : ℂ) (wRight : 1/4 < w.re)
 (wBelow : w.re < 1/2) :
 burnolAmbientCompletedMellinEvaluator
   (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
   (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)) =
 (-(1/(observation.coordinate/2+w-(1/2 : ℂ)))) *
 burnolAmbientCompletedMellinEvaluator
   (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
   (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal) := by
 rw [OriginalKCombFirstFullSourceDynamics.raw_successor,
   OriginalKCombCofinalRAction.original_R_direct]
 exact Pricing.ambient_R_scalar_action (observation.coordinate/2)
   (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)
   _ (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal)
   w wRight wBelow

/-- One generated bridge exposes source code, its actual R action/effect, scalar equation,
position-gap face and the successor raw; no receiver field or target is supplied. -/
theorem actual_division_source_bridge :
 type_of% (actual_source_action_code observation nontrivial half depth ordinal) ∧
 type_of% (Full.joint_source_value observation nontrivial half
   (FR.sourceInput 0 (Parent.D.initial observation nontrivial half depth))) ∧
 type_of% (Full.original_effect observation nontrivial half
   (FR.physicalInput (FR.completeInput
    (FR.sourceInput 0 (Parent.D.initial observation nontrivial half depth))))
   (FR.residualInput (FR.completeInput
    (FR.sourceInput 0 (Parent.D.initial observation nontrivial half depth))))) ∧
 type_of% (Calc.source_payload_literal observation nontrivial half depth ordinal) ∧
 type_of% (Calc.actual_material_source_payload observation nontrivial half depth ordinal) ∧
 type_of% (Calc.calculated_full_R_action observation nontrivial half depth ordinal) ∧
 type_of% (Calc.calculated_target_raw_successor observation nontrivial half depth ordinal) ∧
 type_of% (actual_source_scalar_action_generated observation nontrivial half depth ordinal
   (1/3 : ℂ) (by norm_num) (by norm_num)) ∧
 type_of% (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal) := by
 exact ⟨actual_source_action_code observation nontrivial half depth ordinal,
  Full.joint_source_value observation nontrivial half
   (FR.sourceInput 0 (Parent.D.initial observation nontrivial half depth)),
  Full.original_effect observation nontrivial half
   (FR.physicalInput (FR.completeInput
    (FR.sourceInput 0 (Parent.D.initial observation nontrivial half depth))))
   (FR.residualInput (FR.completeInput
    (FR.sourceInput 0 (Parent.D.initial observation nontrivial half depth)))),
  Calc.source_payload_literal observation nontrivial half depth ordinal,
  Calc.actual_material_source_payload observation nontrivial half depth ordinal,
  Calc.calculated_full_R_action observation nontrivial half depth ordinal,
  Calc.calculated_target_raw_successor observation nontrivial half depth ordinal,
  actual_source_scalar_action_generated observation nontrivial half depth ordinal
   (1/3 : ℂ) (by norm_num) (by norm_num),
  OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal⟩

/--
The original cofinal R action and its Division/position-gap read are consumed
at the same D.raw occurrence as the native relation/effect and whole/next.
The scalar action is kept as a source equation; no receiver field or target
value enters the constructor.
-/
theorem actual_division_action_same_root :
 type_of% (actual_source_scalar_action_generated observation nontrivial half depth ordinal
   (1/3 : ℂ) (by norm_num) (by norm_num)) ∧
 type_of% (source_response_positionGap observation nontrivial half depth ordinal) ∧
 type_of% (AN.new_relation_face
   (IC.selected (Parent.D.factory observation nontrivial half)
    (Parent.D.packet observation nontrivial half depth ordinal))) ∧
 type_of% (AN.new_full_trace
   (IC.selected (Parent.D.factory observation nontrivial half)
    (Parent.D.packet observation nontrivial half depth ordinal))) ∧
 type_of% (AN.new_relation_in_born
   (IC.selected (Parent.D.factory observation nontrivial half)
    (Parent.D.packet observation nontrivial half depth ordinal))
   (IC.nativePacket (Parent.D.factory observation nontrivial half)
    (Parent.D.packet observation nontrivial half depth ordinal)).2.2.1) ∧
 type_of% (F.actual_effect
   (R.actualMaterial (Parent.D.packet observation nontrivial half depth ordinal).2.1.1
    (Parent.D.packet observation nontrivial half depth ordinal).2.2.1)) ∧
 type_of% (F.relation_recovery
   (R.actualMaterial (Parent.D.packet observation nontrivial half depth ordinal).2.1.1
    (Parent.D.packet observation nontrivial half depth ordinal).2.2.1)) ∧
 type_of% (Parent.RC.original_whole (Parent.D.factory observation nontrivial half)
   (Parent.D.initial observation nontrivial half depth)
   (Parent.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Parent.RC.actual_generated_current (Parent.D.factory observation nontrivial half)
   (Parent.D.initial observation nontrivial half depth)
   (Parent.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKCombFirstFullSourceDynamics.next_pair observation nontrivial half depth ordinal) := by
 apply consume_actual_direct_R observation nontrivial half depth ordinal
 intro request model compiles whole material_increment material_input native_value native_expression
  old_paid_code old_paid_branches old_paid_R receipt_zero born_old_paid successor successor_paid_value
  successor_branches receiver_input receiver_ast native_packet receipt_bound receipt_action receipt_macro_next
  receipt_compiles born_ast decoder born_inventory born_pair_inventory source_word_inventory actual_next_packet
  old_events old_pair_events whole_paid_in_born generated_joint_in_born full_paid_steps source_boundary
  whole_paid_trace actual_inverse actual_effect relation_recovery native_full_trace native_relation_face
  native_relation_in_born root_generated_current rooted_material_source source_gap source_strong raw_successor
  next_pair full_history paid_prefix_stocks paid_prefix native_coordinate_zero root_future
 have bridge := actual_division_source_bridge observation nontrivial half depth ordinal
 exact ⟨bridge.2.2.2.2.2.2.2.1,
   source_response_positionGap observation nontrivial half depth ordinal,
   native_relation_face,native_full_trace,native_relation_in_born,actual_effect,relation_recovery,
   whole,root_generated_current,raw_successor,next_pair⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision.DirectRDivisionControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
