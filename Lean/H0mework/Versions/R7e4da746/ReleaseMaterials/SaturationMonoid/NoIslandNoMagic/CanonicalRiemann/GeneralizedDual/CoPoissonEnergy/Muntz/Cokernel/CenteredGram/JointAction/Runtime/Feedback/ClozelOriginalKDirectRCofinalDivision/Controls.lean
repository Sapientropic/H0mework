import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Consumer
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "DirectRDivisionControls"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision.DirectRDivisionControls
open Complex MeasureTheory Set Filter BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open scoped InnerProductSpace Topology
local instance controlsComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance controlsGroups (grade : Nat) : ∀ target,AddCommGroup (Parent.L.Value (PairValue Parent.C.Value) grade target) :=
 Parent.L.groups (PairValue Parent.C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- Complete four-branch read of the original actual successor packet. -/
def bornRead : BurnolL2 :=
 let packet:=Parent.D.packet observation nontrivial half depth (ordinal+1)
 let value:=Parent.CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment () (),0)
 (value.1.1+value.1.2)+(value.2.1+value.2.2)

/-- Q, both fixed K probes and the full Gram are restrictions of this actual born value. -/
def BornDivisionFaceAt : Prop :=
 PA.Q (bornRead observation nontrivial half depth ordinal)=
  sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half+sourceReturn observation nontrivial half depth ordinal ∧
 inner ℂ (K.originalK observation nontrivial half)
  (PA.Q (bornRead observation nontrivial half depth ordinal) : BurnolL2)=
  sourceCoefficient observation nontrivial half depth ordinal * inner ℂ (K.originalK observation nontrivial half)
   (sourceUnit observation nontrivial half : BurnolL2)+
  inner ℂ (K.originalK observation nontrivial half) (sourceReturn observation nontrivial half depth ordinal : BurnolL2) ∧
 inner ℂ (K.originalFourierK observation nontrivial half)
  (PA.Q (bornRead observation nontrivial half depth ordinal) : BurnolL2)=
  sourceCoefficient observation nontrivial half depth ordinal * inner ℂ (K.originalFourierK observation nontrivial half)
   (sourceUnit observation nontrivial half : BurnolL2)+
  inner ℂ (K.originalFourierK observation nontrivial half) (sourceReturn observation nontrivial half depth ordinal : BurnolL2) ∧
 ‖PA.Q (bornRead observation nontrivial half depth ordinal)‖^2=
  ‖sourceCoefficient observation nontrivial half depth ordinal‖^2 * ‖sourceUnit observation nontrivial half‖^2+
   2*(inner ℂ (sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half)
    (sourceReturn observation nontrivial half depth ordinal)).re+‖sourceReturn observation nontrivial half depth ordinal‖^2

theorem actual_source_Pa_lineage :
 PA.actualPa observation nontrivial half depth ordinal=PA.E (D.raw observation nontrivial half depth ordinal) ∧ type_of% (PA.actualPa_mem observation nontrivial half depth ordinal) :=
 ⟨rfl,PA.actualPa_mem observation nontrivial half depth ordinal⟩

theorem explicit_return_zero_override (zero : sourceReturn observation nontrivial half depth ordinal=0) :
 PA.Q (D.raw observation nontrivial half depth (ordinal+1))=
 sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half := by
 have actual:=actual_Q_successor observation nontrivial half depth ordinal
 change PA.Q _=sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half+sourceReturn observation nontrivial half depth ordinal at actual
 rw [zero,add_zero] at actual
 exact actual

theorem zero_coefficient_preserves_return (zero : sourceCoefficient observation nontrivial half depth ordinal=0) :
 PA.Q (D.raw observation nontrivial half depth (ordinal+1))=sourceReturn observation nontrivial half depth ordinal ∧
 ‖PA.Q (D.raw observation nontrivial half depth (ordinal+1))‖^2=‖sourceReturn observation nontrivial half depth ordinal‖^2 := by
 have actual:=actual_Q_successor observation nontrivial half depth ordinal
 change PA.Q _=sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half+sourceReturn observation nontrivial half depth ordinal at actual
 rw [zero,zero_smul,zero_add] at actual
 exact ⟨actual,congrArg (fun value : BurnolPaAmbientCarrier=>‖value‖^2) actual⟩

theorem cancellation_counterexample :
 (1 : ℂ)≠0 ∧ (1 : ℂ)≠0 ∧ (-1 : ℂ)≠0 ∧ (1 : ℂ) • (1 : ℂ)+(-1 : ℂ)=0 := by
 norm_num

theorem physical_unit_return_cancellation (unit : BurnolPaAmbientCarrier) (nonzero : unit≠0) :
 (1 : ℂ)≠0 ∧ -unit≠0 ∧ (1 : ℂ) • unit+(-unit)=0 :=
 ⟨one_ne_zero,neg_ne_zero.mpr nonzero,by simp only [one_smul,add_neg_cancel]⟩

theorem fixed_K_FourierK_complete_gram :
 type_of% (actual_original_K_read observation nontrivial half depth ordinal) ∧ type_of% (actual_original_FourierK_read observation nontrivial half depth ordinal) ∧
 type_of% (actual_Q_complete_gram observation nontrivial half depth ordinal) :=
 ⟨actual_original_K_read observation nontrivial half depth ordinal,actual_original_FourierK_read observation nontrivial half depth ordinal,actual_Q_complete_gram observation nontrivial half depth ordinal⟩

/-- This independent consumer computes Q on the same actual born branches and uses its original whole-next. -/
theorem actual_born_division_same_whole :
 type_of% (source_response_value observation nontrivial half depth ordinal) ∧ type_of% (source_response_positionGap observation nontrivial half depth ordinal) ∧
 type_of% (source_response_Q observation nontrivial half depth ordinal) ∧ type_of% (actual_R_source_split observation nontrivial half depth ordinal) ∧
 BornDivisionFaceAt observation nontrivial half depth ordinal ∧
 type_of% (Parent.RC.original_whole (Parent.D.factory observation nontrivial half) (Parent.D.initial observation nontrivial half depth) (Parent.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Parent.RC.actual_generated_current (Parent.D.factory observation nontrivial half) (Parent.D.initial observation nontrivial half depth) (Parent.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Parent.consumed_request_source observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalMaterial.actual_native_value observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalMaterial.actual_successor observation nontrivial half depth ordinal) := by
 apply consume_actual_source_Q observation nontrivial half depth ordinal
 intro response_value response_gap response_Q source_R_split Q_successor K_read FourierK_read complete_gram
  request model compiles whole material_increment material_input native_value native_expression old_paid_code old_paid_branches old_paid_R receipt_zero born_old_paid successor successor_paid_value successor_branches receiver_input receiver_ast native_packet receipt_bound receipt_action receipt_macro_next receipt_compiles born_ast decoder born_inventory born_pair_inventory source_word_inventory actual_next_packet old_events old_pair_events whole_paid_in_born generated_joint_in_born full_paid_steps source_boundary whole_paid_trace actual_inverse actual_effect relation_recovery native_full_trace native_relation_face native_relation_in_born root_generated_current rooted_material_source source_gap source_strong raw_successor next_pair full_history paid_prefix_stocks paid_prefix native_coordinate_zero root_future
 have calculated:=Parent.Full.complete_of_branches observation nontrivial half _ _ successor_branches
 have bornR : bornRead observation nontrivial half depth ordinal=P.R observation nontrivial half (D.raw observation nontrivial half depth ordinal) := calculated.2.2.1
 have raw : bornRead observation nontrivial half depth ordinal=D.raw observation nontrivial half depth (ordinal+1) :=
  bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have sameQ:=congrArg PA.Q raw
 have bornQ:=sameQ.trans Q_successor
 have bornK:=(congrArg (fun value : BurnolPaAmbientCarrier=>
  inner ℂ (K.originalK observation nontrivial half) (value : BurnolL2)) sameQ).trans K_read
 have bornFourierK:=(congrArg (fun value : BurnolPaAmbientCarrier=>
  inner ℂ (K.originalFourierK observation nontrivial half) (value : BurnolL2)) sameQ).trans FourierK_read
 have bornGram:=(congrArg (fun value : BurnolPaAmbientCarrier=>‖value‖^2) sameQ).trans complete_gram
 exact ⟨response_value,response_gap,response_Q,source_R_split,
  ⟨bornQ,bornK,bornFourierK,bornGram⟩,whole,root_generated_current,
  Parent.consumed_request_source observation nontrivial half depth ordinal,native_value,successor⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision.DirectRDivisionControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
