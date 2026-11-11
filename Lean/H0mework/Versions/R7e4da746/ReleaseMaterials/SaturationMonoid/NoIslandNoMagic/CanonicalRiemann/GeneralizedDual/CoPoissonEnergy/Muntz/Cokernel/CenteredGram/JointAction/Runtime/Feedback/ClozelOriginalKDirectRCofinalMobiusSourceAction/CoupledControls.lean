import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.CoupledConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.Controls
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "DirectRCoupledSourceControls"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction.DirectRCoupledSourceControls
open Complex MeasureTheory Set Filter BurnolPhysicalState
open BurnolPhysicalState.OriginalPaPhysicalGreen
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open scoped InnerProductSpace Topology
open DirectRQueryVolterraControls
local instance coupledControlsComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance coupledControlsGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The complete generated reentry vector is read on the same actual born; the whole residual ledger remains intact. -/
def CoupledBornAt : Prop :=
 type_of% (actual_reentry_vector_memPa observation half) ∧
 type_of% (actual_reentry_pairing observation nontrivial half depth ordinal) ∧
 type_of% (actual_reentry_pairing_next_inventory observation nontrivial half depth ordinal) ∧
 PA.E (PC.bornRead observation nontrivial half depth ordinal)=actualQueryCorrection observation nontrivial half depth ordinal+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 actualReentryPairing observation nontrivial half depth ordinal • actualReentryVector observation half ∧
 burnolMobiusSourceL2 (PA.E (PC.bornRead observation nontrivial half depth ordinal))=
 burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (actualQueryTate observation nontrivial half depth ordinal))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
 actualReentryPairing observation nontrivial half depth ordinal • burnolMobiusSourceL2 (actualReentryVector observation half) ∧
 burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (PC.bornRead observation nontrivial half depth ordinal)))=
 sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (actualQueryTate observation nontrivial half depth ordinal)+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)))+
 actualReentryPairing observation nontrivial half depth ordinal • burnolTateReciprocalL2 (burnolMobiusSourceL2 (actualReentryVector observation half)) ∧
 OriginalKDirectRCofinalSourceAction.CanonicalBornSourceAt observation nontrivial half depth ordinal ∧
 type_of% (Prior.RC.original_whole (Prior.D.factory observation nontrivial half) (Prior.D.initial observation nontrivial half depth) (Prior.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Prior.RC.actual_generated_current (Prior.D.factory observation nontrivial half) (Prior.D.initial observation nontrivial half depth) (Prior.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Prior.consumed_request_source observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalMaterial.actual_native_value observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalMaterial.actual_successor observation nontrivial half depth ordinal)

theorem generated_vector_has_full_Pa_qualification : type_of% (actual_reentry_vector_memPa observation half) := actual_reentry_vector_memPa observation half

theorem full_invisible_pairing_retains_both_inventories :
 type_of% (actual_reentry_pairing observation nontrivial half depth ordinal) ∧ type_of% (actual_reentry_pairing_next_inventory observation nontrivial half depth ordinal) :=
 ⟨actual_reentry_pairing observation nontrivial half depth ordinal,actual_reentry_pairing_next_inventory observation nontrivial half depth ordinal⟩

theorem zero_unit_coefficient_retains_Volterra_and_reentry (zero : Prior.sourceCoefficient observation nontrivial half depth ordinal=0) :
 actualQuerySource observation nontrivial half depth (ordinal+1)=
 burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (actualQueryTate observation nontrivial half depth ordinal))+
 actualReentryPairing observation nontrivial half depth ordinal • burnolMobiusSourceL2 (actualReentryVector observation half) := by
 have generated:=actual_query_source_coupled observation nontrivial half depth ordinal
 rw [zero,zero_smul,add_zero] at generated
 exact generated

theorem zero_pairing_retains_Volterra_and_Eunit (zero : actualReentryPairing observation nontrivial half depth ordinal=0) :
 actualQuerySource observation nontrivial half depth (ordinal+1)=
 burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (actualQueryTate observation nontrivial half depth ordinal))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)) := by
 have generated:=actual_query_source_coupled observation nontrivial half depth ordinal
 rw [zero,zero_smul,add_zero] at generated
 exact generated

theorem outside_pairing_cannot_be_dropped :
 let physical : (ℂ × ℂ) := (1,0)
 let outside : (ℂ × ℂ) := (0,1)
 let read : (ℂ × ℂ) → ℂ := fun input=>input.1+input.2
 read (physical+outside)=2 ∧ read physical=1 ∧ read outside=1 ∧ read (physical+outside)≠read physical := by norm_num

theorem nonzero_source_feet_can_cancel :
 let unitFoot : ℂ := 1
 let reentryFoot : ℂ := -1
 unitFoot≠0 ∧ reentryFoot≠0 ∧ unitFoot+reentryFoot=0 := by norm_num

theorem original_whole_and_full_residual_retained :
 type_of% (actual_whole_successor_from_face observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalResidual.actual_residual_inventory observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_original_FourierK_read observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_Q_complete_gram observation nontrivial half depth ordinal) :=
 ⟨actual_whole_successor_from_face observation nontrivial half depth ordinal,OriginalKDirectRCofinalResidual.actual_residual_inventory observation nontrivial half depth ordinal,
 OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal,OriginalKDirectRCofinalDivision.actual_original_FourierK_read observation nontrivial half depth ordinal,
 OriginalKDirectRCofinalDivision.actual_Q_complete_gram observation nontrivial half depth ordinal⟩

set_option maxHeartbeats 2500000 in
/-- The already-paid query/Volterra face is reused, while the new whole-Pa action is evaluated on this callback's actual born. -/
theorem actual_coupled_source_same_born_whole :
 CoupledBornAt observation nontrivial half depth ordinal ∧ QueryVolterraBornAt observation nontrivial half depth ordinal ∧ BornCofinalFaceAt observation nontrivial half depth ordinal ∧ InheritedBornAt observation nontrivial half depth ordinal := by
 refine consume_actual_coupled_source observation nontrivial half depth ordinal
  (Result:=CoupledBornAt observation nontrivial half depth ordinal ∧ QueryVolterraBornAt observation nontrivial half depth ordinal ∧ BornCofinalFaceAt observation nontrivial half depth ordinal ∧ InheritedBornAt observation nontrivial half depth ordinal) ?_
 intro reentry_memPa reentry_actual reentry_inventory coupled_Pa coupled_source coupled_Tate
  query_history query_root query_trace query_point query_reads query_image query_source query_integral query_memPa query_Tate_source query_correction query_whole query_Pa query_next_source query_next_Tate born_projection source_root source_trace source_paid_trace source_input source_point cofinal_injective cofinal_reads cofinal_action window_transitions face_image face_decoder face_inverse_decoder face_action face_inverse_action correction_memPa whole_source Pa_source Mobius_source finite_source compressed_source forced_complete unit_rank forced_energy forced_inverse forced_cost residual_successor residual_inventory reentry_successor response_value response_gap response_Q source_R_split Q_successor K_read FourierK_read complete_gram request model compiles whole material_increment material_input native_value native_expression old_paid_code old_paid_branches old_paid_R receipt_zero born_old_paid successor successor_paid_value successor_branches receiver_input receiver_ast native_packet receipt_bound receipt_action receipt_macro_next receipt_compiles born_ast decoder born_inventory born_pair_inventory source_word_inventory actual_next_packet old_events old_pair_events whole_paid_in_born generated_joint_in_born full_paid_steps source_boundary whole_paid_trace actual_inverse actual_effect relation_recovery native_full_trace native_relation_face native_relation_in_born root_generated_current rooted_material_source source_gap source_strong raw_successor next_pair full_history paid_prefix_stocks paid_prefix native_coordinate_zero root_future
 have base:=DirectRQueryVolterraControls.actual_query_Volterra_same_born_whole observation nontrivial half depth ordinal
 have queryFace:=base.1
 rcases queryFace with ⟨inputHistory,inputRoot,inputTrace,inputPoint,inputReads,inputImage,inputSource,inputIntegral,inputPa,inputTate,inputCorrection,inputPaid,inputWhole,inputPaBorn,inputMobius,inputTateBorn,sourceBorn⟩
 have calculated:=Prior.Full.complete_of_branches observation nontrivial half _ _ successor_branches
 have bornR : PC.bornRead observation nontrivial half depth ordinal=P.R observation nontrivial half (D.raw observation nontrivial half depth ordinal) := calculated.2.2.1
 have raw : PC.bornRead observation nontrivial half depth ordinal=D.raw observation nontrivial half depth (ordinal+1) := bornR.trans raw_successor.symm
 have bornPa:=(congrArg PA.E raw).trans coupled_Pa
 have bornSource:=sourceBorn.symm.trans coupled_source
 have bornTateRead : actualQueryTate observation nontrivial half depth (ordinal+1)=
  burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (PC.bornRead observation nontrivial half depth ordinal))) := congrArg burnolTateReciprocalL2 sourceBorn
 have bornTate:=bornTateRead.symm.trans coupled_Tate
 have anchored:=born_projection successor
 exact ⟨⟨reentry_memPa,reentry_actual,reentry_inventory,bornPa,bornSource,bornTate,anchored,whole,root_generated_current,
  Prior.consumed_request_source observation nontrivial half depth ordinal,native_value,successor⟩,base⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction.DirectRCoupledSourceControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
