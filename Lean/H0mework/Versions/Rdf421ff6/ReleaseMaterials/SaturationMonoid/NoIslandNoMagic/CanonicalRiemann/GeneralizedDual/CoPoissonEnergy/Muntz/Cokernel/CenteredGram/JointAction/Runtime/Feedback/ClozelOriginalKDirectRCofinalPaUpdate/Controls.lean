import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalPaUpdate.Consumer
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "DirectRPaUpdateControls"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls
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

def actualEReturn : BurnolPaAmbientCarrier :=
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))

def bornRead : BurnolL2 :=
 let packet:=Parent.D.packet observation nontrivial half depth (ordinal+1)
 let value:=Parent.CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment () (),0)
 (value.1.1+value.1.2)+(value.2.1+value.2.2)

/-- The forced source is an E-read of this born value, with its own full E-return subtracted. -/
def bornForcedPa : BurnolPaAmbientCarrier := PA.E (bornRead observation nontrivial half depth ordinal)-actualEReturn observation nontrivial half depth ordinal

/-- The inverse fibre below belongs to the mathematical compressed Pa source carrier. -/
def BornPaFaceAt : Prop :=
 bornRead observation nontrivial half depth ordinal=(sourceCorrection observation nontrivial half depth ordinal : BurnolL2)+
  Parent.sourceCoefficient observation nontrivial half depth ordinal • (sourceWholeUnit observation nontrivial half : BurnolL2)+
  P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)) ∧
 PA.E (bornRead observation nontrivial half depth ordinal)=sourceCorrection observation nontrivial half depth ordinal+
  Parent.sourceCoefficient observation nontrivial half depth ordinal • PA.E (sourceWholeUnit observation nontrivial half : BurnolL2)+actualEReturn observation nontrivial half depth ordinal ∧
 burnolMobiusSourceL2 (PA.E (bornRead observation nontrivial half depth ordinal))=
  burnolMobiusSourceL2 (sourceCorrection observation nontrivial half depth ordinal)+
  Parent.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (sourceWholeUnit observation nontrivial half : BurnolL2))+
  burnolMobiusSourceL2 (actualEReturn observation nontrivial half depth ordinal) ∧
 bornForcedPa observation nontrivial half depth ordinal=sourceCorrection observation nontrivial half depth ordinal+
  Parent.sourceCoefficient observation nontrivial half depth ordinal • PA.E (sourceWholeUnit observation nontrivial half : BurnolL2) ∧
 Paid.compressedR observation nontrivial half (actualPaSource observation nontrivial half depth ordinal)=bornForcedPa observation nontrivial half depth ordinal ∧
 type_of% (actual_original_unit_rank observation nontrivial half depth ordinal) ∧
 -(inner ℂ (bornForcedPa observation nontrivial half depth ordinal) (PA.actualPa observation nontrivial half depth ordinal)).re=
  (observation.coordinate/2-1/4).re *
   (‖bornForcedPa observation nontrivial half depth ordinal‖^2+‖Previous.sourceCoefficient observation nontrivial half depth ordinal • Previous.sourceUnit observation nontrivial half‖^2) ∧
 (∀ candidate : Paid.PaSourceCarrier,
  Paid.compressedR observation nontrivial half candidate=bornForcedPa observation nontrivial half depth ordinal→candidate=actualPaSource observation nontrivial half depth ordinal) ∧
 (observation.coordinate/2-1/4).re *
  (‖bornForcedPa observation nontrivial half depth ordinal‖^2+‖Previous.sourceCoefficient observation nontrivial half depth ordinal • Previous.sourceUnit observation nontrivial half‖^2)≤
  ‖bornForcedPa observation nontrivial half depth ordinal‖ * ‖PA.actualPa observation nontrivial half depth ordinal‖

theorem whole_unit_preprojection_zero : burnolMobiusSourceL2 (sourceWholeUnit observation nontrivial half)=0 :=
 burnolZeroOwnedUnitTailState_finiteSource_zero observation nontrivial half.down

theorem preprojection_zero_not_after_projection :
 let unit : (ℂ × ℂ) :=(1,-1)
 let project : (ℂ × ℂ)→(ℂ × ℂ) :=fun value=>(value.1,0)
 let mobius : (ℂ × ℂ) → ℂ :=fun value=>value.1+value.2
 mobius unit=0 ∧ mobius (project unit)≠0 ∧ project (project unit)=project unit := by
 norm_num

theorem complete_return_not_physical_Q_return :
 let returning : (ℂ × ℂ) :=(1,0)
 let E : (ℂ × ℂ)→(ℂ × ℂ) :=fun value=>(value.1,0)
 let Q : (ℂ × ℂ)→(ℂ × ℂ) :=fun value=>(0,value.2)
 E returning≠0 ∧ Q returning=0 ∧ E returning+Q returning=returning := by
 norm_num

theorem zero_coefficient_preserves_correction_and_return (zero : Parent.sourceCoefficient observation nontrivial half depth ordinal=0) :
 PA.actualPa observation nontrivial half depth (ordinal+1)=sourceCorrection observation nontrivial half depth ordinal+actualEReturn observation nontrivial half depth ordinal := by
 have actual:=actual_Pa_source_successor observation nontrivial half depth ordinal
 rw [zero,zero_smul,add_zero] at actual
 exact actual

theorem zero_Ereturn_preserves_Eunit (zero : actualEReturn observation nontrivial half depth ordinal=0) :
 PA.actualPa observation nontrivial half depth (ordinal+1)=sourceCorrection observation nontrivial half depth ordinal+
 Parent.sourceCoefficient observation nontrivial half depth ordinal • PA.E (sourceWholeUnit observation nontrivial half : BurnolL2) := by
 have actual:=actual_Pa_source_successor observation nontrivial half depth ordinal
 change PA.actualPa _ _ _ _ _=sourceCorrection observation nontrivial half depth ordinal+
  Parent.sourceCoefficient observation nontrivial half depth ordinal • PA.E (sourceWholeUnit observation nontrivial half : BurnolL2)+actualEReturn observation nontrivial half depth ordinal at actual
 rw [zero,add_zero] at actual
 exact actual

theorem actual_Mobius_Efoot_and_return :
 type_of% (actual_Mobius_source_successor observation nontrivial half depth ordinal) ∧ type_of% (source_correction_finite_source observation nontrivial half depth ordinal) :=
 ⟨actual_Mobius_source_successor observation nontrivial half depth ordinal,source_correction_finite_source observation nontrivial half depth ordinal⟩

theorem actual_inverse_targets_actual_source (candidate : Paid.PaSourceCarrier)
 (produces : Paid.compressedR observation nontrivial half candidate=forcedPaSource observation nontrivial half depth ordinal) :
 candidate=actualPaSource observation nontrivial half depth ordinal := actual_forced_Pa_inverse observation nontrivial half depth ordinal candidate produces

/-- Every Pa and inverse/energy statement is evaluated on the same original born E-read. -/
theorem actual_born_Pa_same_whole :
 type_of% (source_correction_memPa observation nontrivial half depth ordinal) ∧ type_of% (source_correction_finite_source observation nontrivial half depth ordinal) ∧
 BornPaFaceAt observation nontrivial half depth ordinal ∧
 type_of% (OriginalKDirectRCofinalResidual.actual_residual_successor observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalResidual.actual_residual_inventory observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalResidual.actual_reentry_successor observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_original_FourierK_read observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_Q_complete_gram observation nontrivial half depth ordinal) ∧
 type_of% (Parent.RC.original_whole (Parent.D.factory observation nontrivial half) (Parent.D.initial observation nontrivial half depth) (Parent.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Parent.RC.actual_generated_current (Parent.D.factory observation nontrivial half) (Parent.D.initial observation nontrivial half depth) (Parent.D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) ∧
 type_of% (Parent.consumed_request_source observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalMaterial.actual_native_value observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalMaterial.actual_successor observation nontrivial half depth ordinal) := by
 apply consume_actual_Pa_source observation nontrivial half depth ordinal
 intro correction_memPa whole_source Pa_source Mobius_source finite_source compressed_source forced_complete unit_rank forced_energy forced_inverse forced_cost
  residual_successor residual_inventory reentry_successor response_value response_gap response_Q source_R_split Q_successor K_read FourierK_read complete_gram request model compiles whole material_increment material_input native_value native_expression old_paid_code old_paid_branches old_paid_R receipt_zero born_old_paid successor successor_paid_value successor_branches receiver_input receiver_ast native_packet receipt_bound receipt_action receipt_macro_next receipt_compiles born_ast decoder born_inventory born_pair_inventory source_word_inventory actual_next_packet old_events old_pair_events whole_paid_in_born generated_joint_in_born full_paid_steps source_boundary whole_paid_trace actual_inverse actual_effect relation_recovery native_full_trace native_relation_face native_relation_in_born root_generated_current rooted_material_source source_gap source_strong raw_successor next_pair full_history paid_prefix_stocks paid_prefix native_coordinate_zero root_future
 have calculated:=Parent.Full.complete_of_branches observation nontrivial half _ _ successor_branches
 have bornR : bornRead observation nontrivial half depth ordinal=P.R observation nontrivial half (D.raw observation nontrivial half depth ordinal) := calculated.2.2.1
 have raw : bornRead observation nontrivial half depth ordinal=D.raw observation nontrivial half depth (ordinal+1) := bornR.trans raw_successor.symm
 have bornWhole:=raw.trans whole_source
 have samePa:=congrArg PA.E raw
 have bornPa:=samePa.trans Pa_source
 have bornMobius:=(congrArg burnolMobiusSourceL2 samePa).trans Mobius_source
 have forced : bornForcedPa observation nontrivial half depth ordinal=forcedPaSource observation nontrivial half depth ordinal :=
  congrArg (fun material : BurnolPaAmbientCarrier=>material-actualEReturn observation nontrivial half depth ordinal) samePa
 have bornComplete:=forced.trans forced_complete
 have bornCompressed:=compressed_source.trans forced.symm
 have bornEnergy:=forced_energy
 rw [←forced] at bornEnergy
 have bornCost:=forced_cost
 rw [←forced] at bornCost
 have fibre : ∀ candidate : Paid.PaSourceCarrier,
  Paid.compressedR observation nontrivial half candidate=bornForcedPa observation nontrivial half depth ordinal→candidate=actualPaSource observation nontrivial half depth ordinal :=
  fun candidate produces=>forced_inverse candidate (produces.trans forced)
 exact ⟨correction_memPa,finite_source,
  ⟨bornWhole,bornPa,bornMobius,bornComplete,bornCompressed,unit_rank,bornEnergy,fibre,bornCost⟩,
  residual_successor,residual_inventory,reentry_successor,K_read,FourierK_read,complete_gram,
  whole,root_generated_current,Parent.consumed_request_source observation nontrivial half depth ordinal,native_value,successor⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
