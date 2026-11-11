import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Whole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.SourceEnergy
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open Complex BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance consumerSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (source : Branches) (shift : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

theorem consume_split_source_receipt {Target : Prop}
 (consumer : (whole : type_of% (sourceWholeAt source shift producer packet)) →
 (write : type_of% (actual_born_split_increment source shift (splitFactory producer)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (packet.2.2.2.down.symm ▸ ()))) →
 (effect : type_of% (actual_material_stock_effect source shift producer
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) →
 (trace : type_of% (sourceActorGradedTrace source shift (splitFactory producer)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (sourceSelectedAt source shift producer packet))) → Target) : Target :=
 consumer (sourceWholeAt source shift producer packet)
  (actual_born_split_increment source shift (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down _)
  (actual_material_stock_effect source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
  (sourceActorGradedTrace source shift (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down _)

theorem received_whole_split_source_next :
 ∃ whole : type_of% (sourceWholeAt source shift producer packet),
 (type_of% whole.actual_step) ∧ (type_of% whole.payment.strictDebit) ∧
 (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧ (type_of% whole.entry) ∧
 (type_of% whole.whole_destination) ∧ (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (source_born_root source shift producer packet)) ∧ (type_of% (source_born_current source shift producer packet)) ∧
 (type_of% (actual_born_split_increment source shift (splitFactory producer)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (packet.2.2.2.down.symm ▸ ()))) ∧
 (type_of% (actual_material_stock_effect source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) ∧
 (type_of% (received_born_current_source source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
  (actual_born_split_increment source shift (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down _)
  (actual_material_stock_effect source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down))) ∧
 fullSplitBudget (writtenSourceSplit source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)=
  fullSplitBudget (splitAction 0 source) ∧
 (type_of% (source_emitter_full_trace_inventory source shift (splitFactory producer)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (sourceSelectedAt source shift producer packet))) ∧
 (type_of% (source_emitter_calculation_trace_pair_inventory source shift (splitFactory producer)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (sourceSelectedAt source shift producer packet))) ∧
 (type_of% (actual_stock_receipt_low_stock source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) ∧
 (type_of% (received_actual_material_trace_effect source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) ∧
 (type_of% (sourceActorGradedTrace source shift (splitFactory producer)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (sourceSelectedAt source shift producer packet)).sound) := by
 exact consume_split_source_receipt source shift producer packet fun whole write effect trace =>
  ⟨whole,whole.actual_step,whole.payment.strictDebit,whole.same_ledger,whole.same_visit,whole.entry,
   whole.whole_destination,whole.source_environment,whole.source_expression,source_born_root source shift producer packet,
   source_born_current source shift producer packet,write,effect,
   received_born_current_source source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down write effect,
   received_full_source_budget source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down write effect,
   source_emitter_full_trace_inventory source shift (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down _,
   source_emitter_calculation_trace_pair_inventory source shift (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down _,
   actual_stock_receipt_low_stock source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   received_actual_material_trace_effect source shift producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,trace.sound⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

theorem actual_received_whole_split_source_next (shift : ℝ) : type_of% (received_whole_split_source_next
 (actualSourceMaterial observation nontrivial half depth ordinal h H N radius) shift
 (actualParentFactory observation nontrivial half depth ordinal h)
 (actualParentPacket observation nontrivial half depth ordinal h H N radius)) :=
 received_whole_split_source_next _ _ _ _

/-- The received actual write/effect recovers this source family; local energy comes from its source action, with no extra time-event claim. -/
theorem actual_received_source_debt_transfer (shift : ℝ) :
 let source := actualSourceMaterial observation nontrivial half depth ordinal h H N radius
 let factory := actualParentFactory observation nontrivial half depth ordinal h
 let packet := actualParentPacket observation nontrivial half depth ordinal h H N radius
 writtenSourceSplit source shift factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down=
  actualSplitSource observation nontrivial half depth ordinal h H N radius shift ∧
 (type_of% (actual_Pa_norm_debit observation nontrivial half depth ordinal h H N radius)) ∧
 (type_of% (actual_unit_norm_credit observation nontrivial half depth ordinal h H N radius)) ∧
 (type_of% (actual_outside_norm_zero_slope observation nontrivial half depth ordinal h H N radius)) := by
 dsimp only
 exact consume_split_source_receipt
  (actualSourceMaterial observation nontrivial half depth ordinal h H N radius) shift
  (actualParentFactory observation nontrivial half depth ordinal h)
  (actualParentPacket observation nontrivial half depth ordinal h H N radius) fun _whole write effect _trace =>
   ⟨(received_write_source_split _ _ _ _ _ _ _ write effect).trans
     (received_source_split _ _ _ _ _ _ _ effect),
    actual_Pa_norm_debit _ _ _ _ _ _ _ _ _,actual_unit_norm_credit _ _ _ _ _ _ _ _ _,
    actual_outside_norm_zero_slope _ _ _ _ _ _ _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
