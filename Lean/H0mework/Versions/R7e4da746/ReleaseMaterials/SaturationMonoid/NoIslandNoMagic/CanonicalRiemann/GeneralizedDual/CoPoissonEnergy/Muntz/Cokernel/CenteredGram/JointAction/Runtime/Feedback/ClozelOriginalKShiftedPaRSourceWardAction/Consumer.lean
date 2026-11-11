import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Registry
export OriginalKPaUnitOutsideSourceDebtAction
 (received_born_current_source received_actual_material_trace_effect sourceActorGradedTrace source_emitter_full_trace_inventory
  source_emitter_calculation_trace_pair_inventory actual_stock_receipt_low_stock)
end Registry
local instance sourceConsumerGroups (grade : Nat) (target : Unit) :
 AddCommGroup (OriginalKPaUnitOutsideSourceDebtAction.L.Value
  (PairValue OriginalKPaUnitOutsideSourceDebtAction.C.Value) grade target) :=
 OriginalKPaUnitOutsideSourceDebtAction.L.groups (PairValue OriginalKPaUnitOutsideSourceDebtAction.C.Value) grade target
namespace C
export OriginalKPaUnitOutsideSourceDebtAction.C (Value Var)
end C
namespace SF
export OriginalKPaUnitOutsideSourceDebtAction.SF (Factory)
end SF
namespace AP
export OriginalKPaUnitOutsideSourceDebtAction.AP (AdmissionPacket)
end AP
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (projection : BurnolL2 →L[ℂ] BurnolL2) (source : Split.Branches) (base step : ℝ)
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

def finiteDebtReadAt : Prop :=
 ∃ whole : type_of% (Step.sourceWholeAt source step factory packet),
 (type_of% whole.actual_step) ∧ (type_of% whole.payment.strictDebit) ∧
 (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧ (type_of% whole.entry) ∧
 (type_of% whole.whole_destination) ∧ (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (Step.source_born_root source step factory packet)) ∧ (type_of% (Step.source_born_current source step factory packet)) ∧
 (type_of% (Registry.received_born_current_source source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
  (Step.actual_born_split_increment source step (Previous.splitFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down _)
  (Step.actual_material_stock_effect source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down))) ∧
 Step.writtenSourceSplit source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down=
  shiftedSplit observation nontrivial half depth ordinal h H N (base+step) ∧
 ‖projection (Step.writtenSourceSplit source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).2.2‖^2-
  ‖projection (Previous.sourceRRead source)‖^2=
  ∫ t in base..(base+step), projectedDebtDensity observation nontrivial half depth ordinal h H N projection t ∧
 (type_of% (Registry.source_emitter_full_trace_inventory source step (Previous.splitFactory factory)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (Previous.sourceSelectedAt source step factory packet))) ∧
 (type_of% (Registry.source_emitter_calculation_trace_pair_inventory source step (Previous.splitFactory factory)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (Previous.sourceSelectedAt source step factory packet))) ∧
 (type_of% (Registry.actual_stock_receipt_low_stock source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) ∧
 (type_of% (Registry.received_actual_material_trace_effect source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) ∧
 (type_of% (Registry.sourceActorGradedTrace source step (Previous.splitFactory factory)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (Previous.sourceSelectedAt source step factory packet)).sound)

attribute [irreducible] finiteDebtReadAt

/-- The source alignment is consumed downstream of the actual WB producer; the source constructor accepts no debt or endpoint target. -/
theorem received_whole_finite_source_debt
 (sourceRead : Previous.sourceRRead source=shiftedR observation nontrivial half depth ordinal h H N base) :
 finiteDebtReadAt observation nontrivial half depth ordinal h H N projection source base step factory packet := by
 unfold finiteDebtReadAt
 have action : Previous.splitAction step source=shiftedSplit observation nontrivial half depth ordinal h H N (base+step) := by
  change Split.splitProjection (burnolMultiplicativeDilation (-step/2) (Previous.sourceRRead source))=_
  rw [sourceRead]
  unfold shiftedR
  rw [burnolMultiplicativeDilation_add]
  have parameter : -step/2+ -base/2= -(base+step)/2 := by ring
  rw [parameter]
  rfl
 exact Step.consume_split_source_receipt source step factory packet fun whole write effect trace => by
  have recovered := ((Step.received_write_source_split source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down write effect).trans
   (Step.received_source_split source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down effect)).trans action
  have debt : ‖projection (Step.writtenSourceSplit source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).2.2‖^2-
   ‖projection (Previous.sourceRRead source)‖^2=
   ∫ t in base..(base+step), projectedDebtDensity observation nontrivial half depth ordinal h H N projection t := by
   rw [recovered,sourceRead]
   exact finite_projected_debt observation nontrivial half depth ordinal h H N projection base (base+step)
  exact ⟨whole,whole.actual_step,whole.payment.strictDebit,whole.same_ledger,whole.same_visit,whole.entry,
   whole.whole_destination,whole.source_environment,whole.source_expression,Step.source_born_root _ _ _ _,Step.source_born_current _ _ _ _,
   Registry.received_born_current_source _ _ _ _ _ _ _ write effect,recovered,debt,
   Registry.source_emitter_full_trace_inventory _ _ _ _ _ _ _ _,Registry.source_emitter_calculation_trace_pair_inventory _ _ _ _ _ _ _ _,
   Registry.actual_stock_receipt_low_stock _ _ _ _ _ _ _,Registry.received_actual_material_trace_effect _ _ _ _ _ _ _,trace.sound⟩

variable (radius : ℝ)
theorem actual_received_whole_finite_source_debt (projection : BurnolL2 →L[ℂ] BurnolL2) (base step : ℝ) :
 finiteDebtReadAt observation nontrivial half depth ordinal h H N projection
  (receivedShiftSource observation nontrivial half depth ordinal h H N radius base) base step
  (sourceParentFactory observation nontrivial half depth ordinal h)
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base) :=
 received_whole_finite_source_debt observation nontrivial half depth ordinal h H N projection
  (receivedShiftSource observation nontrivial half depth ordinal h H N radius base) base step
  (sourceParentFactory observation nontrivial half depth ordinal h)
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base)
  (received_shift_source_R observation nontrivial half depth ordinal h H N radius base)

theorem actual_next_source_all_future (base step : ℝ) (futureOrdinal : Nat) (history : List PUnit) (target : Nat) :
 type_of% (Step.source_packet_all_future
  (receivedShiftSource observation nontrivial half depth ordinal h H N radius base) step
  (sourceParentFactory observation nontrivial half depth ordinal h)
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base) futureOrdinal history target) :=
 Step.source_packet_all_future _ _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
