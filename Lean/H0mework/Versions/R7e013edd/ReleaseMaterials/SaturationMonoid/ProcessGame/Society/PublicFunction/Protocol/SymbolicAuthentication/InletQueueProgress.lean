import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active State ClockFree)
open InletOmissionSource (Controller)
open InletQueueSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "ActiveCode" => Active old instructions
variable (origin : Cursor (Active old instructions)) (state : State old instructions) (control : Controller old instructions)
  (count : Nat) (protocols : Nat → Rule (Active old instructions))

theorem the_same_original_packet_and_attempt_set_reach_the_recovery_window :
    (EventStep.seed (terminal old instructions state control count)).frame.sent = (EventStep.seed state.cursor).frame.sent ∧
      QueueScheduler.untried ActiveCode (OriginQueue.baseline origin)
        (EventStep.seed (terminal old instructions state control count)).past =
      QueueScheduler.untried ActiveCode (OriginQueue.baseline origin) (EventStep.seed state.cursor).past := by
  have same := production_and_omission_preserve_the_original_live_communication old instructions control count state.pending.length state
  exact ⟨same.sent,congrArg (fun attempts => QueueScheduler.admitted ActiveCode \ attempts) (same.attempts _)⟩

theorem no_larger_source_deadline_is_created_by_the_inlet :
    horizon old instructions origin state control count ≤ OriginQueue.horizon origin state.cursor := by
  have same := the_same_original_packet_and_attempt_set_reach_the_recovery_window old instructions origin state control count
  have clocks := every_original_stage_pays_its_opportunity old instructions state.cursor
    (produced old instructions state control count).stages
  rw [← InletOmissionSource.every_run_is_the_original_execution] at clocks
  dsimp only [horizon,OriginQueue.horizon,OriginQueue.initialRank]
  rw [same.2]
  change (terminal old instructions state control count).ownerStart -
    (EventStep.seed (terminal old instructions state control count)).history.length + _ ≤ _
  rw [clocks.1,clocks.2.2]
  dsimp only [OriginQueue.warmup]
  omega

private theorem fits (original : OriginQueue.baseline origin ≤ (EventStep.seed state.cursor).past.length) :
    OriginQueue.baseline origin ≤ (EventStep.seed (terminal old instructions state control count)).past.length := by
  have pastExtension :=  OriginQueue.an_actual_prefix_retains_the_original_baseline state.cursor
    (produced old instructions state control count).stages
  rw [← InletOmissionSource.every_run_is_the_original_execution] at pastExtension
  exact original.trans pastExtension.length_le

-- The old opportunity budget pays both the actual production prefix and the whole recovery window.
theorem an_original_joint_budget_funds_the_actual_deadline
    (length : (produced old instructions state control count).stages.length ≤ 2 * count)
    (budget : 2 * count + OriginQueue.horizon origin state.cursor ≤ (EventStep.seed state.cursor).remaining) :
    hasTime old instructions origin state control count = true := by
  have clocks := every_original_stage_pays_its_opportunity old instructions state.cursor
    (produced old instructions state control count).stages
  rw [← InletOmissionSource.every_run_is_the_original_execution] at clocks
  have bounded := no_larger_source_deadline_is_created_by_the_inlet old instructions origin state control count
  apply decide_eq_true (by
    rw [clocks.2.1]
    omega)

theorem the_inlet_deadline_generates_paid_recovery_or_its_exact_fee_refusal
    (original : OriginQueue.baseline origin ≤ (EventStep.seed state.cursor).past.length)
    (time : hasTime old instructions origin state control count = true)
    (serial : Nat) (packet : (Active old instructions).Packet)
    (present : serial < (EventStep.seed state.cursor).frame.sent.length)
    (initial : (EventStep.seed state.cursor).frame.sent[serial]? = some packet)
    (fresh : serial ∈ QueueScheduler.untried ActiveCode (OriginQueue.baseline origin) (EventStep.seed state.cursor).past)
    (interface : QueueMemoryEffect.restores packet = true) :
    ∃ index, locate old instructions origin state control count protocols serial = some index ∧
      index < horizon old instructions origin state control count ∧
      StageReception.delivered (deliveryRow old instructions origin state control count protocols index) serial = true ∧
      (deliveryRow old instructions origin state control count protocols index).before.frame.sent[serial]? = some packet ∧
      (deliveryRow old instructions origin state control count protocols index).submitted = (Active old instructions).deliveryCost packet.recipient ∧
      QueueMemoryEffect.Resolution (deliveryRow old instructions origin state control count protocols index) serial packet := by
  have same := the_same_original_packet_and_attempt_set_reach_the_recovery_window old instructions origin state control count
  apply QueueMemoryDeadline.the_source_deadline_generates_paid_recovery_or_the_original_fee_refusal
    origin (terminal old instructions state control count) protocols
    (fits old instructions origin state control count original) serial packet (of_decide_eq_true time)
  · rwa [same.1]
  · rwa [same.1]
  · rwa [same.2]
  · exact interface

theorem actual_omission_bounded_production_and_old_packet_recovery_share_one_budget
    (clockFree : ClockFree old instructions) (allowance : Nat)
    (counted : count = state.pending.length + allowance)
    (checks : InletOmissionSource.funded old instructions state allowance = true)
    (within : (produced old instructions state control count).withheld ≤ allowance)
    (budget : 2 * count + OriginQueue.horizon origin state.cursor ≤ (EventStep.seed state.cursor).remaining)
    (original : OriginQueue.baseline origin ≤ (EventStep.seed state.cursor).past.length)
    (serial : Nat) (packet : (Active old instructions).Packet)
    (present : serial < (EventStep.seed state.cursor).frame.sent.length)
    (initial : (EventStep.seed state.cursor).frame.sent[serial]? = some packet)
    (fresh : serial ∈ QueueScheduler.untried ActiveCode (OriginQueue.baseline origin) (EventStep.seed state.cursor).past)
    (interface : QueueMemoryEffect.restores packet = true) :
    InletOmissionProgress.Completes old instructions control count state state.pending [] ∧
      ∃ index, locate old instructions origin state control count protocols serial = some index ∧
        QueueMemoryEffect.Resolution (deliveryRow old instructions origin state control count protocols index) serial packet := by
  subst count
  have complete := InletOmissionProgress.checked_production_completes old instructions clockFree control state allowance checks within
  have time := an_original_joint_budget_funds_the_actual_deadline old instructions origin state control _ complete.length budget
  obtain ⟨index,selected,_,_,_,_,resolved⟩ :=
    the_inlet_deadline_generates_paid_recovery_or_its_exact_fee_refusal old instructions origin state control _ protocols
      original time serial packet present initial fresh interface
  exact ⟨complete,index,selected,resolved⟩

theorem every_recovered_row_belongs_to_the_joined_actual_history
    (serial index : Nat)
    (selected : locate old instructions origin state control count protocols serial = some index) :
    deliveryRow old instructions origin state control count protocols index ∈
      StageTrace.records state.cursor (stages old instructions origin state control count protocols) := by
  have bound := (QueueMemoryDeadline.every_location_is_an_actual_source_delivery
    origin (terminal old instructions state control count) protocols serial index selected).1
  have physical := OriginQueue.row_at_its_actual_index origin (terminal old instructions state control count) protocols _ index bound
  rw [stages,OriginQueue.records_append,← InletOmissionSource.every_run_is_the_original_execution]
  exact List.mem_append_right _ (List.mem_of_getElem? physical)

theorem every_joined_record_is_consumed_in_the_final_native_financial_inventory
    (record : StageTrace.Record (code := ActiveCode))
    (inside : record ∈ StageTrace.records state.cursor (stages old instructions origin state control count protocols)) :
    (Financial.inventoryAt (final old instructions origin state control count protocols).source.input
      (ProgrammeHistory.visitAt (final old instructions origin state control count protocols).source.input
        (EventStep.boundary record.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (final old instructions origin state control count protocols).source.input) =
        StageTrace.items record :=
  StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ inside

theorem the_recovery_uses_the_joined_source_current_word_and_next
    (serial index : Nat)
    (selected : locate old instructions origin state control count protocols serial = some index) :
    let actual := deliveryRow old instructions origin state control count protocols index
    let last := final old instructions origin state control count protocols
    actual.before.current = last.source.currentAt (EventStep.boundary actual.cursor) ∧
      actual.submitted = ProgrammeSource.rawEvent last.source.input
        (ProgrammeHistory.visitAt last.source.input (EventStep.boundary actual.cursor)).current ∧
      actual.after.current = last.source.currentAt (EventStep.boundary actual.cursor + 1) ∧
      actual.after.current = (Active old instructions).law.next actual.before.current actual.submitted :=
  StageTrace.every_record_is_a_completed_occurrence_of_the_final_source _ _ _
    (every_recovered_row_belongs_to_the_joined_actual_history old instructions origin state control count protocols serial index selected)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueProgress
