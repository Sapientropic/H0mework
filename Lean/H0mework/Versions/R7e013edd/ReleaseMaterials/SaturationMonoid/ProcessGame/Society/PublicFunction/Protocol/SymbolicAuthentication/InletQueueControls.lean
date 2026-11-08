import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueProgress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 96000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open InletQueueSource InletQueueProgress
open Repayment.Recovery (Good)
abbrev old := WholeCursorSupplySource.code
def vocabulary : List Action := [WholeCursorLaw.production,WholeCursorLaw.transfer,WholeCursorLaw.useFeed]
abbrev active := InletClockedSource.Active old vocabulary
-- Set the opportunity budget before the original send, preserving its paid packet and debt.
def initial : Cursor old := {WholeCursorSupplySource.initialCursor with
  entry := {WholeCursorSupplySource.initialCursor.entry with budget := 18}}
abbrev saved := EventHistory.execute initial WholeCursorSupplySource.past
abbrev opening := LiveProductionInletSource.start old vocabulary saved
abbrev working : InletClockedSource.State old vocabulary := ⟨opening,vocabulary⟩
def adaptive : InletOmissionSource.Controller old vocabulary := fun state =>
  ⟨decide (state.cursor.cut ≠ opening.cut),[LiveProductionInletControls.forged]⟩
def quiet : Nat → Rule active := fun _ => SilentWindow.quiet
abbrev completed := produced old vocabulary working adaptive 4
abbrev endCursor := terminal old vocabulary working adaptive 4
abbrev joined := final old vocabulary opening working adaptive 4 quiet
abbrev delivered := deliveryRow old vocabulary opening working adaptive 4 quiet 1
def packet : active.Packet := ⟨⟨0,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,1⟩

theorem the_actual_material_and_omission_prefix_preserves_the_old_packet :
    InletOmissionSource.funded old vocabulary working 1 = true ∧
      completed.withheld = 1 ∧ completed.unserved = 0 ∧ completed.submitted = vocabulary ∧
      completed.state.pending = List.replicate 4 LiveProductionInletControls.forged ∧
      completed.stages.length = 8 ∧ endCursor.cut = 12 ∧
      (EventStep.seed endCursor).remaining = 6 ∧
      (EventStep.seed endCursor).current.stock producer .service = 3 ∧
      (EventStep.seed endCursor).current.claims () producer creditor = 7 ∧
      (EventStep.seed endCursor).frame.sent = (EventStep.seed opening).frame.sent ∧
      (EventStep.seed opening).frame.sent[0]? = some packet ∧
      (EventStep.seed endCursor).frame.inbox ⟨0,by decide⟩ = ⟨0,by decide⟩ := by
  and_intros <;> first | rfl | decide +kernel

theorem the_joint_source_deadline_really_pays_and_recovers_the_old_message :
    horizon old vocabulary opening working adaptive 4 = 2 ∧
      hasTime old vocabulary opening working adaptive 4 = true ∧
      locate old vocabulary opening working adaptive 4 quiet 0 = some 1 ∧
      QueueMemoryEffect.resolve delivered 0 = .restored ∧
      delivered.submitted = [WholeCursorLaw.charge] ∧
      delivered.before.frame.sent[0]? = some packet ∧
      (EventStep.seed joined).current.stock producer .service = 2 ∧
      NativeDeliveryJournal.entries joined = [(13,0)] ∧
      (EventStep.seed joined).frame.inbox ⟨0,by decide⟩ = ⟨1,by decide⟩ ∧
      (EventStep.seed joined).remaining = 4 ∧ joined.cut = 14 ∧
      (EventStep.seed joined).current.claims () producer creditor = 7 := by
  and_intros <;> first | rfl | decide +kernel

theorem the_vocabulary_is_clock_free : InletClockedSource.ClockFree old vocabulary := by
  intro current request member
  simp only [vocabulary,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same | same <;> subst request <;> rfl

theorem every_actual_control_with_one_omission_reaches_the_same_resource_prefix_and_queue_window
    (control : InletOmissionSource.Controller old vocabulary)
    (within : (produced old vocabulary working control 4).withheld ≤ 1) (protocols : Nat → Rule active) :
    InletOmissionProgress.Completes old vocabulary control 4 working working.pending [] ∧
      ∃ index, locate old vocabulary opening working control 4 protocols 0 = some index ∧
        QueueMemoryEffect.Resolution (deliveryRow old vocabulary opening working control 4 protocols index) 0 packet :=
  actual_omission_bounded_production_and_old_packet_recovery_share_one_budget old vocabulary
    opening working control 4 protocols the_vocabulary_is_clock_free 1 rfl
    (by decide +kernel) within (by decide +kernel) (by decide +kernel) 0 packet
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev unfunded : InletClockedSource.State old vocabulary := ⟨opening,[WholeCursorLaw.production,WholeCursorLaw.transfer]⟩
abbrev refused := deliveryRow old vocabulary opening unfunded adaptive 3 quiet 1
abbrev refusalFinal := final old vocabulary opening unfunded adaptive 3 quiet

theorem an_actual_delivery_attempt_retains_the_original_fee_refusal :
    hasTime old vocabulary opening unfunded adaptive 3 = true ∧
      locate old vocabulary opening unfunded adaptive 3 quiet 0 = some 1 ∧
      StageReception.delivered refused 0 = true ∧
      QueueMemoryEffect.resolve refused 0 = .refused ∧
      refused.submitted = [WholeCursorLaw.charge] ∧
      NativeDeliveryJournal.entries refusalFinal = [] ∧
      (EventStep.seed refusalFinal).frame.inbox ⟨0,by decide⟩ = ⟨0,by decide⟩ ∧
      (EventStep.seed refusalFinal).current.stock producer .service = 0 := by
  and_intros <;> first | rfl | decide +kernel

-- Original timing is exhausted by the successful material prefix; no delivery is fabricated.
def shortInitial : Cursor old := {WholeCursorSupplySource.initialCursor with
  entry := {WholeCursorSupplySource.initialCursor.entry with budget := 12}}
abbrev shortOpening := LiveProductionInletSource.start old vocabulary
  (EventHistory.execute shortInitial WholeCursorSupplySource.past)
abbrev shortState : InletClockedSource.State old vocabulary := ⟨shortOpening,vocabulary⟩
abbrev shortPrefix := produced old vocabulary shortState adaptive 4
abbrev shortFinal := final old vocabulary shortOpening shortState adaptive 4 quiet
abbrev shortRow := deliveryRow old vocabulary shortOpening shortState adaptive 4 quiet 1

theorem material_completion_without_time_does_not_become_message_recovery :
    shortPrefix.unserved = 0 ∧ (EventStep.seed shortPrefix.state.cursor).remaining = 0 ∧
      hasTime old vocabulary shortOpening shortState adaptive 4 = false ∧
      locate old vocabulary shortOpening shortState adaptive 4 quiet 0 = none ∧
      QueueMemoryEffect.resolve shortRow 0 = .notDelivered ∧
      NativeDeliveryJournal.entries shortFinal = [] ∧
      (EventStep.seed shortFinal).frame.inbox ⟨0,by decide⟩ = ⟨0,by decide⟩ := by
  and_intros <;> first | rfl | decide +kernel

abbrev continued : InletClockedSource.State old vocabulary := ⟨joined,[]⟩
abbrev reused := final old vocabulary opening continued adaptive 0 quiet
abbrev reset := final old vocabulary joined continued adaptive 0 quiet

theorem the_fixed_original_baseline_prevents_reopening_a_completed_address :
    horizon old vocabulary opening continued adaptive 0 = 0 ∧
      locate old vocabulary opening continued adaptive 0 quiet 0 = none ∧
      NativeDeliveryJournal.entries reused = [(13,0)] ∧
      horizon old vocabulary joined continued adaptive 0 = 2 ∧
      NativeDeliveryJournal.entries reset = [(13,0),(15,0)] ∧
      (EventStep.seed reset).current.stock producer .service = 1 := by
  and_intros <;> first | rfl | decide +kernel

abbrev actualFinance := every_joined_record_is_consumed_in_the_final_native_financial_inventory old vocabulary
  opening working adaptive 4 quiet delivered
  (every_recovered_row_belongs_to_the_joined_actual_history old vocabulary opening working adaptive 4 quiet 0 1 (by decide +kernel))
abbrev occurrence := the_recovery_uses_the_joined_source_current_word_and_next old vocabulary
  opening working adaptive 4 quiet 0 1 (by decide +kernel)
abbrev feeMemory := NativeDeliveryConsumer.every_published_entry_consumes_its_native_fee_and_memory
  joined 13 0 (by decide +kernel)
abbrev native := ProgrammeHistory.execution_face_shares_whole_ledger_and_next joined.source.input (EventStep.boundary joined)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueControls
