import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventMemorySource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryEffect
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def restores (packet : code.Packet) : Bool :=
  (List.finRange code.signals).all fun old =>
    code.memoryReady (code.afterDelivery packet.recipient packet.sender old packet.signal)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem the_original_packet_and_source_interface_generate_repair (packet : code.Packet)
    (checked : restores packet = true) (old : Fin code.signals) :
    code.memoryReady (code.afterDelivery packet.recipient packet.sender old packet.signal) = true :=
  (List.all_eq_true.mp checked) old (List.mem_finRange _)

inductive Verdict where
  | restored | refused | notRestoring | missingPacket | notDelivered
  deriving DecidableEq

def paid (row : StageTrace.Record (code := code)) (packet : code.Packet) : Prop :=
  ∀ item ∈ code.law.rawItems row.before.current (code.deliveryCost packet.recipient),
    code.law.Valid item.before item.request
instance (row : StageTrace.Record (code := code)) (packet : code.Packet) : Decidable (paid row packet) := by
  unfold paid; infer_instance

-- The verdict reads the original packet and fee, never a supplied receipt or future ready state.
def resolve (row : StageTrace.Record (code := code)) (serial : Nat) : Verdict :=
  if StageReception.delivered row serial then
    match row.before.frame.sent[serial]? with
    | none => .missingPacket
    | some packet => if restores packet then if paid row packet then .restored else .refused else .notRestoring
  else .notDelivered

theorem the_admitted_delivery_has_its_exact_original_memory_effect
    (cursor : Cursor code) (stage : EventHistory.Stage (code := code)) (serial : Nat) (packet : code.Packet)
    (present : (EventStep.seed cursor).frame.sent[serial]? = some packet)
    (delivered : StageReception.delivered (StageTrace.material cursor stage.1 stage.2) serial = true) :
    EventMemorySource.effect cursor stage =
      if paid (StageTrace.material cursor stage.1 stage.2) packet then
        .delivery packet.recipient packet.sender packet.signal else .idle := by
  unfold StageReception.delivered at delivered
  split at delivered <;> try contradiction
  rename_i event selected
  split at delivered <;> try contradiction
  rename_i address kind
  have same : address = serial := of_decide_eq_true delivered
  subst address
  have admitted := StageTrace.captured_admission_is_the_actual_decision cursor stage.1 stage.2 (EventStep.seed cursor)
  change StageTransport.admission (StageTrace.material cursor stage.1 stage.2) = _ at admitted
  have choice := admitted.symm.trans selected
  simp only [EventMemorySource.effect, choice, EventMemorySource.ofEvent, kind, present]
  rfl

def Resolution (row : StageTrace.Record (code := code)) (serial : Nat) (packet : code.Packet) : Prop :=
  (resolve row serial = .restored ∧ paid row packet ∧ code.memoryReady (row.after.frame.inbox packet.recipient) = true) ∨
  (resolve row serial = .refused ∧ row.after.frame.inbox = row.before.frame.inbox ∧
    ∃ item ∈ StageTrace.items row, ¬ code.law.Valid item.before item.request ∧
      code.law.actualDebit item.before item.request = [] ∧ code.law.actualCredit item.before item.request = [])

theorem the_actual_delivery_generates_recovery_or_its_exact_payment_obstruction
    (cursor : Cursor code) (stage : EventHistory.Stage (code := code)) (serial : Nat) (packet : code.Packet)
    (present : (EventStep.seed cursor).frame.sent[serial]? = some packet)
    (delivered : StageReception.delivered (StageTrace.material cursor stage.1 stage.2) serial = true)
    (checked : restores packet = true) :
    Resolution (StageTrace.material cursor stage.1 stage.2) serial packet := by
  let row := StageTrace.material cursor stage.1 stage.2
  change StageReception.delivered row serial = true at delivered
  change row.before.frame.sent[serial]? = some packet at present
  have words : row.submitted = code.deliveryCost packet.recipient :=
    StageReception.actual_delivery_submits_the_original_cost cursor [stage] row List.mem_cons_self serial packet present delivered
  have exactEffect := the_admitted_delivery_has_its_exact_original_memory_effect cursor stage serial packet present delivered
  have update := EventMemorySource.actual_stage_generates_its_exact_memory_effect cursor stage
  rw [← (StageTrace.material_is_the_actual_step cursor stage.1 stage.2).1] at update
  change EventMemorySource.apply (EventMemorySource.effect cursor stage) row.before.frame.inbox = row.after.frame.inbox at update
  have verdict : resolve row serial = if paid row packet then .restored else .refused := by
    rw [resolve, if_pos delivered, present]
    change (if restores packet = true then if paid row packet then Verdict.restored else Verdict.refused else Verdict.notRestoring) = _
    rw [if_pos checked]
  by_cases funds : paid row packet
  · left
    rw [exactEffect, if_pos funds] at update
    refine ⟨verdict.trans (if_pos funds), funds, ?_⟩
    rw [← update]
    simp only [EventMemorySource.apply, ite_true]
    exact the_original_packet_and_source_interface_generate_repair packet checked (row.before.frame.inbox packet.recipient)
  · right
    rw [exactEffect, if_neg funds] at update
    have unchanged : row.after.frame.inbox = row.before.frame.inbox := update.symm
    have denied := funds
    unfold paid at denied
    push Not at denied
    obtain ⟨item, member, invalid⟩ := denied
    refine ⟨verdict.trans (if_neg funds), unchanged, item, ?_, invalid, ?_, ?_⟩
    · change item ∈ code.law.rawItems row.before.current row.submitted
      rw [words]
      exact member
    · simp only [RawLaw.actualDebit, if_neg invalid]
    · simp only [RawLaw.actualCredit, if_neg invalid]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryEffect
