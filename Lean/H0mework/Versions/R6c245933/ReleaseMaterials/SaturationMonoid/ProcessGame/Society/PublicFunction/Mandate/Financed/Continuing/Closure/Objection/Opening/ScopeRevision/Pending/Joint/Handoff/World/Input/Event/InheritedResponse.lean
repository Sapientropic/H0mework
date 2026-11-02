import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.TaskTransport
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancialBalance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.InheritedResponse

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Future.Expiry.Progress
noncomputable section
variable {first last : Packet} (incoming : Evolution first last) (trace : Trace last.2)

def combined : Evolution first trace.packet := .append incoming trace.native

def original (row : Responsibility.Row first) := Responsibility.transport (combined incoming trace) row

def complete (row : Responsibility.Row first) := (original incoming trace row).complete

def financialSlot (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : first.2.finance.current.slots[index]? = some slot) :=
  Response.financialSlotAlong (combined incoming trace) index slot present

structure Paid where
  private mk ::
  next : Programme.Completion.PaidNext
    (Programme.produce (Event.observed trace.ending.1 (Future.ownWord trace.ending.1)))
  packet : trace.packet = next.packet
  four : Nonempty (Handoff.PaidOpening next.fresh (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted)
  homology : ∀ index : first.1.source.Slot,
    (Handoff.source next.fresh).seed.slot (Handoff.homologous next.fresh (TaskTransport.along incoming index)) =
      first.1.source.seed.slot index
  service : ∀ index : first.1.source.Slot,
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (Handoff.law next.fresh)
      (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted
      (first.1.source.seed.slot index).bearer (first.1.source.seed.slot index).goods (first.1.source.seed.slot index).purpose
  healthy : ExitCapacity.Nonnegative (current trace.packet.1 trace.packet.2.inputs)
  exitMaterial : ExitCapacity.Envelope (current trace.packet.1 trace.packet.2.inputs)

def lift (next : Programme.Completion.PaidNext
    (Programme.produce (Event.observed trace.ending.1 (Future.ownWord trace.ending.1))))
    (packet : trace.packet = next.packet) (facts : Future.Opened next) : Paid incoming trace := by
  refine ⟨next, packet, ⟨next.opening⟩, ?_, ?_, ?_, ?_⟩
  · intro index
    exact (facts.homology (TaskTransport.along incoming index)).trans (TaskTransport.content incoming index)
  · intro index
    have payment := facts.service (TaskTransport.along incoming index)
    rw [TaskTransport.content incoming index] at payment
    exact payment
  · rw [packet]
    exact facts.healthy
  · rw [packet]
    exact facts.exitMaterial

/-- Every branch retains the actual source's decision and its own next event. -/
inductive Result where
  | private paid (witness : Paid incoming trace)
  | private blocked (reason : trace.ending.2.1.event.original.original.decision.kind ≠ .paid)
      (original : Future.Openness trace.ending.2.1.event.original.original.decision)

def classify : Result incoming trace := by
  have outlook := trace.ending.2.1.openness
  cases outlook
  next next kind packet facts => exact .paid (lift incoming trace next packet facts)
  next kind absent reason packet => exact .blocked (by rw [kind]; decide) trace.ending.2.1.openness
  next kind fresh chosen absent failure methods packet =>
    exact .blocked (by rw [kind]; decide) trace.ending.2.1.openness

def Result.kind : Result incoming trace → World.ContinuationKind
  | .paid .. => .paid
  | .blocked _ outlook => outlook.kind

theorem classification_is_the_actual_terminal_decision :
    (classify incoming trace).kind incoming trace = trace.ending.2.1.event.original.original.decision.kind := by
  unfold classify
  generalize actual : trace.ending.2.1.openness = outlook
  cases outlook
  next next kind packet facts => exact kind.symm
  next kind absent reason packet => exact kind.symm
  next kind fresh chosen absent failure methods packet => exact kind.symm

theorem all_original_rows_have_their_actual_complete_runs (row : Responsibility.Row first) :
    (original incoming trace row).row.origin = row.origin ∧
      row.state.history <+: (original incoming trace row).state.history ∧
      Nonempty ((original incoming trace row).native.Run row.origin.initial (original incoming trace row).state) := by
  have kept := Responsibility.every_actual_step_retains_its_original_admission_and_history (combined incoming trace) row
  exact ⟨kept.1, kept.2, ⟨complete incoming trace row⟩⟩

theorem all_original_financial_addresses_have_the_same_actual_records
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : first.2.finance.current.slots[index]? = some slot) :
    Financial.Family.Migration.identity sources (financialSlot incoming trace index slot present).slot =
      Financial.Family.Migration.identity sources slot ∧
    (financialSlot incoming trace index slot present).path.records sources index =
      (Response.financeAlong (combined incoming trace)).events.filter (fun event => event.slot == index) :=
  Response.every_actual_path_preserves_each_original_financial_address (combined incoming trace) index slot present

theorem own_next_is_generated_at_the_actual_endpoint :
    trace.nextSourceEvent.before = current trace.packet.1 trace.packet.2.inputs ∧
    (World.actual trace.packet.2 (Future.ownWord trace.packet.2)).after = trace.nextSourceEvent.after :=
  ⟨Future.own_event_starts_at_the_saved_current _,Future.submitting_the_own_event_preserves_its_actual_after _⟩

theorem Result.paid_has_a_full_inherited_witness (result : Result incoming trace)
    (paid : result.kind incoming trace = .paid) : Nonempty (Paid incoming trace) := by
  cases result
  next witness => exact ⟨witness⟩
  next absent outlook =>
    exact False.elim (absent (outlook.classifies_the_actual_decision.symm.trans paid))

def produce : Result incoming (Future.Expiry.Progress.Runtime.trace last.2) := classify incoming _

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.InheritedResponse
