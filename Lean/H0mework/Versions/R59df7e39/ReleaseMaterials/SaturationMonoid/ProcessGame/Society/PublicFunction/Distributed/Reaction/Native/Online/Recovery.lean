import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Source
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Recovery
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver) (oldDepth : Nat) (word : List (Future.Recovery.Action seed))

structure Receipt where
  private mk ::
  transport : Future.Receipt seed oldDepth cursor.source cursor.count word
  output : Future.Recovery.Output transport
  pricing : Future.Recovery.Pricing (Future.Recovery.Action seed)
  generated : output = Future.Recovery.produceWith pricing transport

def execute (pricing : Future.Recovery.Pricing (Future.Recovery.Action seed)) :
    PLift (¬ Mandate.Replay.Legal (base := seed.base) seed.scope (Authority.currentAt seed oldDepth) word) ⊕
      Receipt cursor oldDepth word :=
  match Future.produce seed oldDepth cursor.source cursor.count word with
  | .inl blocked => .inl blocked
  | .inr original => .inr ⟨original,Future.Recovery.produceWith pricing original,pricing,rfl⟩

namespace Receipt
variable {cursor oldDepth word} (made : Receipt cursor oldDepth word)
abbrev next := cursor.recover made.output

theorem actual_paid_source_is_the_online_source : made.next.model = made.output.bound :=
  cursor.recovery_has_the_same_actual_source made.output

theorem invoices_keep_the_original_feedback_budget :
    made.next.state.remaining = cursor.state.remaining ∧ made.next.feedbackIndex = cursor.feedbackIndex :=
  ⟨cursor.all_recovery_invoices_and_retries_preserve_the_next_input_budget made.output,rfl⟩

theorem online_state_is_the_actual_recovery_next :
    made.next.state.current = made.output.bound.source.currentAt (made.output.walk.finish.depth+1) :=
  made.next.aligned

theorem the_original_paid_recovery_contract_is_consumed :
    made.output.Metered ∧ made.output.walk.Closed ∧
      made.output.walk.finish.consumed ++ made.output.walk.finish.residual = word :=
  ⟨made.output.metered,made.output.walk.closed,made.output.walk.finish.split⟩
end Receipt
variable (origin : Authority.Sources seed.base seed.scope)

/-- The request's legal origin may be the current actual source, or a preserved earlier actual source.
    The output always executes on this cursor and is assimilated from its exact emitted interval. -/
structure ReceiptFrom where
  private mk ::
  transport : Future.Receipt (boundAt seed origin) oldDepth cursor.source cursor.count word
  output : Future.Recovery.Output transport
  pricing : Future.Recovery.Pricing (Future.Recovery.Action seed)
  generated : output = Future.Recovery.produceWith (old := boundAt seed origin) pricing transport

def executeFrom (pricing : Future.Recovery.Pricing (Future.Recovery.Action seed)) :
    PLift (¬ Mandate.Replay.Legal (base := seed.base) seed.scope (Authority.currentAt (boundAt seed origin) oldDepth) word) ⊕
      ReceiptFrom cursor oldDepth word origin :=
  match Future.produce (boundAt seed origin) oldDepth cursor.source cursor.count word with
  | .inl blocked => .inl blocked
  | .inr original => .inr ⟨original,Future.Recovery.produceWith (old := boundAt seed origin) pricing original,pricing,rfl⟩

variable {oldDepth word origin}
namespace ReceiptFrom
variable (made : ReceiptFrom cursor oldDepth word origin)
abbrev next := cursor.assimilate made.output

theorem actual_paid_source_is_the_online_source : made.next.model = made.output.bound :=
  cursor.assimilation_has_the_same_actual_source made.output

theorem complete_invoices_are_in_the_next_local_history :
    made.next.state.frame.word = cursor.state.frame.word ++
      ((List.range (made.output.walk.finish.depth-cursor.depth)).map
        (fun index => (made.output.bound.source.actualExecution (cursor.depth+index)).submitted)).flatten :=
  cursor.assimilated_frame_contains_every_actual_invoice_and_retry made.output

theorem invoices_keep_the_original_feedback_budget_and_communication :
    made.next.state.remaining = cursor.state.remaining ∧ made.next.feedbackIndex = cursor.feedbackIndex ∧
    HEq made.next.state.past cursor.state.past ∧ HEq made.next.state.frame.inbox cursor.state.frame.inbox ∧
    HEq made.next.state.frame.sent cursor.state.frame.sent := by
  have memory := cursor.assimilation_preserves_communication_without_fabricating_events made.output
  exact ⟨cursor.all_assimilated_invoices_and_retries_preserve_the_next_input_budget made.output,rfl,
    memory.1,memory.2.1,memory.2.2⟩

theorem the_original_paid_kernel_and_all_native_rows_are_consumed :
    made.output.Metered ∧ made.output.walk.Closed ∧
    made.output.walk.finish.consumed ++ made.output.walk.finish.residual = word ∧
    made.next.model = made.output.bound ∧
    made.output.native = Authority.fullGenerate made.output.bound (made.output.walk.finish.depth-1) :=
  ⟨made.output.metered,made.output.walk.closed,made.output.walk.finish.split,
    made.actual_paid_source_is_the_online_source,made.output.native_exact⟩
end ReceiptFrom

variable (word)
def executeCurrent (pricing : Future.Recovery.Pricing (Future.Recovery.Action seed)) :=
  executeFrom cursor cursor.depth word cursor.source pricing

theorem current_receipt_is_legal_at_the_actual_learning_state
    (made : ReceiptFrom cursor cursor.depth word cursor.source) :
    Mandate.Replay.Legal (base := seed.base) seed.scope cursor.state.current word := by
  have legal := made.transport.origin
  change Mandate.Replay.Legal (base := seed.base) seed.scope
    (cursor.source.val.currentAt (cursor.depth+1)) word at legal
  rwa [← cursor.aligned] at legal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Recovery
