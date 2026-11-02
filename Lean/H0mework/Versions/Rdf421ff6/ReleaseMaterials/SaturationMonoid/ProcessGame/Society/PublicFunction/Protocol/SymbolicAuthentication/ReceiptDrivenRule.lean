import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshReception

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRule
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def isForSignal (signal : Fin code.signals) (receipt : RequestReadback.Receipt (code := code)) :=
  decide (receipt.reading = signal ∧ RequestReadback.localRead (code := code) signal = some receipt.statement.request)

def reply (pending : FreshReception.Mailbox (code := code)) (site : Fin code.sites) (signal : Fin code.signals) :=
  if (pending site).any (isForSignal signal)
    then RequestResponse.work site signal else []

theorem reply_supported (pending : FreshReception.Mailbox (code := code)) (site : Fin code.sites) (signal : Fin code.signals) :
    reply pending site signal ∈ words code.actions code.actionLimit := by
  unfold reply
  split
  · exact RequestResponse.work_supported site signal
  · exact (mem_words_iff _ _ _).mpr (by simp)

def protocol (base : Rule code) (pending : FreshReception.Mailbox (code := code)) : Rule code where
  work := ⟨fun key inside => if reply pending key.1 key.2 = [] then base.work.val key inside else reply pending key.1 key.2, by
    apply code.every_local_policy_is_enumerated
    intro key inside
    split
    · exact ((List.mem_pi _ _).mp base.work.property) key inside
    · exact reply_supported pending key.1 key.2⟩
  events := fun key inside => if reply pending key.1 key.2 = [] then base.events key inside
    else RequestResponse.activation key.1

-- One submitted response consumes one matching notification. Different inputs
-- and additional occurrences remain queued with their original source history.
def consume (pending : FreshReception.Mailbox (code := code)) (row : StageTrace.Record (code := code)) :
    FreshReception.Mailbox (code := code) := fun site =>
  if StageTrace.activation row = some site ∧ reply pending site (row.before.frame.inbox site) ≠ [] ∧
      row.submitted = reply pending site (row.before.frame.inbox site) ∧
      (∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request)
    then (pending site).eraseP (isForSignal (row.before.frame.inbox site)) else pending site

theorem removing_a_notification_requires_its_actual_valid_response
    (pending : FreshReception.Mailbox (code := code)) (row : StageTrace.Record (code := code))
    (site : Fin code.sites) (receipt : RequestReadback.Receipt (code := code))
    (before : receipt ∈ pending site) (removed : receipt ∉ consume pending row site) :
    StageTrace.activation row = some site ∧ reply pending site (row.before.frame.inbox site) ≠ [] ∧
      row.submitted = reply pending site (row.before.frame.inbox site) ∧
      (∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request) := by
  unfold consume at removed
  split at removed
  · assumption
  · exact False.elim (removed before)

theorem consumed_receipts_were_already_queued (pending : FreshReception.Mailbox (code := code))
    (row : StageTrace.Record (code := code)) (site : Fin code.sites) (receipt : RequestReadback.Receipt (code := code))
    (inside : receipt ∈ consume pending row site) : receipt ∈ pending site := by
  unfold consume at inside
  split at inside
  · exact List.mem_of_mem_eraseP inside
  · exact inside

theorem a_reply_preserves_every_different_queued_input (pending : FreshReception.Mailbox (code := code))
    (row : StageTrace.Record (code := code)) (site : Fin code.sites) (receipt : RequestReadback.Receipt (code := code))
    (inside : receipt ∈ pending site) (different : receipt.reading ≠ row.before.frame.inbox site) :
    receipt ∈ consume pending row site := by
  unfold consume
  split
  · apply (List.mem_eraseP_of_neg ?_).mpr inside
    intro aligned
    exact different (of_decide_eq_true aligned).1
  · exact inside

theorem one_sites_next_action_ignores_other_sites_queues_and_private_histories
    (base : Rule code) (left right : FreshReception.Mailbox (code := code))
    (site : Fin code.sites) (sameQueue : left site = right site)
    (ownerStart : Nat) (first second : Opponent code) (leftHistory rightHistory : History)
    (leftPast rightPast : Events code) (a b : code.Frame)
    (ownedLeft : Distributed.Recall.Information.Agency.ownerAt code ownerStart leftHistory.length = some site)
    (ownedRight : Distributed.Recall.Information.Agency.ownerAt code ownerStart rightHistory.length = some site)
    (sameSignal : a.inbox site = b.inbox site) :
    driver code ownerStart (protocol base left) first leftHistory leftPast a =
      driver code ownerStart (protocol base right) second rightHistory rightPast b := by
  simp only [driver, ownedLeft, ownedRight]
  rw [sameSignal]
  simp only [localEvent, protocol, reply, sameQueue]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRule
