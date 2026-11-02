import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ObservationSupply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalService

open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (installed : List (Rule code))

-- The entering record is the key's own current signal, not a vector of actual snapshots.
def work (site : Fin code.sites) (signal : Fin code.signals) :=
  ReceivedStatementAuthentication.work vocabulary encoding law start installed installed.length signal site signal

theorem work_supported (site : Fin code.sites) (signal : Fin code.signals) :
    work vocabulary encoding law start installed site signal ∈ words code.actions code.actionLimit :=
  ReceivedStatementAuthentication.work_supported vocabulary encoding law start installed installed.length signal site signal

def protocol : Rule code where
  work := ⟨fun key _ => work vocabulary encoding law start installed key.1 key.2, by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact work_supported vocabulary encoding law start installed key.1 key.2⟩
  events := fun key _ => if work vocabulary encoding law start installed key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem actual_nonempty_work_keeps_its_own_paid_receipt
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (needed : work vocabulary encoding law start (stages.map Prod.fst) site
      (RetainedIntent.memory start stages site) ≠ []) :
    ∃ body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (stages.map Prod.fst)
        stages.length (RetainedIntent.memory start stages site) site (RetainedIntent.memory start stages site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start stages site stages.length).receipts,
        receipt.statement = body ∧
        RequestReadback.localRead (code := code) (RetainedIntent.memory start stages site) = some body.request ∧
        body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  have entering : ReceivedStatementAuthentication.remembered start stages stages.length site =
      RetainedIntent.memory start stages site := by
    unfold ReceivedStatementAuthentication.remembered
    rw [List.getElem?_eq_none_iff.mpr (by rw [StageTrace.record_count])]
  have result := ReceivedStatementAuthentication.nonempty_work_has_actual_paid_communication_support
    vocabulary encoding law start stages stages.length site
  rw [entering] at result
  exact result (by simpa only [work, List.length_map] using needed)

theorem own_action_uses_only_the_current_local_record
    (ownerStart : Nat) (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt code ownerStart history.length = some site)
    (same : left.inbox site = right.inbox site) :
    driver code ownerStart (protocol vocabulary encoding law start installed) first history past left =
      driver code ownerStart (protocol vocabulary encoding law start installed) second history past right :=
  own_action_uses_only_its_actual_local_record code ownerStart _ first second history past left right site owned same

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalService
