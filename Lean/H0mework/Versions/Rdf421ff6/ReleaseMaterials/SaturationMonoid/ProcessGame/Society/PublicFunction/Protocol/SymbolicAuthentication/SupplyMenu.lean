import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalSupply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyMenu

open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (law : StageReception.Law code) (start : Cursor code)
  (observed : List (EventHistory.Stage (code := code)))

-- A rank skips source actions, never signers or a received request's contents.
def supply (rank : Nat) (site : Fin code.sites) :=
  (code.actions.drop rank).find? (LocalSupply.isOwnTransfer site)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem supply_has_its_actual_source_and_signer (rank : Nat) (site : Fin code.sites) (request)
    (chosen : supply rank site = some request) :
    request ∈ code.actions ∧ request.signer = code.siteParty site ∧
      ∃ recipient goods, request.operation = .transfer (code.siteParty site) recipient goods := by
  have member := List.mem_of_find?_eq_some chosen
  have checked := List.find?_some chosen
  simp only [LocalSupply.isOwnTransfer, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨List.mem_of_mem_drop member, checked.1, ?_⟩
  cases kind : request.operation <;> simp_all

def work (rank : Nat) (site : Fin code.sites) (reading : Fin code.signals) :=
  let original := LocalSupply.input vocabulary law start observed site
  let repaired := (supply rank site).toList ++ original
  if reading = RetainedIntent.memory start observed site ∧ original ≠ [] ∧
      (supply rank site).isSome ∧ repaired ∈ words code.actions code.actionLimit then repaired else []

theorem work_supported (rank : Nat) (site : Fin code.sites) (reading : Fin code.signals) :
    work vocabulary law start observed rank site reading ∈ words code.actions code.actionLimit := by
  dsimp only [work]
  split
  · exact ‹_ ∧ _ ∧ _ ∧ _›.2.2.2
  · exact (mem_words_iff _ _ _).mpr (by simp)

def protocol (rank : Nat) : Rule code where
  work := ⟨fun key _ => work vocabulary law start observed rank key.1 key.2, by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact work_supported vocabulary law start observed rank key.1 key.2⟩
  events := fun key _ => if work vocabulary law start observed rank key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem every_menu_rule_is_in_the_original_local_rule_domain (rank : Nat) :
    protocol vocabulary law start observed rank ∈ rules code :=
  every_rule_is_source_generated code _

theorem nonempty_work_keeps_the_original_paid_content (rank : Nat) (site : Fin code.sites)
    (reading : Fin code.signals) (needed : work vocabulary law start observed rank site reading ≠ []) :
    reading = RetainedIntent.memory start observed site ∧
    ∃ request, supply rank site = some request ∧ request ∈ code.actions ∧
      request.signer = code.siteParty site ∧
      work vocabulary law start observed rank site reading =
        request :: LocalSupply.input vocabulary law start observed site ∧
      ∃ body ∈ RequestAttestation.ledger vocabulary start observed,
        RequestReadback.localRead (code := code) (RetainedIntent.memory start observed site) = some body.request ∧
        body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start observed)).current := by
  dsimp only [work] at needed ⊢
  split at needed <;> try contradiction
  rename_i checked
  obtain ⟨request, chosen⟩ := Option.isSome_iff_exists.mp checked.2.2.1
  refine ⟨checked.1, request, chosen, (supply_has_its_actual_source_and_signer rank site request chosen).1,
    (supply_has_its_actual_source_and_signer rank site request chosen).2.1, ?_,
    LocalSupply.nonempty_input_is_an_actual_owned_paid_source_statement vocabulary law start observed site checked.2.1⟩
  rw [if_pos checked]
  simp only [chosen, Option.toList_some, List.singleton_append]

theorem actual_own_event_cannot_read_another_local_record (rank : Nat) (ownerStart : Nat)
    (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt code ownerStart history.length = some site)
    (same : left.inbox site = right.inbox site) :
    driver code ownerStart (protocol vocabulary law start observed rank) first history past left =
      driver code ownerStart (protocol vocabulary law start observed rank) second history past right :=
  own_action_uses_only_its_actual_local_record code ownerStart _ first second history past left right site owned same

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyMenu
