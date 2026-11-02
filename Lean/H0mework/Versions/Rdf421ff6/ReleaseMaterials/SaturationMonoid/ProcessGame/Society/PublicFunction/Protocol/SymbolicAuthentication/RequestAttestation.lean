import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageBudget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestAttestation

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev Request := Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument

-- This application wellFormed is an explicit protocol convention. Native revision
-- requests keep their original meaning, payments and legacy label interpretation.
def protocolSyntax (request : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Bool :=
  match request.operation with
  | .use bearer _ .external => decide (bearer = request.signer ∧ request.consents = [] ∧ request.gates = [])
  | _ => false

structure StatementData (Party Good Port Technology Instrument : Type) (sites : Nat) where
  ballot : OwnedAttestation.BallotData Party sites
  request : Institutions.Capitalism.Universal.Source.Program.Request Party Good Port Technology Instrument
  deriving DecidableEq

abbrev Statement := StatementData Party Good Port (Mandate.State Party Technology) Instrument code.sites

inductive Rejection where
  | source (reason : OwnedAttestation.Rejection)
  | missingItem | outsideProtocol
  deriving DecidableEq

inductive OutcomeData (Body : Type) where
  | rejected (reason : Rejection)
  | attested (statement : Body)
  deriving DecidableEq

abbrev Outcome := OutcomeData (Statement (code := code))

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def outcome (row : StageTrace.Record (code := code)) (position : Nat) : Outcome (code := code) :=
  match StageBudget.outcome vocabulary row position with
  | .rejected reason => .rejected (.source reason)
  | .attested ballot => match (StageTrace.items row)[position]? with
    | none => .rejected .missingItem
    | some item => if protocolSyntax item.request then .attested ⟨ballot, item.request⟩ else .rejected .outsideProtocol

def issued (row : StageTrace.Record (code := code)) (position : Nat) : Option (Statement (code := code)) :=
  match outcome vocabulary row position with
  | .rejected _ => none
  | .attested statement => some statement

def ledger (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) : List (Statement (code := code)) :=
  (StageTrace.records start stages).flatMap fun row =>
    (List.range row.submitted.length).filterMap (issued vocabulary row)

def verify (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (candidate : Statement (code := code)) : Bool := decide (candidate ∈ ledger vocabulary start stages)

def audit (row : StageTrace.Record (code := code)) :=
  (StageTrace.items row).mapIdx fun position item => (item, outcome vocabulary row position)

theorem the_audit_keeps_every_original_request (row : StageTrace.Record (code := code)) :
    (audit vocabulary row).map (fun entry => entry.1.request) = row.submitted := by
  calc
    _ = (StageTrace.items row).map ExecutionItem.request := by
      apply List.ext_getElem?
      intro i
      simp [audit, Function.comp_def]
    _ = _ := code.law.inventory_requests_exact _ 0 _

theorem issued_binds_the_complete_original_request
    (row : StageTrace.Record (code := code)) (position : Nat) (body : Statement (code := code))
    (made : issued vocabulary row position = some body) :
    StageBudget.issued vocabulary row position = some body.ballot ∧
      ∃ item, (StageTrace.items row)[position]? = some item ∧ item.request = body.request ∧ protocolSyntax item.request = true := by
  have inspected : outcome vocabulary row position = .attested body := by
    unfold issued at made
    split at made <;> try contradiction
    cases Option.some.inj made
    assumption
  unfold outcome at inspected
  split at inspected <;> try contradiction
  rename_i ballot legacy
  split at inspected <;> try contradiction
  rename_i item actual
  split at inspected <;> try contradiction
  rename_i wellFormed
  cases OutcomeData.attested.inj inspected
  exact ⟨by simp only [StageBudget.issued, legacy], item, actual, rfl, wellFormed⟩

theorem ledger_origin (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : Statement (code := code)) (inside : body ∈ ledger vocabulary start stages) :
    ∃ row ∈ StageTrace.records start stages, ∃ position,
      issued vocabulary row position = some body := by
  obtain ⟨row, present, included⟩ := List.mem_flatMap.mp inside
  obtain ⟨position, _, made⟩ := List.mem_filterMap.mp included
  exact ⟨row, present, position, made⟩

theorem every_statement_retains_owned_valid_paid_source_and_complete_request
    (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : Statement (code := code)) (inside : body ∈ ledger vocabulary start stages) :
    ∃ row ∈ StageTrace.records start stages, ∃ position site item,
      StageTrace.activation row = some site ∧ (StageTrace.items row)[position]? = some item ∧
      item.request = body.request ∧ protocolSyntax item.request = true ∧
      code.law.Valid item.before item.request ∧ item.request.signer = code.siteParty site ∧
      vocabulary.decode item.request.purpose = some (body.ballot.scope, body.ballot.choice) ∧
      body.ballot.scope.epoch = vocabulary.epoch item.before ∧ body.ballot.key = site ∧
      body.ballot.cut = row.cursor.cut ∧ body.ballot.position = position ∧
      body.ballot.fee = flowAt (code.law.actualDebit item.before item.request) (code.siteParty site) vocabulary.feeUnit ∧
      0 < body.ballot.fee := by
  obtain ⟨row, present, position, made⟩ := ledger_origin vocabulary start stages body inside
  obtain ⟨legacy, item, actual, request, wellFormed⟩ := issued_binds_the_complete_original_request vocabulary row position body made
  obtain ⟨site, oldItem, owned, same, valid, signer, decoded, epoch, key, cut, address, fee, paid⟩ :=
    StageBudget.issued_has_an_owned_valid_paid_origin vocabulary row position body.ballot legacy
  have sameItem : oldItem = item := Option.some.inj (same.symm.trans actual)
  subst oldItem
  exact ⟨row, present, position, site, item, owned, actual, request, wellFormed, valid, signer, decoded, epoch, key, cut, address, fee, paid⟩

theorem independently_verified_iff (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : Statement (code := code)) : verify vocabulary start stages body = true ↔ body ∈ ledger vocabulary start stages := by
  simp only [verify, decide_eq_true_eq]

theorem a_statement_cannot_create_a_new_legacy_ballot
    (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : Statement (code := code)) (inside : body ∈ ledger vocabulary start stages) :
    body.ballot ∈ StageBudget.ledger vocabulary start stages := by
  obtain ⟨row, present, included⟩ := List.mem_flatMap.mp inside
  obtain ⟨position, bounded, made⟩ := List.mem_filterMap.mp included
  have legacy := (issued_binds_the_complete_original_request vocabulary row position body made).1
  exact List.mem_flatMap.mpr ⟨row, present, List.mem_filterMap.mpr ⟨position, bounded, legacy⟩⟩

theorem source_rejection_cannot_become_a_statement (row : StageTrace.Record (code := code)) (position : Nat)
    (reason : OwnedAttestation.Rejection) (rejected : StageBudget.outcome vocabulary row position = .rejected reason) :
    outcome vocabulary row position = .rejected (.source reason) ∧ issued vocabulary row position = none := by
  constructor <;> simp only [outcome, rejected, issued]

theorem a_nonprotocol_request_cannot_become_a_statement
    (row : StageTrace.Record (code := code)) (position : Nat)
    (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument)
    (actual : (StageTrace.items row)[position]? = some item) (outside : protocolSyntax item.request = false) :
    issued vocabulary row position = none := by
  cases legacy : StageBudget.outcome vocabulary row position with
  | rejected reason => simp only [issued, outcome, legacy]
  | attested ballot => simp only [issued, outcome, legacy, actual, outside, Bool.false_eq_true, if_false]

theorem native_mandate_requests_are_outside_the_vote_syntax
    (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (signer : Party) (command : Mandate.Command Party) :
    protocolSyntax (Mandate.request model.scope current signer command) = false := rfl

theorem deleting_the_actual_source_deletes_all_statements (start : Cursor code) : ledger vocabulary start [] = [] := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestAttestation
