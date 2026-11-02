import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- A fixed application vocabulary, interpreted only at an actual owned activation.
The epoch is read from source state; a purpose label alone grants no authority. -/
structure Vocabulary where
  decode : Port → Option (Scope × Bool)
  epoch : RawCurrent Party Good (Mandate.State Party Technology) Instrument → Nat
  feeUnit : Good

structure BallotData (Actor : Type) (sites : Nat) where
  cut : Nat
  position : Nat
  key : Fin sites
  actor : Actor
  scope : Scope
  choice : Bool
  fee : ℚ
  deriving DecidableEq

inductive Rejection where
  | notOwnedActivation | missingItem | unlabelled | expired | wrongSigner | invalid | unpaid
  deriving DecidableEq

inductive OutcomeData (Body : Type) where
  | rejected (reason : Rejection)
  | attested (body : Body)
  deriving DecidableEq

variable (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat) (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev actual := Distributed.Recall.Information.Agency.Protocol.target source input cut protocol rival
abbrev localState (n : Nat) := Distributed.Recall.Information.Agency.Protocol.state source input cut protocol rival n
abbrev execution (n : Nat) := (actual source input cut protocol rival).actualExecution
  (source.history.length + 1 + (cut + n))
abbrev Ballot := BallotData Party source.code.sites

def owner (n : Nat) : Option (Fin source.code.sites) :=
  if source.continuation.isEmpty then
    if n < (source.feedbackState input cut).remaining then
      match Distributed.Recall.Information.Agency.ownerAt source.code (Distributed.Recall.Information.Agency.start source cut)
          (localState source input cut protocol rival n).history.length with
      | none => none
      | some site =>
        match Distributed.Recall.Information.Agency.Protocol.localEvent source.code protocol site
            ((localState source input cut protocol rival n).frame.inbox site) with
        | none => none
        | some event => if event.val = .activate site then some site else none
    else none
  else none

def classify (n position : Nat) (site : Fin source.code.sites)
    (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument) :
    OutcomeData (Ballot source) :=
  match vocabulary.decode item.request.purpose with
  | none => .rejected .unlabelled
  | some (scope, choice) =>
      if scope.epoch ≠ vocabulary.epoch item.before then .rejected .expired
      else if item.request.signer ≠ source.code.siteParty site then .rejected .wrongSigner
      else if ¬ source.code.law.Valid item.before item.request then .rejected .invalid
      else
        let fee := flowAt (source.code.law.actualDebit item.before item.request)
          (source.code.siteParty site) vocabulary.feeUnit
        if 0 < fee then .attested ⟨n, position, site, source.code.siteParty site, scope, choice, fee⟩
        else .rejected .unpaid

def inspect (n position : Nat) : OutcomeData (Ballot source) :=
  match owner source input cut protocol rival n with
  | none => .rejected .notOwnedActivation
  | some site =>
      match (source.code.law.rawItems (execution source input cut protocol rival n).before
          (execution source input cut protocol rival n).submitted)[position]? with
      | none => .rejected .missingItem
      | some item => classify source vocabulary n position site item

def issuedAt (n position : Nat) : Option (Ballot source) :=
  match inspect source input cut protocol rival vocabulary n position with
  | .rejected _ => none
  | .attested body => some body

def verify (candidate : Ballot source) : Bool :=
  decide (issuedAt source input cut protocol rival vocabulary candidate.cut candidate.position = some candidate)

/-- Original items survive application rejection and external impersonation. -/
def audit (n : Nat) :=
  let actual := execution source input cut protocol rival n
  (source.code.law.rawItems actual.before actual.submitted).mapIdx fun position item =>
    (item, inspect source input cut protocol rival vocabulary n position)

theorem owned_origin_has_no_preloaded_continuation (n : Nat) (site : Fin source.code.sites)
    (generated : owner source input cut protocol rival n = some site) : source.continuation = [] := by
  cases present : source.continuation with
  | nil => rfl
  | cons head tail => simp [owner, present] at generated

theorem every_original_request_is_retained (n : Nat) :
    (audit source input cut protocol rival vocabulary n).map (fun row => row.1.request) =
      (execution source input cut protocol rival n).submitted := by
  calc
    _ = (source.code.law.rawItems (execution source input cut protocol rival n).before
        (execution source input cut protocol rival n).submitted).map ExecutionItem.request := by
      apply List.ext_getElem?
      intro i
      simp [audit, Function.comp_def]
    _ = _ := source.code.law.inventory_requests_exact _ 0 _

theorem owned_activation_is_actual_selected_local_work
    (empty : source.continuation = []) (n : Nat) (site : Fin source.code.sites)
    (generated : owner source input cut protocol rival n = some site) :
    (execution source input cut protocol rival n).submitted = source.code.action protocol.work.val site
      ((localState source input cut protocol rival n).frame.inbox site) := by
  simp only [owner, empty, List.isEmpty_nil, if_true] at generated
  split at generated <;> try contradiction
  rename_i bounded
  split at generated <;> try contradiction
  rename_i worker owned
  split at generated <;> try contradiction
  rename_i event chosen
  split at generated <;> try contradiction
  rename_i activation
  have same := Option.some.inj generated
  subst site
  exact Distributed.Recall.Information.Agency.Protocol.actual_own_activation_submits_the_selected_local_work source input cut protocol rival
    empty n bounded worker owned event chosen activation

theorem attested_has_owned_paid_origin (n position : Nat) (body : Ballot source)
    (generated : issuedAt source input cut protocol rival vocabulary n position = some body) :
    ∃ site item,
      owner source input cut protocol rival n = some site ∧
      (source.code.law.rawItems (execution source input cut protocol rival n).before
        (execution source input cut protocol rival n).submitted)[position]? = some item ∧
      source.code.law.Valid item.before item.request ∧
      item.request.signer = source.code.siteParty site ∧
      vocabulary.decode item.request.purpose = some (body.scope, body.choice) ∧
      body.scope.epoch = vocabulary.epoch item.before ∧
      body.cut = n ∧ body.position = position ∧ body.key = site ∧
      body.actor = source.code.siteParty site ∧
      body.fee = flowAt (source.code.law.actualDebit item.before item.request)
        body.actor vocabulary.feeUnit ∧ 0 < body.fee := by
  have inspected : inspect source input cut protocol rival vocabulary n position = .attested body := by
    unfold issuedAt at generated
    split at generated <;> try contradiction
    rename_i produced classified
    have same := Option.some.inj generated
    subst body
    exact classified
  unfold inspect at inspected
  split at inspected <;> try contradiction
  rename_i site owned
  split at inspected <;> try contradiction
  rename_i item actualItem
  unfold classify at inspected
  split at inspected <;> try contradiction
  rename_i scope choice labelled
  dsimp only at inspected
  split_ifs at inspected with expired signer invalid paid
  have same := OutcomeData.attested.inj inspected
  subst body
  exact ⟨site, item, owned, actualItem, by simpa only [not_not] using invalid,
    by simpa only [not_not] using signer, labelled,
    by simpa only [not_not] using expired, rfl, rfl, rfl, rfl, rfl, paid⟩

def ledger (horizon : Nat) : List (Ballot source) :=
  (List.range horizon).flatMap fun n =>
    (List.range (execution source input cut protocol rival n).submitted.length).filterMap fun position =>
      issuedAt source input cut protocol rival vocabulary n position

theorem ledger_members_are_independently_verifiable (horizon : Nat) (body : Ballot source)
    (inside : body ∈ ledger source input cut protocol rival vocabulary horizon) :
    verify source input cut protocol rival vocabulary body = true := by
  obtain ⟨n, _, included⟩ := List.mem_flatMap.mp inside
  obtain ⟨position, _, issued⟩ := List.mem_filterMap.mp included
  obtain ⟨_, _, _, _, _, _, _, _, coordinates, address, _⟩ :=
    attested_has_owned_paid_origin source input cut protocol rival vocabulary n position body issued
  simp only [verify, coordinates, address, issued, decide_true]

def conflicts (left right : Ballot source) : Bool :=
  decide (left.key = right.key ∧ left.scope = right.scope ∧ left.choice ≠ right.choice)

def evidence (horizon : Nat) :=
  let ballots := ledger source input cut protocol rival vocabulary horizon
  ballots.flatMap fun left => (ballots.filter fun right => conflicts source left right).map (left, ·)

theorem evidence_contains_two_actual_verified_conflicting_ballots
    (horizon : Nat) (left right : Ballot source)
    (inside : (left, right) ∈ evidence source input cut protocol rival vocabulary horizon) :
    verify source input cut protocol rival vocabulary left = true ∧
      verify source input cut protocol rival vocabulary right = true ∧
      left.key = right.key ∧ left.scope = right.scope ∧ left.choice ≠ right.choice := by
  obtain ⟨first, firstInside, pairInside⟩ := List.mem_flatMap.mp inside
  obtain ⟨second, filtered, pair⟩ := List.mem_map.mp pairInside
  cases pair
  obtain ⟨secondInside, conflict⟩ := List.mem_filter.mp filtered
  exact ⟨ledger_members_are_independently_verifiable source input cut protocol rival vocabulary horizon left firstInside,
    ledger_members_are_independently_verifiable source input cut protocol rival vocabulary horizon right secondInside,
    of_decide_eq_true conflict⟩

theorem different_phases_are_not_equivocation (left right : Ballot source)
    (different : left.scope.phase ≠ right.scope.phase) : conflicts source left right = false := by
  simp only [conflicts, decide_eq_false_iff_not]
  rintro ⟨_, same, _⟩
  exact different (congrArg Scope.phase same)

theorem external_turn_cannot_generate_attestation (n position : Nat)
    (external : Distributed.Recall.Information.Agency.ownerAt source.code (Distributed.Recall.Information.Agency.start source cut)
      (localState source input cut protocol rival n).history.length = none) :
    issuedAt source input cut protocol rival vocabulary n position = none := by
  simp [issuedAt, inspect, owner, external]


end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation
