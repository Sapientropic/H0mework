import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageTrace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageBudget

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev Ballot := OwnedAttestation.BallotData Party code.sites

def outcome (row : StageTrace.Record (code := code)) (position : Nat) : OwnedAttestation.OutcomeData (Ballot (code := code)) :=
  match StageTrace.activation row with
  | none => .rejected .notOwnedActivation
  | some site => match (StageTrace.items row)[position]? with
    | none => .rejected .missingItem
    | some item => OwnedAttestation.classify row.cursor.source vocabulary row.cursor.cut position site item

def issued (row : StageTrace.Record (code := code)) (position : Nat) : Option (Ballot (code := code)) :=
  match outcome vocabulary row position with
  | .rejected _ => none
  | .attested ballot => some ballot

def ledger (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) : List (Ballot (code := code)) :=
  (StageTrace.records cursor stages).flatMap fun row =>
    (List.range row.submitted.length).filterMap (issued vocabulary row)

def verify (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (candidate : Ballot (code := code)) : Bool :=
  decide (candidate ∈ ledger vocabulary cursor stages)

theorem issued_has_an_owned_valid_paid_origin (row : StageTrace.Record (code := code))
    (position : Nat) (body : Ballot (code := code)) (made : issued vocabulary row position = some body) :
    ∃ site item, StageTrace.activation row = some site ∧ (StageTrace.items row)[position]? = some item ∧
      code.law.Valid item.before item.request ∧ item.request.signer = code.siteParty site ∧
      vocabulary.decode item.request.purpose = some (body.scope, body.choice) ∧
      body.scope.epoch = vocabulary.epoch item.before ∧ body.key = site ∧
      body.cut = row.cursor.cut ∧ body.position = position ∧
      body.fee = flowAt (code.law.actualDebit item.before item.request) (code.siteParty site) vocabulary.feeUnit ∧ 0 < body.fee := by
  have inspected : outcome vocabulary row position = .attested body := by
    unfold issued at made
    split at made <;> try contradiction
    rename_i produced classified
    cases Option.some.inj made
    exact classified
  unfold outcome at inspected
  split at inspected <;> try contradiction
  rename_i site owned
  split at inspected <;> try contradiction
  rename_i item actual
  unfold OwnedAttestation.classify at inspected
  split at inspected <;> try contradiction
  rename_i scope choice labelled
  dsimp only at inspected
  split_ifs at inspected with expired signer invalid paid
  cases OwnedAttestation.OutcomeData.attested.inj inspected
  exact ⟨site, item, owned, actual, by simpa only [not_not] using invalid,
    by simpa only [not_not] using signer, labelled, by simpa only [not_not] using expired,
    rfl, rfl, rfl, rfl, paid⟩

theorem ledger_origin (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : Ballot (code := code)) (inside : body ∈ ledger vocabulary cursor stages) :
    ∃ row ∈ StageTrace.records cursor stages, ∃ position, issued vocabulary row position = some body := by
  obtain ⟨row, included, generated⟩ := List.mem_flatMap.mp inside
  obtain ⟨position, _, made⟩ := List.mem_filterMap.mp generated
  exact ⟨row, included, position, made⟩

def labels (row : StageTrace.Record (code := code)) (key : Fin code.sites) :=
  (code.action row.protocol.work.val key (row.before.frame.inbox key)).filterMap
    (DeviationBudget.labelFor row.cursor.source vocabulary key)

def liveRecords (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :=
  (StageTrace.records cursor stages).filter fun row => row.before.remaining ≠ 0

theorem issued_is_in_the_actual_installed_local_word
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (row : StageTrace.Record (code := code)) (inside : row ∈ StageTrace.records cursor stages)
    (position : Nat) (body : Ballot (code := code)) (made : issued vocabulary row position = some body) :
    row ∈ liveRecords cursor stages ∧ StageTrace.activation row = some body.key ∧
      (body.scope, body.choice) ∈ labels vocabulary row body.key := by
  obtain ⟨site, item, owned, actual, _, signer, decoded, _, key, _⟩ := issued_has_an_owned_valid_paid_origin vocabulary row position body made
  obtain ⟨pastStages, protocol, rival, suffix, _, same⟩ := StageTrace.every_record_retains_its_actual_stage cursor stages row inside
  subst row
  have word := StageTrace.an_owned_activation_submits_its_selected_work _ protocol rival site owned
  have requestIn : item.request ∈ (StageTrace.material (EventHistory.execute cursor pastStages) protocol rival).submitted := by
    have requests := code.law.inventory_requests_exact
      (StageTrace.material (EventHistory.execute cursor pastStages) protocol rival).before.current 0
      (StageTrace.material (EventHistory.execute cursor pastStages) protocol rival).submitted
    rw [← requests]
    exact List.mem_map.mpr ⟨item, List.mem_of_getElem? actual, rfl⟩
  refine ⟨List.mem_filter.mpr ⟨inside, by simpa using word.1⟩, by simpa only [key] using owned, ?_⟩
  rw [word.2] at requestIn
  rw [key]
  refine List.mem_filterMap.mpr ⟨item.request, requestIn, ?_⟩
  simp only [DeviationBudget.labelFor, if_pos signer, decoded]

def capacityKeys (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) : Finset (Fin code.sites) :=
  let rows := liveRecords cursor stages
  Finset.univ.filter fun key =>
    (rows.product rows).any (fun pair => decide (labels vocabulary pair.1 key ≠ labels vocabulary pair.2 key)) ||
      rows.any (fun row => decide (StageTrace.activation row = some key ∧
        DeviationBudget.contradictory (labels vocabulary row key) = true))

theorem capacity_key_iff (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (key : Fin code.sites) :
    key ∈ capacityKeys vocabulary cursor stages ↔
      (∃ first ∈ liveRecords cursor stages, ∃ second ∈ liveRecords cursor stages,
        labels vocabulary first key ≠ labels vocabulary second key) ∨
      (∃ row ∈ liveRecords cursor stages, StageTrace.activation row = some key ∧
        DeviationBudget.contradictory (labels vocabulary row key) = true) := by
  simp [capacityKeys, List.any_eq_true]
  constructor
  · rintro (⟨first, second, ⟨one, two⟩, different⟩ | hazard)
    · exact Or.inl ⟨first, one, second, two, different⟩
    · exact Or.inr hazard
  · rintro (⟨first, one, second, two, different⟩ | hazard)
    · exact Or.inl ⟨first, second, ⟨one, two⟩, different⟩
    · exact Or.inr hazard

def conflicts (first second : Ballot (code := code)) : Bool :=
  decide (first.key = second.key ∧ first.scope = second.scope ∧ first.choice ≠ second.choice)

def evidence (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :=
  ((ledger vocabulary cursor stages).product (ledger vocabulary cursor stages)).filter fun pair => conflicts pair.1 pair.2

def evidenceKeys (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) : Finset (Fin code.sites) :=
  ((evidence vocabulary cursor stages).map (fun pair => pair.1.key)).toFinset

abbrev budget (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :=
  (capacityKeys vocabulary cursor stages).card

theorem every_actual_equivocation_is_covered_by_the_source_capacity_budget
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (first second : Ballot (code := code))
    (one : first ∈ ledger vocabulary cursor stages) (two : second ∈ ledger vocabulary cursor stages)
    (key : first.key = second.key) (scope : first.scope = second.scope) (different : first.choice ≠ second.choice) :
    first.key ∈ capacityKeys vocabulary cursor stages := by
  obtain ⟨left, leftIn, a, aMade⟩ := ledger_origin vocabulary cursor stages first one
  obtain ⟨right, rightIn, b, bMade⟩ := ledger_origin vocabulary cursor stages second two
  obtain ⟨leftLive, owned, firstLabel⟩ := issued_is_in_the_actual_installed_local_word vocabulary cursor stages left leftIn a first aMade
  obtain ⟨rightLive, _, secondLabel⟩ := issued_is_in_the_actual_installed_local_word vocabulary cursor stages right rightIn b second bMade
  apply (capacity_key_iff vocabulary cursor stages first.key).mpr
  by_cases changed : labels vocabulary left first.key = labels vocabulary right first.key
  · right
    refine ⟨left, leftLive, owned, (DeviationBudget.contradictory_iff _).mpr ?_⟩
    refine ⟨(first.scope, first.choice), firstLabel, (first.scope, second.choice), ?_, rfl, different⟩
    rw [changed, scope, key]
    exact secondLabel
  · exact Or.inl ⟨left, leftLive, right, rightLive, changed⟩

theorem actual_evidence_keys_are_within_the_generated_capacity_budget
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    evidenceKeys vocabulary cursor stages ⊆ capacityKeys vocabulary cursor stages := by
  intro key inside
  obtain ⟨pair, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp inside)
  obtain ⟨members, conflict⟩ := List.mem_filter.mp present
  obtain ⟨one, two⟩ := List.mem_product.mp members
  obtain ⟨keys, scope, different⟩ := of_decide_eq_true conflict
  rw [← same]
  exact every_actual_equivocation_is_covered_by_the_source_capacity_budget vocabulary cursor stages _ _ one two keys scope different

omit [DecidableEq Port] [DecidableEq Technology] in
theorem different_phases_are_not_equivocation (first second : Ballot (code := code))
    (different : first.scope.phase ≠ second.scope.phase) : conflicts first second = false := by
  simp only [conflicts, decide_eq_false_iff_not]
  rintro ⟨_, same, _⟩
  exact different (congrArg Scope.phase same)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageBudget
