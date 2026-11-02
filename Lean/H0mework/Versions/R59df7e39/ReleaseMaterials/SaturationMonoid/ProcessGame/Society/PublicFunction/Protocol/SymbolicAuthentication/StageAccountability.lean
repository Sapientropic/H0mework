import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDutyRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountability

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

abbrev Receipt := StageReception.Receipt (code := code)
abbrev Slot := Fin code.sites × Scope

def matchesSlot (slot : Slot (code := code)) (pair : Receipt (code := code) × Receipt (code := code)) : Bool :=
  decide (pair.1.wire.ballot.key = slot.1 ∧ pair.1.wire.ballot.scope = slot.2) &&
    StageBudget.conflicts pair.1.wire.ballot pair.2.wire.ballot

def query (receipts : List (Receipt (code := code))) (slot : Slot (code := code)) :=
  (receipts.product receipts).find? (matchesSlot slot)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem query_sound (receipts : List (Receipt (code := code))) (slot : Slot (code := code))
    (pair : Receipt (code := code) × Receipt (code := code)) (found : query receipts slot = some pair) :
    pair.1 ∈ receipts ∧ pair.2 ∈ receipts ∧ pair.1.wire.ballot.key = slot.1 ∧
      pair.1.wire.ballot.scope = slot.2 ∧ StageBudget.conflicts pair.1.wire.ballot pair.2.wire.ballot = true := by
  have members := List.mem_product.mp (List.mem_of_find?_eq_some found)
  have selected := List.find?_some (p := matchesSlot slot) found
  have facts : (pair.1.wire.ballot.key = slot.1 ∧ pair.1.wire.ballot.scope = slot.2) ∧
      StageBudget.conflicts pair.1.wire.ballot pair.2.wire.ballot = true := by
    simpa [matchesSlot] using selected
  exact ⟨members.1, members.2, facts.1.1, facts.1.2, facts.2⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem query_exists_iff (receipts : List (Receipt (code := code))) (slot : Slot (code := code)) :
    (∃ pair, query receipts slot = some pair) ↔
      ∃ first ∈ receipts, ∃ second ∈ receipts,
        first.wire.ballot.key = slot.1 ∧ first.wire.ballot.scope = slot.2 ∧
          StageBudget.conflicts first.wire.ballot second.wire.ballot = true := by
  constructor
  · rintro ⟨pair, found⟩
    have facts := query_sound receipts slot pair found
    exact ⟨pair.1, facts.1, pair.2, facts.2.1, facts.2.2⟩
  · rintro ⟨first, one, second, two, key, scope, conflict⟩
    cases found : query receipts slot with
    | some pair => exact ⟨pair, rfl⟩
    | none =>
      have absent := List.find?_eq_none.mp found (first, second) (List.mem_product.mpr ⟨one, two⟩)
      simp [matchesSlot, key, scope, conflict] at absent

abbrev receipts (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) :=
  (StageReception.run vocabulary encoding law cursor stages receiver stages.length).receipts

structure Incident where
  private mk ::
  pastStages : List (EventHistory.Stage (code := code))
  stage : EventHistory.Stage (code := code)
  receiver : Fin code.sites
  slot : Slot (code := code)
  pair : Receipt (code := code) × Receipt (code := code)
  detected : query (receipts cursor vocabulary encoding law (pastStages ++ [stage]) receiver) slot = some pair
  fresh : query (receipts cursor vocabulary encoding law pastStages receiver) slot = none

abbrev Incident.birthStages (entry : Incident cursor vocabulary encoding law) := entry.pastStages ++ [entry.stage]
abbrev Incident.nativeSource (entry : Incident cursor vocabulary encoding law) := (EventHistory.execute cursor entry.birthStages).source

def birth (pastStages : List (EventHistory.Stage (code := code))) (stage : EventHistory.Stage (code := code))
    (receiver : Fin code.sites) (slot : Slot (code := code)) : Option (Incident cursor vocabulary encoding law) :=
  if old : query (receipts cursor vocabulary encoding law pastStages receiver) slot = none then
    match found : query (receipts cursor vocabulary encoding law (pastStages ++ [stage]) receiver) slot with
    | none => none
    | some pair => some ⟨pastStages, stage, receiver, slot, pair, found, old⟩
  else none

def emit (pastStages : List (EventHistory.Stage (code := code))) (stage : EventHistory.Stage (code := code)) :=
  (List.finRange code.sites).flatMap fun receiver =>
    (((receipts cursor vocabulary encoding law (pastStages ++ [stage]) receiver).map
      (fun receipt => (receipt.wire.ballot.key, receipt.wire.ballot.scope))).eraseDups).filterMap
        (birth cursor vocabulary encoding law pastStages stage receiver)

def walk (pastStages : List (EventHistory.Stage (code := code))) :
    List (EventHistory.Stage (code := code)) → List (Incident cursor vocabulary encoding law)
  | [] => []
  | stage :: tail => emit cursor vocabulary encoding law pastStages stage ++
      walk (pastStages ++ [stage]) tail

def ledger (stages : List (EventHistory.Stage (code := code))) := walk cursor vocabulary encoding law [] stages

theorem from_append (pastStages first more : List (EventHistory.Stage (code := code))) :
    walk cursor vocabulary encoding law pastStages (first ++ more) =
      walk cursor vocabulary encoding law pastStages first ++
        walk cursor vocabulary encoding law (pastStages ++ first) more := by
  induction first generalizing pastStages with
  | nil => simp [walk]
  | cons stage tail ih => simp only [List.cons_append, walk, ih, List.append_assoc, List.nil_append]

theorem ledger_extends_by_its_generated_next (stages more : List (EventHistory.Stage (code := code))) :
    ledger cursor vocabulary encoding law (stages ++ more) =
      ledger cursor vocabulary encoding law stages ++ walk cursor vocabulary encoding law stages more := by
  simpa only [ledger, List.nil_append] using from_append cursor vocabulary encoding law [] stages more

theorem birth_retains_its_original_transition
    (pastStages : List (EventHistory.Stage (code := code))) (stage : EventHistory.Stage (code := code))
    (receiver : Fin code.sites) (slot : Slot (code := code)) (entry : Incident cursor vocabulary encoding law)
    (born : birth cursor vocabulary encoding law pastStages stage receiver slot = some entry) :
    entry.pastStages = pastStages ∧ entry.stage = stage ∧ entry.receiver = receiver ∧ entry.slot = slot := by
  unfold birth at born
  split at born <;> try contradiction
  split at born <;> try contradiction
  cases Option.some.inj born
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem every_generated_incident_has_its_original_birth_prefix
    (pastStages stages : List (EventHistory.Stage (code := code))) (entry : Incident cursor vocabulary encoding law)
    (inside : entry ∈ walk cursor vocabulary encoding law pastStages stages) :
    entry.birthStages <+: pastStages ++ stages := by
  induction stages generalizing pastStages with
  | nil => simp [walk] at inside
  | cons stage tail ih =>
    rcases List.mem_append.mp inside with now | later
    · obtain ⟨receiver, _, member⟩ := List.mem_flatMap.mp now
      obtain ⟨slot, _, born⟩ := List.mem_filterMap.mp member
      have original := birth_retains_its_original_transition cursor vocabulary encoding law pastStages stage receiver slot entry born
      refine ⟨tail, ?_⟩
      simp only [Incident.birthStages, original.1, original.2.1, List.append_assoc, List.singleton_append]
    · simpa only [List.append_assoc, List.singleton_append] using ih (pastStages ++ [stage]) later

theorem birth_is_generated_at_the_first_observed_conflict
    (pastStages : List (EventHistory.Stage (code := code))) (stage : EventHistory.Stage (code := code))
    (receiver : Fin code.sites) (slot : Slot (code := code))
    (old : query (receipts cursor vocabulary encoding law pastStages receiver) slot = none)
    (found : ∃ pair, query (receipts cursor vocabulary encoding law (pastStages ++ [stage]) receiver) slot = some pair) :
    ∃ entry ∈ emit cursor vocabulary encoding law pastStages stage, entry.receiver = receiver ∧ entry.slot = slot := by
  obtain ⟨pair, actual⟩ := found
  have facts := query_sound _ slot pair actual
  have candidate : slot ∈ ((receipts cursor vocabulary encoding law (pastStages ++ [stage]) receiver).map
      (fun receipt => (receipt.wire.ballot.key, receipt.wire.ballot.scope))).eraseDups := by
    apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨pair.1, facts.1, Prod.ext facts.2.2.1 facts.2.2.2.1⟩
  let entry : Incident cursor vocabulary encoding law := ⟨pastStages, stage, receiver, slot, pair, actual, old⟩
  have born : birth cursor vocabulary encoding law pastStages stage receiver slot = some entry := by
    unfold birth
    rw [dif_pos old]
    split
    · rename_i absent
      rw [actual] at absent
      contradiction
    · rename_i produced found
      have same : produced = pair := Option.some.inj (found.symm.trans actual)
      subst produced
      rfl
  exact ⟨entry, List.mem_flatMap.mpr ⟨receiver, List.mem_finRange _, List.mem_filterMap.mpr ⟨slot, candidate, born⟩⟩, rfl, rfl⟩

theorem every_locally_observed_conflict_generates_an_incident
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (slot : Slot (code := code)) :
    (∃ pair, query (receipts cursor vocabulary encoding law stages receiver) slot = some pair) →
      ∃ entry ∈ ledger cursor vocabulary encoding law stages, entry.receiver = receiver ∧ entry.slot = slot := by
  induction stages using List.reverseRecOn with
  | nil =>
    intro found
    obtain ⟨pair, actual⟩ := found
    change (none : Option (Receipt (code := code) × Receipt (code := code))) = some pair at actual
    contradiction
  | append_singleton past stage ih =>
    intro found
    cases previous : query (receipts cursor vocabulary encoding law past receiver) slot with
    | some pair =>
      obtain ⟨entry, inside, same⟩ := ih ⟨pair, previous⟩
      refine ⟨entry, ?_, same⟩
      rw [ledger_extends_by_its_generated_next]
      exact List.mem_append_left _ inside
    | none =>
      obtain ⟨entry, emitted, same⟩ := birth_is_generated_at_the_first_observed_conflict cursor vocabulary encoding law past stage receiver slot previous found
      refine ⟨entry, ?_, same⟩
      rw [ledger_extends_by_its_generated_next]
      exact List.mem_append_right _ (by simpa only [walk, List.append_nil] using emitted)

theorem later_stages_do_not_readmit_an_already_observed_incident
    (entry : Incident cursor vocabulary encoding law) (more : List (EventHistory.Stage (code := code)))
    (stage : EventHistory.Stage (code := code)) :
    birth cursor vocabulary encoding law (entry.birthStages ++ more) stage entry.receiver entry.slot = none := by
  have facts := query_sound _ entry.slot entry.pair entry.detected
  have preserved := StagePrefix.receipts_survive_actual_extension cursor entry.birthStages more vocabulary encoding law entry.receiver
  have found : ∃ pair, query (receipts cursor vocabulary encoding law (entry.birthStages ++ more) entry.receiver) entry.slot = some pair :=
    (query_exists_iff _ entry.slot).mpr ⟨entry.pair.1, preserved.subset facts.1, entry.pair.2,
      preserved.subset facts.2.1, facts.2.2⟩
  have present : query (receipts cursor vocabulary encoding law (entry.birthStages ++ more) entry.receiver) entry.slot ≠ none := by
    obtain ⟨pair, actual⟩ := found
    intro absent
    rw [absent] at actual
    contradiction
  simp only [birth, dif_neg present]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountability
