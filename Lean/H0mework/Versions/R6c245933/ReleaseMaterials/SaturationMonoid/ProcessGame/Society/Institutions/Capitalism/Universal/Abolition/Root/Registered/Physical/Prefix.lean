import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Execution

/-! Canonical finite prefix occurrences, reconstructed solely from the raw
input past. Their equality with an activated macro history is a separate
consumer obligation; this fold does not assert that a supplied past occurred. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

variable {Party Good Port Technology Instrument : Type}

def cursor (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    Cursor Party Good Port Technology Instrument :=
  past.foldl (fun before raw => Physical.next (receive before raw)) Physical.initial

theorem cursor_append (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    cursor (past ++ [raw]) = Physical.next (receive (cursor past) raw) := by
  simp only [cursor, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem past_readback (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    (cursor past).past = past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past raw prior =>
      rw [cursor_append]
      change (cursor past).past ++ [raw] = past ++ [raw]
      rw [prior]

theorem incoming_is_fresh_advance (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    (cursor past).incoming = .advance := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past raw prior => rw [cursor_append]; rfl

theorem reconstructs_the_same_cursor (original : Cursor Party Good Port Technology Instrument) :
    receive (cursor original.past) original.incoming = original := by
  rcases original with ⟨past, incoming⟩
  unfold receive
  simp only [past_readback]

def eventCursor
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (position : Fin past.length) : Cursor Party Good Port Technology Instrument :=
  receive (cursor (past.take position.val)) (past.get position)

theorem event_readback
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (position : Fin past.length) :
    (eventCursor past position).past = past.take position.val ∧
      (eventCursor past position).incoming = past.get position :=
  ⟨past_readback _, rfl⟩

theorem input_order_is_exact
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    (List.ofFn fun position : Fin past.length => (eventCursor past position).incoming) = past :=
  List.ofFn_get past

theorem next_event_cursor_is_the_next_prefix
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (position : Fin past.length) :
    Physical.next (eventCursor past position) = cursor (past.take (position.val + 1)) := by
  rw [List.take_succ_eq_append_getElem position.isLt, cursor_append]
  rfl

noncomputable section

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
  (position : Fin past.length)

def source := sourceAt input depth count prefixLimit renewalLimit (eventCursor past position)
def root := ledgerRoot input depth count prefixLimit renewalLimit (eventCursor past position)
def visit := (root input depth count prefixLimit renewalLimit past position).toRoot.initialVisit

def occurrence := emitted input depth count prefixLimit renewalLimit (eventCursor past position) (eventCursor past position)

theorem initial_visit_is_the_original_event_cursor :
    (visit input depth count prefixLimit renewalLimit past position).current = eventCursor past position := rfl

theorem literal_source_and_initial_occurrence :
    (root input depth count prefixLimit renewalLimit past position).source.source =
        source input depth count prefixLimit renewalLimit past position ∧
      (root input depth count prefixLimit renewalLimit past position).emitted
        (visit input depth count prefixLimit renewalLimit past position).current =
          occurrence input depth count prefixLimit renewalLimit past position := ⟨rfl, rfl⟩

theorem original_execution_reads_this_prefix_only :
    execution input depth count prefixLimit renewalLimit (eventCursor past position) =
      Compile.execution input depth count prefixLimit renewalLimit
        (stateAt input depth count prefixLimit renewalLimit (past.take position.val)) (past.get position) := by
  unfold execution
  rw [(event_readback past position).1, (event_readback past position).2]

theorem source_next_is_the_prefix_successor :
    ((root input depth count prefixLimit renewalLimit past position).toRoot.evolutionAt
      (visit input depth count prefixLimit renewalLimit past position).current).nextCurrent? =
        some (Physical.next (eventCursor past position)) := by
  change ((sourceAt input depth count prefixLimit renewalLimit (eventCursor past position)).toRootSource.actual.compile
    (emitted input depth count prefixLimit renewalLimit (eventCursor past position) (eventCursor past position))).nextCurrent? = _
  rw [compiler_eq_source_choice]
  split <;> rfl

def afterVisit := (visit input depth count prefixLimit renewalLimit past position).next
  (source_next_is_the_prefix_successor input depth count prefixLimit renewalLimit past position)

theorem successor_visit_reads_the_next_prefix :
    (afterVisit input depth count prefixLimit renewalLimit past position).current = cursor (past.take (position.val + 1)) :=
  next_event_cursor_is_the_next_prefix past position

theorem next_prefix_is_the_same_physical_state :
    stateAt input depth count prefixLimit renewalLimit
        (afterVisit input depth count prefixLimit renewalLimit past position).current.past =
      stateAt input depth count prefixLimit renewalLimit (past.take (position.val + 1)) := by
  rw [successor_visit_reads_the_next_prefix, past_readback]

theorem original_requested_items_and_next_share_the_prefix :
    (execution input depth count prefixLimit renewalLimit (eventCursor past position)).items.map ExecutionItem.request =
        Compile.requests input depth count prefixLimit renewalLimit
          (stateAt input depth count prefixLimit renewalLimit (past.take position.val)) (past.get position) ∧
      stateAt input depth count prefixLimit renewalLimit (past.take (position.val + 1)) =
        Compile.next input depth count prefixLimit renewalLimit
          (stateAt input depth count prefixLimit renewalLimit (past.take position.val)) (past.get position) := by
  constructor
  · rw [original_execution_reads_this_prefix_only]
    exact Compile.compiled_requests_are_exactly_interpreted input depth count prefixLimit renewalLimit _ _
  · have after := consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit (eventCursor past position)
    rw [next_event_cursor_is_the_next_prefix, past_readback,
      (event_readback past position).1, (event_readback past position).2] at after
    exact after

#print axioms reconstructs_the_same_cursor
#print axioms input_order_is_exact
#print axioms literal_source_and_initial_occurrence
#print axioms source_next_is_the_prefix_successor
#print axioms original_requested_items_and_next_share_the_prefix

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix
