import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Prefix
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
variable (start : Cursor seed driver)

abbrev pointFor (words : List (List (Future.Recovery.Action start.model))) := start.submitPrefix words

theorem at_depth (words : List (List (Future.Recovery.Action start.model))) :
    (pointFor start words).depth = start.depth+words.length := by
  change start.source.val.history.length+1+(start.count+words.length) = start.source.val.history.length+1+start.count+words.length
  omega

theorem at_word (words : List (List (Future.Recovery.Action start.model))) (index : Nat) (inside : index < words.length) :
    ((pointFor start words).source.val.actualExecution (start.depth+index)).submitted = words[index] := by
  cases words with
  | nil => simp at inside
  | cons head tail => exact start.install_word (head::tail) index inside

theorem at_current (words : List (List (Future.Recovery.Action start.model))) (index : Nat) (inside : index ≤ words.length) :
    (pointFor start words).source.val.currentAt (start.depth+index+1) =
      (words.take index).foldl start.source.val.code.law.next start.state.current := by
  cases words with
  | nil =>
    have zero : index = 0 := by simpa using inside
    subst index
    exact start.aligned.symm
  | cons head tail => exact start.install_current (head::tail) index inside

theorem at_keeps_the_complete_raw_observation (words : List (List (Future.Recovery.Action start.model))) :
    (pointFor start words).state.history = start.state.history ++ words ∧
    (pointFor start words).state.frame.word = start.state.frame.word ++ words.flatten ∧
    (pointFor start words).state.remaining = start.state.remaining ∧
    (pointFor start words).feedbackIndex = start.feedbackIndex ∧
    (pointFor start words).state.past = start.state.past ∧
    (pointFor start words).state.frame.inbox = start.state.frame.inbox ∧
    (pointFor start words).state.frame.sent = start.state.frame.sent := by
  cases words <;> simp [pointFor,Cursor.submitPrefix]

def reindex (reference : Term start) (words : List (List (Future.Recovery.Action start.model))) : Term (pointFor start words) :=
  ⟨reference.val,by change reference.val ∈ controls start;exact reference.property⟩

variable (actor : Party) (position : Nat)
structure Bill where
  private mk ::
  before : List (List (Future.Recovery.Action start.model))
  units : Nat
  fee : Future.Recovery.Action start.model
  registered : feeAt (pointFor start before) actor position = some fee
  payment : Mandate.Replay.Path (base := start.model.base) start.model.scope (pointFor start before).state.current
    [Prepaid.scaled (pointFor start before) fee units]
  payment_exact : payment = Mandate.Replay.compile start.model.base start.model.scope (pointFor start before).state.current
    [Prepaid.scaled (pointFor start before) fee units]

def quote (before : List (List (Future.Recovery.Action start.model))) (units : Nat) : Option {bill : Bill start actor position // bill.before = before ∧ bill.units = units} :=
  match registered : feeAt (pointFor start before) actor position with
  | none => none
  | some fee => some ⟨⟨before,units,fee,registered,
      Mandate.Replay.compile start.model.base start.model.scope (pointFor start before).state.current
        [Prepaid.scaled (pointFor start before) fee units],rfl⟩,rfl,rfl⟩

def Bill.reprice {start : Cursor seed driver} {actor : Party} {position : Nat}
    (bill : Bill start actor position) (units : Nat) : Bill start actor position :=
  ⟨bill.before,units,bill.fee,bill.registered,
    Mandate.Replay.compile start.model.base start.model.scope (pointFor start bill.before).state.current
      [Prepaid.scaled (pointFor start bill.before) bill.fee units],rfl⟩

def ownWords := words (Future.Recovery.Search.menu start.model actor) start.source.val.code.actionLimit

structure Own where
  private mk ::
  before : List (List (Future.Recovery.Action start.model))
  requested : List (Future.Recovery.Action start.model)
  registered : requested ∈ ownWords start actor
  execution : Mandate.Replay.Path (base := start.model.base) start.model.scope
    (pointFor start before).state.current requested
  execution_exact : execution = Mandate.Replay.compile start.model.base start.model.scope
    (pointFor start before).state.current requested

namespace Own
variable {start actor} (own : Own start actor)
theorem requested_is_personal : Mandate.Replay.Personal actor own.requested := by
  intro request inside
  exact Future.Recovery.Search.every_registered_repair_is_personally_signed start.model actor request
    (((mem_words_iff _ _ _).mp own.registered).2 request inside)

theorem output_is_personal : Mandate.Replay.Personal actor own.execution.output :=
  own.execution.output_preserves_personal_signature_control actor own.requested_is_personal

theorem original_requests_are_exactly_consumed_or_residual :
    own.execution.consumed ++ own.execution.residual = own.requested :=
  own.execution.original_split
end Own

def ownCandidates (before : List (List (Future.Recovery.Action start.model))) : List (Own start actor) :=
  (ownWords start actor).attach.map fun word =>
    ⟨before,word.val,word.property,Mandate.Replay.compile start.model.base start.model.scope
      (pointFor start before).state.current word.val,rfl⟩

/-- Issue one received request directly, without selecting a hidden-state-dependent candidate. -/
def issue (before : List (List (Future.Recovery.Action start.model)))
    (word : List (Future.Recovery.Action start.model)) :
    Option {own : Own start actor // own.before = before ∧ own.requested = word} :=
  if registered : word ∈ ownWords start actor then
    some ⟨⟨before,word,registered,Mandate.Replay.compile start.model.base start.model.scope
      (pointFor start before).state.current word,rfl⟩,rfl,rfl⟩
  else none

theorem issue_is_some_exactly_for_registered_personal_words
    (before : List (List (Future.Recovery.Action start.model)))
    (word : List (Future.Recovery.Action start.model)) :
    (issue start actor before word).isSome = true ↔ word ∈ ownWords start actor := by
  unfold issue
  split <;> simp_all

theorem own_words_are_exactly_bounded_personal_requests
    (word : List (Future.Recovery.Action start.model)) :
    word ∈ ownWords start actor ↔
      word ∈ words start.source.val.code.actions start.source.val.code.actionLimit ∧
      Mandate.Replay.Personal actor word := by
  constructor
  · intro registered
    obtain ⟨bound,inside⟩ := (mem_words_iff _ _ _).mp registered
    refine ⟨(mem_words_iff _ _ _).mpr ⟨bound,?_⟩,?_⟩
    · intro request member
      exact (List.mem_filter.mp (inside request member)).1
    · intro request member
      exact Future.Recovery.Search.every_registered_repair_is_personally_signed start.model actor request
        (inside request member)
  · rintro ⟨bounded,personal⟩
    obtain ⟨bound,inside⟩ := (mem_words_iff _ _ _).mp bounded
    exact (mem_words_iff _ _ _).mpr ⟨bound,fun request member =>
      List.mem_filter.mpr ⟨inside request member,decide_eq_true (personal request member)⟩⟩

theorem every_personal_registered_word_is_generated
    (before : List (List (Future.Recovery.Action start.model)))
    (word : List (Future.Recovery.Action start.model))
    (bounded : word ∈ words start.source.val.code.actions start.source.val.code.actionLimit)
    (personal : Mandate.Replay.Personal actor word) :
    ∃ own ∈ ownCandidates start actor before, own.before = before ∧ own.requested = word := by
  have supported : word ∈ ownWords start actor := by
    obtain ⟨length,registered⟩ := (mem_words_iff _ _ _).mp bounded
    apply (mem_words_iff _ _ _).mpr
    refine ⟨length,?_⟩
    intro request inside
    exact List.mem_filter.mpr ⟨registered request inside,decide_eq_true (personal request inside)⟩
  refine ⟨⟨before,word,supported,Mandate.Replay.compile start.model.base start.model.scope
    (pointFor start before).state.current word,rfl⟩,?_,rfl,rfl⟩
  exact List.mem_map.mpr ⟨⟨word,supported⟩,List.mem_attach _ _,rfl⟩

inductive Entry where
  | bill (value : Bill start actor position)
  | action (value : Own start actor)

namespace Entry
variable {start actor position}
def before : Entry start actor position → List (List (Future.Recovery.Action start.model))
  | .bill invoice => invoice.before
  | .action own => own.before
def output : Entry start actor position → List (Future.Recovery.Action start.model)
  | .bill invoice => invoice.payment.output
  | .action own => own.execution.output
end Entry

structure Journal where
  private mk ::
  entries : List (Entry start actor position)
  ordered : ∀ index (inside : index < entries.length),
    (entries[index]'inside).before = (entries.take index).map Entry.output

def empty : Journal start actor position := ⟨[],by simp⟩
namespace Journal
variable {start actor position} (journal : Journal start actor position)
abbrev words := journal.entries.map Entry.output
abbrev point := pointFor start journal.words

def bills : List (Bill start actor position) := journal.entries.filterMap fun entry =>
  match entry with | .bill invoice => some invoice | .action _ => none

def appendEntry (entry : Entry start actor position) (same : entry.before = journal.words) : Journal start actor position :=
  ⟨journal.entries ++ [entry],by
    intro index inside
    by_cases earlier : index < journal.entries.length
    · rw [List.getElem_append_left earlier,List.take_append_of_le_length (Nat.le_of_lt earlier)]
      exact journal.ordered index earlier
    · have last : index = journal.entries.length := by simp only [List.length_append,List.length_singleton] at inside;omega
      subst index
      simpa using same⟩

def append (bill : Bill start actor position) (same : bill.before = journal.words) : Journal start actor position :=
  journal.appendEntry (.bill bill) same

def appendOwn (own : Own start actor) (same : own.before = journal.words) : Journal start actor position :=
  journal.appendEntry (.action own) same

theorem append_words (bill : Bill start actor position) (same : bill.before = journal.words) :
    (journal.append bill same).words = journal.words ++ [bill.payment.output] := by
  change (journal.entries ++ [Entry.bill bill]).map Entry.output = _
  simp only [List.map_append,List.map_cons,List.map_nil,Entry.output]

theorem appendOwn_words (own : Own start actor) (same : own.before = journal.words) :
    (journal.appendOwn own same).words = journal.words ++ [own.execution.output] := by
  change (journal.entries ++ [Entry.action own]).map Entry.output = _
  simp only [List.map_append,List.map_cons,List.map_nil,Entry.output]

theorem every_entry_is_its_actual_source_word (index : Nat) (inside : index < journal.entries.length) :
    (journal.point.source.val.actualExecution (start.depth+index)).submitted = (journal.entries[index]'inside).output := by
  have actual := at_word start journal.words index (by simpa using inside)
  simpa using actual

theorem each_entry_has_its_own_actual_before (index : Nat) (inside : index < journal.entries.length) :
    journal.point.source.val.currentAt (start.depth+index+1) =
      (pointFor start (journal.entries[index]'inside).before).state.current := by
  have actual := at_current start journal.words index (by simpa using Nat.le_of_lt inside)
  rw [journal.ordered index inside]
  simpa only [pointFor,Cursor.submitPrefix,words,List.map_take] using actual
end Journal
/-- A branch-local invoice is quoted at the actual output of this own action. -/
structure Settlement where
  private mk ::
  own : Own start actor
  units : Nat
  quoted : Option {bill : Bill start actor position //
    bill.before = own.before ++ [own.execution.output] ∧ bill.units = units}
  quoted_exact : quoted = quote start actor position (own.before ++ [own.execution.output]) units

def settle (own : Own start actor) (units : Nat) : Settlement start actor position :=
  ⟨own,units,quote start actor position (own.before ++ [own.execution.output]) units,rfl⟩

namespace Settlement
variable {start actor position} (made : Settlement start actor position)
def words : List (List (Future.Recovery.Action start.model)) :=
  made.own.before ++ [made.own.execution.output] ++
    (made.quoted.map (fun bill => bill.val.payment.output)).toList

def paid : Bool := (made.quoted.map (fun bill => bill.val.payment.succeeded)).getD false

def appendTo (journal : Journal start actor position) (same : made.own.before = journal.words) :
    Journal start actor position :=
  let after := journal.appendOwn made.own same
  match made.quoted with
  | none => after
  | some bill => after.append bill.val (by
      rw [journal.appendOwn_words]
      exact bill.property.1.trans (congrArg (· ++ [made.own.execution.output]) same))

theorem appendTo_words (journal : Journal start actor position) (same : made.own.before = journal.words) :
    (made.appendTo journal same).words = made.words := by
  unfold appendTo words
  cases quoted : made.quoted with
  | none => simp only [Option.map_none,Option.toList_none,List.append_nil]
            exact (journal.appendOwn_words made.own same).trans (congrArg (· ++ [made.own.execution.output]) same.symm)
  | some bill =>
    simp only [Option.map_some,Option.toList_some]
    rw [Journal.append_words,Journal.appendOwn_words]
    exact congrArg (fun before => before ++ [made.own.execution.output] ++ [bill.val.payment.output]) same.symm

theorem each_settlement_is_quoted_after_its_own_actual_action :
    made.quoted = quote start actor position (made.own.before ++ [made.own.execution.output]) made.units :=
  made.quoted_exact

theorem the_original_action_requests_and_first_refusal_are_retained :
    made.own.execution.consumed ++ made.own.execution.residual = made.own.requested :=
  made.own.original_requests_are_exactly_consumed_or_residual
end Settlement

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Prefix
