import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Release
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Cuts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate
open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

theorem ActualCommand.recognize_complete
    {current : RawCurrent Party Good (State Party Technology) Instrument}
    {word : RawEvent Party Good Port (State Party Technology) Instrument}
    (actual : ActualCommand base scope current word) : recognize base scope current word actual.item = some actual := by
  cases actual
  next item operator target command operation marked accepted =>
    unfold recognize
    split
    · rename_i operator' target' operation'
      have linked := operation.symm.trans operation'
      injection linked with sameOperator sameTarget
      subst operator'
      subst target'
      split
      · rename_i noneMarked
        rw [marked] at noneMarked
        cases noneMarked
      · rename_i command' marked'
        have sameCommand := Option.some.inj (marked.symm.trans marked')
        subst command'
        simp only [dif_pos accepted]
    all_goals simp_all

def ActualCommand.reindex
    {current otherCurrent : RawCurrent Party Good (State Party Technology) Instrument}
    {word otherWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : otherCurrent = current) (sameWord : otherWord = word)
    (actual : ActualCommand base scope current word) : ActualCommand base scope otherCurrent otherWord := by
  cases sameCurrent
  cases sameWord
  exact actual

theorem ActualCommand.reindex_facts
    {current otherCurrent : RawCurrent Party Good (State Party Technology) Instrument}
    {word otherWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : otherCurrent = current) (sameWord : otherWord = word)
    (actual : ActualCommand base scope current word) :
    (actual.reindex sameCurrent sameWord).item.val = actual.item.val ∧
    (actual.reindex sameCurrent sameWord).command = actual.command := by
  cases sameCurrent
  cases sameWord
  exact ⟨rfl,rfl⟩

namespace Lifecycle.Observed
variable {currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat} {grant : Grant base scope (currentAt birth) (wordAt birth)}

theorem History.consume_eq_of_not_revise
    (history : History base scope currentAt wordAt birth grant)
    (visit : Nat)
    (item : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)})
    (notRevise : ∀ operator target, item.val.request.operation ≠ .revise operator target) :
    history.consume visit item = history := by
  unfold History.consume
  cases recognized : recognize base scope (currentAt visit) (wordAt visit) item with
  | some actual =>
      have item_eq : actual.item = item := by
        simp only [recognize] at recognized
        cases recognized
      have operation := actual.operation
      rw [item_eq] at operation
      exact False.elim (notRevise actual.operator actual.target operation)
  | none =>
      simp only [readEvent, recognized]

theorem History.foldl_consume_eq_of_not_revise
    (history : History base scope currentAt wordAt birth grant)
    (visit : Nat)
    (items : List {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)})
    (notRevise : ∀ item ∈ items, ∀ operator target,
      item.val.request.operation ≠ .revise operator target) :
    items.foldl (fun prior item => prior.consume visit item) history = history := by
  induction items generalizing history with
  | nil => rfl
  | cons item rest ih =>
      rw [List.foldl_cons, History.consume_eq_of_not_revise history visit item
        (notRevise item (by simp))]
      apply ih
      intro next member operator target
      exact notRevise next (by simp [member]) operator target

end Lifecycle.Observed

namespace Lifecycle.Observed.Release
variable {currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat} {grant : Grant base scope (currentAt birth) (wordAt birth)}

theorem read_isSome_iff
    (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length) :
    (read history visit index).isSome = true ↔
    (readEvent (before history visit index).obligation (before history visit index).origin visit
      ((items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index)).map isRelease = some true := by
  unfold read
  split
  · rename_i found
    conv_rhs => rw [found]
    simp
  · rename_i event found
    conv_rhs => rw [found]
    simp only [Option.map_some]
    split
    · rename_i released
      simp only [Option.isSome_some, released]
    · rename_i denied
      simp only [Option.isSome_none, Bool.false_eq_true, Option.some.injEq]
      exact iff_of_false (by intro impossible; cases impossible) denied

theorem actual_paid_exit_is_read
    (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length)
    (actual : ActualCommand base scope (currentAt visit) (wordAt visit))
    (item : actual.item = (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index)
    (exiting : actual.command = .exit)
    (held : actual.item.val.before.technology.holder = some (before history visit index).obligation.bearer)
    (later : birth < visit) : (read history visit index).isSome = true := by
  have follows : Later base scope currentAt wordAt birth grant visit actual.item.val.index := Or.inl later
  have boundary : IsBoundary actual.command := by rw [exiting]; trivial
  have ended : actual.after.technology.holder ≠ some (before history visit index).obligation.bearer := by
    rw [actual.actual_effect.1,exiting]
    change (none : Option Party) ≠ some _
    intro impossible
    cases impossible
  have released := And.intro held ended
  rw [read_isSome_iff]
  rw [show readEvent (before history visit index).obligation (before history visit index).origin visit
      ((items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index) =
      readEvent (before history visit index).obligation (before history visit index).origin visit actual.item from congrArg _ item.symm]
  simp only [readEvent,actual.recognize_complete,Lifecycle.readEvent,dif_pos follows,dif_pos boundary,Option.map_some]
  simp only [isRelease,Event.disposition,acceptedDisposition]
  split_ifs with condition
  · rfl
  · exact False.elim (condition released)

private def attachedRun (history : History base scope currentAt wordAt birth grant)
    (visit : Nat)
    (xs : List {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    (process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run
      history.state (xs.foldl (fun prior item => prior.consume visit item) history).state := by
  induction xs generalizing history with
  | nil => exact .nil
  | cons item rest ih =>
      exact (history.consumeRun visit item).concatRuns _
        (ih (history.consume visit item))

theorem Receipt.actual_visit_run
    {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) visit).length}
    (receipt : Receipt history visit index) :
    ∃ (prefixRun : (process (base := base) (scope := scope) (currentAt := currentAt)
        (wordAt := wordAt) (birth := birth) (grant := grant)).Run
        history.state (before history visit index).state)
      (suffixRun : (process (base := base) (scope := scope) (currentAt := currentAt)
        (wordAt := wordAt) (birth := birth) (grant := grant)).Run
        ((before history visit index).cross receipt.event).state (history.visit visit).state),
      let wholeRun := prefixRun.concatRuns _ (receipt.crossing.concatRuns _ suffixRun)
      (history.visit visit).state.history = history.state.history ++ wholeRun.events ∧
        ((before history visit index).edge receipt.event).lifecycleEvent ∈ wholeRun.events ∧
        ((before history visit index).edge receipt.event).lifecycleEvent.kind = .bearerRelease := by
  let xs := items (base := base) (scope := scope) (currentAt := currentAt)
    (wordAt := wordAt) visit
  let n := index.val
  have split : xs.take n ++ (xs.get index :: xs.drop (n + 1)) = xs := by
    calc
      xs.take n ++ (xs.get index :: xs.drop (n + 1)) = xs.take n ++ xs.drop n := by
        exact congrArg (fun rest => xs.take n ++ rest) (List.getElem_cons_drop index.isLt)
      _ = xs := List.take_append_drop n xs
  let priorHistory := history.visitPrefix visit n
  have prefix_eq : priorHistory = before history visit index := rfl
  have folded :
      (xs.drop (n + 1)).foldl (fun prior item => prior.consume visit item)
        ((before history visit index).cross receipt.event) = history.visit visit := by
    change (xs.drop (n + 1)).foldl (fun prior item => prior.consume visit item)
        ((before history visit index).cross receipt.event) =
      xs.foldl (fun prior item => prior.consume visit item) history
    have hfold := congrArg
      (fun ys : List {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)} =>
        ys.foldl (fun prior item => prior.consume visit item) history) split
    simp only [List.foldl_append, List.foldl_cons] at hfold
    have prefixFold : (xs.take n).foldl (fun prior item => prior.consume visit item) history =
        before history visit index := by rfl
    rw [prefixFold] at hfold
    rw [receipt.is_the_actual_consumption] at hfold
    exact hfold
  have foldedState := congrArg History.state folded
  have prefixEqState : priorHistory.state = (before history visit index).state :=
    congrArg History.state prefix_eq
  let prefixRun := prefixEqState ▸ attachedRun history visit (xs.take n)
  let suffixRun := foldedState ▸ attachedRun ((before history visit index).cross receipt.event)
    visit (xs.drop (n + 1))
  refine ⟨prefixRun, suffixRun, ?_, ?_, ?_⟩
  · exact (prefixRun.concatRuns _ (receipt.crossing.concatRuns _ suffixRun)).history_eq
  · rw [NativeResponsibilityProcess.Run.events_concatRuns]
    apply List.mem_append_right
    rw [NativeResponsibilityProcess.Run.events_concatRuns]
    apply List.mem_append_left
    simp [Receipt.crossing, NativeResponsibilityProcess.Run.events]
  · exact receipt.native_kind



theorem Receipt.is_recorded_in_the_actual_visit
    {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) visit).length} (receipt : Receipt history visit index) :
    ((before history visit index).edge receipt.event).lifecycleEvent ∈ (history.visit visit).state.history := by
  obtain ⟨prefixRun,suffixRun,whole,member,_kind⟩ := receipt.actual_visit_run
  rw [whole]
  exact List.mem_append_right _ member

end Lifecycle.Observed.Release
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate
