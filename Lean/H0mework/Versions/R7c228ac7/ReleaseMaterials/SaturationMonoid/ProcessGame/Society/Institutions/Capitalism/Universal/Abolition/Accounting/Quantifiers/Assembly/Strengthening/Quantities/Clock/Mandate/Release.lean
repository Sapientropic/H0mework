import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate

open Source.Program PublicFunction PublicFunction.Mandate PublicFunction.Mandate.Lifecycle
open PublicFunction.Mandate.Lifecycle.Observed
open PublicFunction.Mandate.Lifecycle.Observed.Release (items before)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat} {grant : Grant base scope (currentAt birth) (wordAt birth)}

theorem paid_expiry_review_reaches_the_original_bearer_release
    (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length)
    (actual : ActualCommand base scope (currentAt visit) (wordAt visit))
    (item : actual.item = (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index)
    (review : actual.command = .review) (expired : scope.task.deadline < (currentAt visit).clock)
    (held : actual.item.val.before.technology.holder = some (before history visit index).obligation.bearer)
    (later : birth < visit) :
    (Release.read history visit index).isSome = true := by
  have follows : Later base scope currentAt wordAt birth grant visit actual.item.val.index := Or.inl later
  have boundary : IsBoundary actual.command := by rw [review]; trivial
  have released := (an_actual_paid_review_ends_expired_authority_and_keeps_claims actual review expired).1
  have ended : actual.after.technology.holder ≠ some (before history visit index).obligation.bearer := by
    rw [released]
    intro impossible
    cases impossible
  rw [Release.read_isSome_iff]
  rw [show Observed.readEvent (before history visit index).obligation (before history visit index).origin visit
    ((items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index) =
    Observed.readEvent (before history visit index).obligation (before history visit index).origin visit actual.item from congrArg _ item.symm]
  simp only [Observed.readEvent, actual.recognize_complete, Lifecycle.readEvent, dif_pos follows, dif_pos boundary, Option.map_some]
  simp only [Release.isRelease, Observed.Event.disposition, acceptedDisposition]
  split_ifs with condition
  · rfl
  · exact False.elim (condition ⟨held, ended⟩)

theorem paid_expiry_review_writes_the_original_lifecycle_visit
    (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length)
    (actual : ActualCommand base scope (currentAt visit) (wordAt visit))
    (item : actual.item = (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index)
    (review : actual.command = .review) (expired : scope.task.deadline < (currentAt visit).clock)
    (held : actual.item.val.before.technology.holder = some (before history visit index).obligation.bearer)
    (later : birth < visit) :
    ∃ receipt : Release.Receipt history visit index,
      Release.read history visit index = some receipt ∧ (type_of% receipt.actual_visit_run) := by
  have recorded := paid_expiry_review_reaches_the_original_bearer_release history visit index actual item review expired held later
  cases observed : Release.read history visit index with
  | none => rw [observed] at recorded; cases recorded
  | some receipt => exact ⟨receipt, rfl, receipt.actual_visit_run⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate
