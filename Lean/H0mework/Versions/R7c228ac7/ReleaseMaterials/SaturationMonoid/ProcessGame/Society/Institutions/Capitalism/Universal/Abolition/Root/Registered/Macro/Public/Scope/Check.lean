import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

structure Failure (raw : Compile.RawInput Party Good Port Technology Instrument) where
  word : RawEvent Party Good Port Technology Instrument
  selected : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = some word
  issue : Review.Guarded.Issue (checkInput input) (Actual.origin input depth count)
    (actualState input depth count prefixLimit renewalLimit oldPast current).raw
    (scope input depth count prefixLimit renewalLimit oldPast current word) word

theorem Failure.refutes {raw : Compile.RawInput Party Good Port Technology Instrument}
    (failure : Failure input depth count prefixLimit renewalLimit oldPast current raw) :
    ¬ Checks input depth count prefixLimit renewalLimit oldPast current failure.word :=
  failure.issue.refutes _ _ _ _ _

inductive Decision (raw : Compile.RawInput Party Good Port Technology Instrument) : Type
  | delegated (noPeriod : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = none)
  | accepted (word : RawEvent Party Good Port Technology Instrument)
      (selected : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = some word)
      (checked : Checks input depth count prefixLimit renewalLimit oldPast current word)
  | rejected (failure : Failure input depth count prefixLimit renewalLimit oldPast current raw)

/-- The complete standing and current public word are source readouts;
neither a successful period nor a replacement actor list is input. -/
def inspect (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Decision input depth count prefixLimit renewalLimit oldPast current raw :=
  match selected : periodWord? input depth count prefixLimit renewalLimit oldPast current raw with
  | none => .delegated selected
  | some word =>
      match Review.Guarded.inspect (checkInput input) (Actual.origin input depth count)
          (actualState input depth count prefixLimit renewalLimit oldPast current).raw
          (scope input depth count prefixLimit renewalLimit oldPast current word) word with
      | .accepted checked => .accepted word selected checked
      | .rejected issue => .rejected ⟨word, selected, issue⟩

theorem every_checked_actual_period_is_accepted
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = some word)
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current word) :
    ∃ source proof, inspect input depth count prefixLimit renewalLimit oldPast current raw = .accepted word source proof := by
  cases result : inspect input depth count prefixLimit renewalLimit oldPast current raw with
  | delegated absent =>
      rw [selected] at absent
      contradiction
  | accepted actual source proof =>
      have same : actual = word := Option.some.inj (source.symm.trans selected)
      cases same
      exact ⟨source, proof, rfl⟩
  | rejected failure =>
      have same : failure.word = word := Option.some.inj (failure.selected.symm.trans selected)
      exact (failure.refutes input depth count prefixLimit renewalLimit oldPast current (same.symm ▸ checked)).elim

#print axioms inspect
#print axioms Failure.refutes
#print axioms every_checked_actual_period_is_accepted

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope
