import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)

theorem a_checked_migration_executes_its_front_and_fixes_its_own_tail
    (checked : Actual.Migration.Checks input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair) :
    (compile input depth count prefixLimit renewalLimit current (.migrate pair)).isAccepted input depth count prefixLimit renewalLimit current = true ∧
    requests input depth count prefixLimit renewalLimit current (.migrate pair) = pair.1 ∧
    (next input depth count prefixLimit renewalLimit current (.migrate pair)).raw = input.law.next current.raw pair.1 ∧
    (next input depth count prefixLimit renewalLimit current (.migrate pair)).phase = .renewal pair.2 := by
  obtain ⟨proof, inspected⟩ := Actual.Migration.inspect_selects_every_checked_pair input (Actual.origin input depth count)
    current.raw (Actual.members input depth count) pair checked
  simp only [compile, inspected, Result.isAccepted, requests, Result.requests, Actual.Command.requests,
    next, Result.next, Actual.Command.next, and_self]

theorem a_refused_migration_executes_neither_prefix_nor_tail
    (issue : Actual.Migration.Issue input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair)
    (refused : Actual.Migration.inspect input (Actual.origin input depth count) current.raw
      (Actual.members input depth count) pair = .refused issue) :
    next input depth count prefixLimit renewalLimit current (.migrate pair) = current ∧
    (execution input depth count prefixLimit renewalLimit current (.migrate pair)).items = [] := by
  simp only [next, compile, refused, Result.next, execution, Result.execution, Result.requests,
    refusalRequests, RawLaw.execute, and_self]

theorem an_unchecked_migration_cannot_start
    (failed : ¬ Actual.Migration.Checks input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair) :
    next input depth count prefixLimit renewalLimit current (.migrate pair) = current ∧
    (execution input depth count prefixLimit renewalLimit current (.migrate pair)).items = [] := by
  cases inspected : Actual.Migration.inspect input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair with
  | accepted checked => exact (failed checked).elim
  | refused issue =>
      exact a_refused_migration_executes_neither_prefix_nor_tail
        input depth count prefixLimit renewalLimit current pair issue inspected

#print axioms a_checked_migration_executes_its_front_and_fixes_its_own_tail
#print axioms a_refused_migration_executes_neither_prefix_nor_tail
#print axioms an_unchecked_migration_cannot_start

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile
