import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit : Nat)

namespace AttemptAt

variable {current : RawCurrent Party Good Technology Instrument}
  {focus : Focus (Party := Party) (Good := Good) (Port := Port)}
  {remaining : List (Request Party Good Port Technology Instrument)}
  (attempt : AttemptAt input depth count current focus remaining)

inductive Followup : Type
  | ready (plan : Material.Migration.Plan input (Migration.origin input depth count) (attempt.after input)
      (Migration.cohort input depth count) prefixLimit renewalLimit)
      (produced : attempt.reassess input depth count prefixLimit renewalLimit = .accepted plan)
  | obstructed (issue : Material.Migration.Obstruction input (Migration.origin input depth count) (attempt.after input)
      (Migration.cohort input depth count) prefixLimit renewalLimit)
      (produced : attempt.reassess input depth count prefixLimit renewalLimit = .obstructed issue)
      (choice : Choice input depth count (attempt.after input)
        (obstructionFocus input depth count prefixLimit renewalLimit issue) attempt.tail)

/-- The next attempt consumes the remaining original code. It never reloads
the alphabet to present a refused request as a fresh pending responsibility. -/
def followup : Followup input depth count prefixLimit renewalLimit attempt :=
  match produced : attempt.reassess input depth count prefixLimit renewalLimit with
  | .accepted plan => .ready plan produced
  | .obstructed issue => .obstructed issue produced
      (choose input depth count (attempt.after input)
        (obstructionFocus input depth count prefixLimit renewalLimit issue) attempt.tail)

theorem following_attempt_uses_a_strictly_smaller_original_inventory
    (issue : Material.Migration.Obstruction input (Migration.origin input depth count) (attempt.after input)
      (Migration.cohort input depth count) prefixLimit renewalLimit)
    (nextAttempt : AttemptAt input depth count (attempt.after input)
      (obstructionFocus input depth count prefixLimit renewalLimit issue) attempt.tail) :
    nextAttempt.request ∈ attempt.tail ∧ nextAttempt.tail.length < attempt.tail.length ∧
      attempt.tail.length < remaining.length :=
  ⟨nextAttempt.original, attempted_inventory_strictly_decreases input depth count nextAttempt,
    attempted_inventory_strictly_decreases input depth count attempt⟩

end AttemptAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair
