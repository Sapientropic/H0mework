import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Search
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.Context
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

abbrev frame := Admission.frame input depth count
abbrev N := Continuation.N input (frame input depth count)
def origin := Continuation.initial input (frame input depth count)
def cohort := Settlement.members input depth count

variable (prefixLimit renewalLimit : Nat)

abbrev Outcome := Material.Migration.Outcome input (origin input depth count) (origin input depth count)
  (cohort input depth count) prefixLimit renewalLimit

def selection : Outcome input depth count prefixLimit renewalLimit :=
  Material.Migration.compileMigration input (origin input depth count) (origin input depth count)
    (cohort input depth count) prefixLimit renewalLimit

inductive Assessment (current : RawCurrent Party Good Technology Instrument) : Type
  | obstruction (issue : Material.Migration.Obstruction input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
  | prefix (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
      (result : Material.Migration.PrefixDecision input (origin input depth count) current (cohort input depth count) plan.pair.1)
  | renewal (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
      (result : Review.Guarded.Check input (origin input depth count) current (cohort input depth count) plan.pair.2)

def Assessment.word {current : RawCurrent Party Good Technology Instrument} :
    Assessment input depth count prefixLimit renewalLimit current → Option (RawEvent Party Good Port Technology Instrument)
  | .obstruction _ => none
  | .prefix plan result => match result with
    | .accepted _ => some plan.pair.1
    | .rejected _ => none
  | .renewal plan result => match result with
    | .accepted _ => some plan.pair.2
    | .rejected _ => none

/-- Every later period is rechecked at its actual current. A changed need,
policy or permission produces the original typed issue without a period. -/
def assess (current : RawCurrent Party Good Technology Instrument) (index : Nat) :
    Assessment input depth count prefixLimit renewalLimit current :=
  match selection input depth count prefixLimit renewalLimit with
  | .obstructed issue => .obstruction issue
  | .accepted plan => if index = 0 then
      .prefix plan (Material.Migration.checkPrefix input (origin input depth count) current (cohort input depth count) plan.pair.1)
    else .renewal plan (Review.Guarded.inspect input (origin input depth count) current (cohort input depth count) plan.pair.2)

theorem assessed_prefix_is_paid
    (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
    (selected : selection input depth count prefixLimit renewalLimit = .accepted plan) :
    (assess input depth count prefixLimit renewalLimit (origin input depth count) 0).word input depth count prefixLimit renewalLimit =
      some plan.pair.1 := by
  cases checked : Material.Migration.checkPrefix input (origin input depth count) (origin input depth count)
      (cohort input depth count) plan.pair.1 with
  | accepted proof => simp [assess, selected, checked, Assessment.word]
  | rejected issue => exact (issue.refutes input _ _ _ _ plan.checked.1).elim

theorem assessed_renewal_is_paid
    (plan : Material.Migration.Plan input (origin input depth count) (origin input depth count)
      (cohort input depth count) prefixLimit renewalLimit)
    (selected : selection input depth count prefixLimit renewalLimit = .accepted plan)
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (checked : Review.Guarded.Checks input (origin input depth count) current (cohort input depth count) plan.pair.2) :
    (assess input depth count prefixLimit renewalLimit current (index + 1)).word input depth count prefixLimit renewalLimit =
      some plan.pair.2 := by
  obtain ⟨proof, observed⟩ := Review.Guarded.inspect_selects_checked input _ _ _ _ checked
  simp [assess, selected, observed, Assessment.word]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration
