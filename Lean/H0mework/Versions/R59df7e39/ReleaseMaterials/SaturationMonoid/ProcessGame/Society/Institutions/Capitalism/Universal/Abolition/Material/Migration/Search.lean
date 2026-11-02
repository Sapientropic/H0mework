import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Sustainable

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)

def PairChecks (pair : CodePair Party Good Port Technology Instrument) : Prop :=
  PrefixChecks input origin current members pair.1 ∧
  RenewalChecks input origin (input.law.next current pair.1) members pair.2

instance (pair : CodePair Party Good Port Technology Instrument) :
    Decidable (PairChecks input origin current members pair) := by unfold PairChecks; infer_instance

inductive PairIssue (pair : CodePair Party Good Port Technology Instrument) : Type
  | prefixFailure (issue : PrefixIssue input origin current members pair.1)
  | renewal (issue : RenewalIssue input origin (input.law.next current pair.1) members pair.2)

theorem PairIssue.refutes {pair : CodePair Party Good Port Technology Instrument}
    (issue : PairIssue input origin current members pair) : ¬ PairChecks input origin current members pair := by
  intro checked
  cases issue with
  | prefixFailure issue => exact issue.refutes input origin current members pair.1 checked.1
  | renewal issue => exact issue.refutes input origin _ members pair.2 checked.2

inductive PairDecision (pair : CodePair Party Good Port Technology Instrument) : Type
  | accepted (checked : PairChecks input origin current members pair)
  | rejected (issue : PairIssue input origin current members pair)

def checkPair (pair : CodePair Party Good Port Technology Instrument) :
    PairDecision input origin current members pair :=
  match checkPrefix input origin current members pair.1 with
  | .rejected issue => .rejected (.prefixFailure issue)
  | .accepted front => match checkRenewal input origin (input.law.next current pair.1) members pair.2 with
    | .rejected issue => .rejected (.renewal issue)
    | .accepted renewal => .accepted ⟨front, renewal⟩

private inductive Search (candidates : List (CodePair Party Good Port Technology Instrument)) : Type
  | accepted (pair : CodePair Party Good Port Technology Instrument)
      (generated : pair ∈ candidates) (checked : PairChecks input origin current members pair)
  | rejected (diagnoses : List (Sigma (PairIssue input origin current members)))
      (complete : ∀ pair ∈ candidates, ∃ issue : PairIssue input origin current members pair,
        ⟨pair, issue⟩ ∈ diagnoses)

private def search : (candidates : List (CodePair Party Good Port Technology Instrument)) →
    Search input origin current members candidates
  | [] => .rejected [] (by simp)
  | pair :: remaining => match checkPair input origin current members pair with
    | .accepted checked => .accepted pair List.mem_cons_self checked
    | .rejected issue => match search remaining with
      | .accepted other generated checked => .accepted other (List.mem_cons_of_mem _ generated) checked
      | .rejected diagnoses complete => .rejected (⟨pair, issue⟩ :: diagnoses) (by
          intro candidate original
          rcases List.mem_cons.mp original with same | previous
          · subst candidate
            exact ⟨issue, List.mem_cons_self⟩
          · obtain ⟨prior, present⟩ := complete candidate previous
            exact ⟨prior, List.mem_cons_of_mem _ present⟩)

/-- Check a prefix before constructing its continuation candidates. A bad
prefix rules out its entire finite subtree; that subtree is expanded into
diagnostics only when no later prefix succeeds. -/
private def searchPrefixes (renewalLimit : Nat) :
    (fronts : List (RawEvent Party Good Port Technology Instrument)) →
    Search input origin current members (fronts.flatMap fun front =>
      (sourceWords input (input.law.next current front) renewalLimit).map (fun tail => (front, tail)))
  | [] => .rejected [] (by simp)
  | front :: remaining =>
      match checkPrefix input origin current members front with
      | .rejected issue =>
          match searchPrefixes renewalLimit remaining with
          | .accepted pair generated checked => .accepted pair (List.mem_append_right _ generated) checked
          | .rejected diagnostics complete =>
              let head := (sourceWords input (input.law.next current front) renewalLimit).map
                (fun tail => (⟨(front, tail), PairIssue.prefixFailure issue⟩ : Sigma (PairIssue input origin current members)))
              .rejected (head ++ diagnostics) (by
                intro pair present
                rcases List.mem_append.mp present with first | later
                · obtain ⟨tail, source, same⟩ := List.mem_map.mp first
                  cases same
                  exact ⟨PairIssue.prefixFailure issue, List.mem_append_left _ (List.mem_map.mpr ⟨tail, source, rfl⟩)⟩
                · obtain ⟨prior, presentIssue⟩ := complete pair later
                  exact ⟨prior, List.mem_append_right _ presentIssue⟩)
      | .accepted _ =>
          match search input origin current members
              ((sourceWords input (input.law.next current front) renewalLimit).map (fun tail => (front, tail))) with
          | .accepted pair generated checked => .accepted pair (List.mem_append_left _ generated) checked
          | .rejected firstDiagnostics firstComplete =>
              match searchPrefixes renewalLimit remaining with
              | .accepted pair generated checked => .accepted pair (List.mem_append_right _ generated) checked
              | .rejected diagnostics complete => .rejected (firstDiagnostics ++ diagnostics) (by
                  intro pair present
                  rcases List.mem_append.mp present with first | later
                  · obtain ⟨issue, presentIssue⟩ := firstComplete pair first
                    exact ⟨issue, List.mem_append_left _ presentIssue⟩
                  · obtain ⟨issue, presentIssue⟩ := complete pair later
                    exact ⟨issue, List.mem_append_right _ presentIssue⟩)

variable (prefixLimit renewalLimit : Nat)

structure Plan where
  private mk ::
  pair : CodePair Party Good Port Technology Instrument
  generated : pair ∈ sourcePairs input current prefixLimit renewalLimit
  checked : PairChecks input origin current members pair

/-- A finite source code is checked here, before the private plan is built.
No successful checks, material target or continuation are caller inputs. -/
def inspectPlan (pair : CodePair Party Good Port Technology Instrument)
    (generated : pair ∈ sourcePairs input current prefixLimit renewalLimit) :
    Option (Plan input origin current members prefixLimit renewalLimit) :=
  match checkPair input origin current members pair with
  | .accepted checked => some ⟨pair, generated, checked⟩
  | .rejected _ => none

theorem inspectPlan_returns_exactly_the_checked_source_code
    (pair : CodePair Party Good Port Technology Instrument)
    (generated : pair ∈ sourcePairs input current prefixLimit renewalLimit)
    (checked : PairChecks input origin current members pair) :
    ∃ plan, inspectPlan input origin current members prefixLimit renewalLimit pair generated = some plan ∧ plan.pair = pair := by
  unfold inspectPlan
  cases result : checkPair input origin current members pair with
  | accepted accepted => exact ⟨_, rfl, rfl⟩
  | rejected issue => exact (issue.refutes input origin current members checked).elim

structure Obstruction where
  private mk ::
  diagnoses : List (Sigma (PairIssue input origin current members))
  complete : ∀ pair ∈ sourcePairs input current prefixLimit renewalLimit,
    ∃ issue : PairIssue input origin current members pair, ⟨pair, issue⟩ ∈ diagnoses

inductive Outcome : Type
  | accepted (plan : Plan input origin current members prefixLimit renewalLimit)
  | obstructed (obstruction : Obstruction input origin current members prefixLimit renewalLimit)

/-- Source code, finite limits and the original cohort are the only inputs.
The successful pair, target resources and future programme are outputs. -/
def compileMigration : Outcome input origin current members prefixLimit renewalLimit :=
  match searchPrefixes input origin current members renewalLimit (sourceWords input current prefixLimit) with
  | .accepted pair generated checked => .accepted ⟨pair, generated, checked⟩
  | .rejected diagnoses complete => .obstructed ⟨diagnoses, complete⟩

theorem compile_selects_when_available
    (available : ∃ pair ∈ sourcePairs input current prefixLimit renewalLimit,
      PairChecks input origin current members pair) :
    ∃ plan, compileMigration input origin current members prefixLimit renewalLimit = .accepted plan := by
  cases outcome : compileMigration input origin current members prefixLimit renewalLimit with
  | accepted plan => exact ⟨plan, rfl⟩
  | obstructed obstruction =>
      obtain ⟨pair, generated, checked⟩ := available
      obtain ⟨issue, _original⟩ := obstruction.complete pair generated
      exact (issue.refutes input origin current members checked).elim

theorem compile_obstructs_exactly_when_no_admitted_pair :
    (∃ obstruction, compileMigration input origin current members prefixLimit renewalLimit = .obstructed obstruction) ↔
      ∀ pair ∈ sourcePairs input current prefixLimit renewalLimit, ¬ PairChecks input origin current members pair := by
  constructor
  · rintro ⟨obstruction, _produced⟩ pair original checked
    obtain ⟨issue, _listed⟩ := obstruction.complete pair original
    exact issue.refutes input origin current members checked
  · intro noneAdmitted
    cases result : compileMigration input origin current members prefixLimit renewalLimit with
    | obstructed obstruction => exact ⟨obstruction, rfl⟩
    | accepted plan => exact (noneAdmitted plan.pair plan.generated plan.checked).elim

theorem Plan.every_generated_period
    (plan : Plan input origin current members prefixLimit renewalLimit)
    (timing : input.law.TimeIndependent) (policy : input.law.ReserveInsensitive) (n : Nat) :
    let target := input.law.next current plan.pair.1
    let after := (Continuation.repeatPeriod input target plan.pair.2).currentAt n
    PeriodChecks input after members plan.pair.2 ∧
      OriginalNeedFloor input origin after members plan.pair.2 ∧ after.claims = current.claims := by
  have sustained := renewal_generates_every_finite_period input timing policy origin
    (input.law.next current plan.pair.1) members plan.pair.2 plan.checked.2 n
  exact ⟨sustained.1, sustained.2.1,
    sustained.2.2.trans (plan.checked.1.2.2.2.1.next_claims input.law current plan.pair.1)⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.compile_selects_when_available
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Plan.every_generated_period
