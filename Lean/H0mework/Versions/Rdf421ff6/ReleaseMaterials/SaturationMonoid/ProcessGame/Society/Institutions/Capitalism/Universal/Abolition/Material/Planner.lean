import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Context
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Issues

/-!
# Source-bound finite migration-period compiler

The original occurrence supplies the actual after-current, complete old
cohort and request alphabet. A finite search generates an admissible period
or an original-data diagnosis for every candidate in the stated domain.
The instruction limit bounds this domain; it is not a paid-review budget or
a theorem that no larger/unknown technological programme can exist.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program Source.ProgrammeControl.Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

private inductive Search (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (candidates : List (RawEvent Party Good Port Technology Instrument)) where
  | accepted (word : RawEvent Party Good Port Technology Instrument)
      (generated : word ∈ candidates) (checked : PeriodChecks input current members word)
  | rejected (diagnoses : List (Sigma (PeriodIssue input current members)))
      (complete : ∀ word ∈ candidates, ∃ issue : PeriodIssue input current members word,
        ⟨word, issue⟩ ∈ diagnoses)

private def search (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) :
    (candidates : List (RawEvent Party Good Port Technology Instrument)) → Search input current members candidates
  | [] => .rejected [] (by simp)
  | word :: tail => match checkPeriod input current members word with
    | .accepted checked => .accepted word List.mem_cons_self checked
    | .rejected issue => match search current members tail with
      | .accepted other generated checked =>
          .accepted other (List.mem_cons_of_mem _ generated) checked
      | .rejected diagnoses complete =>
          .rejected (⟨word, issue⟩ :: diagnoses) (by
            intro candidate member
            rcases List.mem_cons.mp member with same | previous
            · subst candidate
              exact ⟨issue, List.mem_cons_self⟩
            · obtain ⟨oldIssue, present⟩ := complete candidate previous
              exact ⟨oldIssue, List.mem_cons_of_mem _ present⟩)

/-- Raw source kernel used by a registered successor epoch. Its caller must
read `current/members/candidates` from that epoch's source; no checked result
or target state is an input. The original-visit facade below is one binding. -/
structure RawPeriodPlanAt (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (candidates : List (RawEvent Party Good Port Technology Instrument)) where
  private mk ::
  word : RawEvent Party Good Port Technology Instrument
  generated : word ∈ candidates
  checked : PeriodChecks input current members word

structure RawPeriodObstructionAt (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (candidates : List (RawEvent Party Good Port Technology Instrument)) where
  private mk ::
  diagnoses : List (Sigma (PeriodIssue input current members))
  complete : ∀ word ∈ candidates, ∃ issue : PeriodIssue input current members word,
    ⟨word, issue⟩ ∈ diagnoses

inductive RawPeriodOutcomeAt (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (candidates : List (RawEvent Party Good Port Technology Instrument)) where
  | accepted (plan : RawPeriodPlanAt input current members candidates)
  | obstructed (obstruction : RawPeriodObstructionAt input current members candidates)

def compileRawPeriod (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (candidates : List (RawEvent Party Good Port Technology Instrument)) :
    RawPeriodOutcomeAt input current members candidates :=
  match search input current members candidates with
  | .accepted word generated checked => .accepted ⟨word, generated, checked⟩
  | .rejected diagnoses complete => .obstructed ⟨diagnoses, complete⟩

theorem compileRawPeriod_selects_when_available
    (current : RawCurrent Party Good Technology Instrument) (members : List Party)
    (candidates : List (RawEvent Party Good Port Technology Instrument))
    (available : ∃ word ∈ candidates, PeriodChecks input current members word) :
    ∃ plan, compileRawPeriod input current members candidates = .accepted plan := by
  cases outcome : compileRawPeriod input current members candidates with
  | accepted plan => exact ⟨plan, rfl⟩
  | obstructed obstruction =>
      obtain ⟨word, present, checked⟩ := available
      obtain ⟨issue, _inside⟩ := obstruction.complete word present
      exact (issue.refutes input current members word checked).elim

variable (visit : RootFace.Visit input) (instructionLimit : Nat)

structure PeriodPlanAt where
  private mk ::
  word : RawEvent Party Good Port Technology Instrument
  generated : word ∈ candidateWords input visit instructionLimit
  checked : PeriodChecks input (reviewCurrent input visit) (originalMembers input visit) word

structure PeriodObstructionAt where
  private mk ::
  diagnoses : List (Sigma (PeriodIssue input (reviewCurrent input visit) (originalMembers input visit)))
  complete : ∀ word ∈ candidateWords input visit instructionLimit,
    ∃ issue : PeriodIssue input (reviewCurrent input visit) (originalMembers input visit) word,
      ⟨word, issue⟩ ∈ diagnoses

inductive PeriodOutcomeAt where
  | accepted (plan : PeriodPlanAt input visit instructionLimit)
  | obstructed (obstruction : PeriodObstructionAt input visit instructionLimit)

/-- Actual execution is a separate source action. Returning a plan does not
make it the old emitter's word or create its target occurrence. -/
def compilePeriodAt : PeriodOutcomeAt input visit instructionLimit :=
  match compileRawPeriod input (reviewCurrent input visit) (originalMembers input visit)
      (candidateWords input visit instructionLimit) with
  | .accepted plan => .accepted ⟨plan.word, plan.generated, plan.checked⟩
  | .obstructed obstruction => .obstructed ⟨obstruction.diagnoses, obstruction.complete⟩

namespace PeriodPlanAt
variable {input visit instructionLimit}
  (plan : PeriodPlanAt input visit instructionLimit)

def next := input.law.next (reviewCurrent input visit) plan.word

theorem source_domain : plan.word.length ≤ instructionLimit ∧
    ∀ request ∈ plan.word, request ∈ availableRequests input visit :=
  (candidateWords_complete input visit instructionLimit plan.word).mp plan.generated

theorem pays_original_member (person : Party) (original : person ∈ originalMembers input visit) :
    Exit.Necessity.BundlePaid input.law (reviewCurrent input visit) plan.word person
      (input.law.necessities (reviewCurrent input visit) person) .necessity ∧
    Exit.Necessity.BundlePaid input.law (reviewCurrent input visit) plan.word person
      (input.law.mandatoryMaintenance (reviewCurrent input visit) person) .maintenance :=
  checked_candidate_keeps_original_life input visit plan.word plan.checked person original

theorem original_claims_accounted (code : Instrument) (debtor creditor : Party) :
    plan.next.claims code debtor creditor = (reviewCurrent input visit).claims code debtor creditor +
      (plan.word.map (fun request => RawLaw.claimDelta request code debtor creditor)).sum :=
  checked_period_financial_balance input _ _ plan.word plan.checked code debtor creditor

end PeriodPlanAt

namespace PeriodObstructionAt
variable {input visit instructionLimit}
  (obstruction : PeriodObstructionAt input visit instructionLimit)

include obstruction in
theorem no_checked_candidate (word : RawEvent Party Good Port Technology Instrument)
    (generated : word ∈ candidateWords input visit instructionLimit) :
    ¬ PeriodChecks input (reviewCurrent input visit) (originalMembers input visit) word := by
  obtain ⟨issue, _inside⟩ := obstruction.complete word generated
  exact issue.refutes input _ _ word

end PeriodObstructionAt

/-- Completeness is exactly the source-generated finite domain. A valid
candidate cannot be vetoed by the planner or reported as obstruction. -/
theorem compilePeriodAt_selects_when_available
    (available : ∃ word ∈ candidateWords input visit instructionLimit,
      PeriodChecks input (reviewCurrent input visit) (originalMembers input visit) word) :
    ∃ plan, compilePeriodAt input visit instructionLimit = .accepted plan := by
  cases outcome : compilePeriodAt input visit instructionLimit with
  | accepted plan => exact ⟨plan, rfl⟩
  | obstructed obstruction =>
      obtain ⟨word, generated, checked⟩ := available
      exact (obstruction.no_checked_candidate word generated checked).elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.compileRawPeriod
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.compilePeriodAt
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.compilePeriodAt_selects_when_available
