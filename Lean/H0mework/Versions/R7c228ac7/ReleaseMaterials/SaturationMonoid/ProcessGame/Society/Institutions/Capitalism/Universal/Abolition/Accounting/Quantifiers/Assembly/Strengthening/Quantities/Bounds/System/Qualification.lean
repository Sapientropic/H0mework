import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System

noncomputable section

universe u v w

variable {Candidate : Type u} {Index : Type v} {Issue : Index → Candidate → Type w}

def Passes (check : (index : Index) → (candidate : Candidate) → Option (Issue index candidate))
    (candidate : Candidate) : Prop :=
  ∀ index, check index candidate = none

abbrev Failure (check : (index : Index) → (candidate : Candidate) → Option (Issue index candidate))
    (candidate : Candidate) :=
  Σ index, { issue : Issue index candidate // check index candidate = some issue }

private theorem hasFailure
    (check : (index : Index) → (candidate : Candidate) → Option (Issue index candidate))
    (candidate : Candidate) (rejected : ¬ Passes check candidate) : Nonempty (Failure check candidate) := by
  classical
  obtain ⟨index, missing⟩ := not_forall.mp rejected
  cases found : check index candidate with
  | none => exact (missing found).elim
  | some issue => exact ⟨⟨index, issue, found⟩⟩

/-- One indexed failure explains why the simultaneous constraint fails.
The source program itself is kept for whole-account disposition. -/
def inspect (check : (index : Index) → (candidate : Candidate) → Option (Issue index candidate))
    (candidate : Candidate) : Option (Failure check candidate) := by
  classical
  exact if passes : Passes check candidate then none else some (Classical.choice (hasFailure check candidate passes))

theorem all_checks_pass_exactly_when_there_is_no_failure
    (check : (index : Index) → (candidate : Candidate) → Option (Issue index candidate))
    (candidate : Candidate) :
    inspect check candidate = none ↔ Passes check candidate := by
  classical
  by_cases passes : Passes check candidate <;> simp [inspect, passes]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System
