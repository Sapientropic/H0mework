import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat) (active : bound.source.feedback? = some input)

variable (empty : bound.source.continuation = [])

structure Candidate (reference : Term bound input cut) where
  term : Term bound input cut
  feasible : Cut.Feasible bound.source input cut term
  no_regression : NoWorse bound input cut active term reference

def acceptable (reference term : Term bound input cut) : Prop :=
  Cut.Feasible bound.source input cut term ∧ NoWorse bound input cut active term reference

instance (reference term : Term bound input cut) : Decidable (acceptable bound input cut active reference term) := by
  letI := decidableNoWorse bound input cut active term reference
  unfold acceptable
  infer_instance

def check (reference term : Term bound input cut) : Option (Candidate bound input cut active reference) :=
  if accepted : acceptable bound input cut active reference term then some ⟨term, accepted.1, accepted.2⟩ else none

def candidates (reference : Term bound input cut) :=
  (Cut.terms bound.source input cut).filterMap (check bound input cut active reference)

theorem every_accepted_term_is_generated (reference term : Term bound input cut)
    (accepted : acceptable bound input cut active reference term) :
    ∃ candidate ∈ candidates bound input cut active reference, candidate.term = term := by
  refine ⟨⟨term, accepted.1, accepted.2⟩, ?_, rfl⟩
  exact List.mem_filterMap.mpr ⟨term, List.mem_attach _ _, by simp [check, accepted]⟩

abbrev Choice (reference : Term bound input cut) :=
  Selected (axes bound input cut) (fun candidate : Candidate bound input cut active reference => benefitCost bound input cut active candidate.term)
    (candidates bound input cut active reference)

inductive Row where
  | economic (row : Cut.Row bound.source input cut)
  | native (table : Table bound input cut)

def rows : List (Row bound input cut) := (Cut.rows bound.source input cut).map .economic ++
  (Cut.tables bound.source input cut).map .native

def Holds (reference term : Term bound input cut) : Row bound input cut → Prop
  | .economic row => Cut.Holds bound.source input cut reference term row
  | .native table => native bound input cut active table term reference

instance (reference term : Term bound input cut) (row : Row bound input cut) :
    Decidable (Holds bound input cut active reference term row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (reference term : Term bound input cut) :
    (∀ row ∈ rows bound input cut, Holds bound input cut active reference term row) ↔ acceptable bound input cut active reference term := by
  constructor
  · intro all
    have economic : ∀ row ∈ Cut.rows bound.source input cut, Cut.Holds bound.source input cut reference term row :=
      fun row inside => all (.economic row) (by simp [rows, inside])
    obtain ⟨feasible, bounded⟩ := (Cut.rows_iff bound.source input cut reference term).mp economic
    exact ⟨feasible, (comparison_iff bound input cut active term reference).mpr
      ⟨bounded, fun table inside => all (.native table) (by simp [rows, inside])⟩⟩
  · rintro ⟨feasible, bounded⟩ row inside
    obtain ⟨economic, natives⟩ := (comparison_iff bound input cut active term reference).mp bounded
    cases row with
    | economic row => exact (Cut.rows_iff bound.source input cut reference term).mpr ⟨feasible, economic⟩ row (by simpa [rows] using inside)
    | native table => exact natives table (by simpa [rows] using inside)

structure Rejection (reference term : Term bound input cut) where
  row : Row bound input cut
  original : row ∈ rows bound input cut
  broken : ¬ Holds bound input cut active reference term row

inductive Outcome (reference : Term bound input cut) where
  | selected (choice : Choice bound input cut active reference)
  | blocked (rejected : ∀ term : Term bound input cut, Rejection bound input cut active reference term)

def compile (reference : Term bound input cut) : Outcome bound input cut active reference :=
  match result : choose (axes bound input cut)
    (fun candidate : Candidate bound input cut active reference => benefitCost bound input cut active candidate.term)
      (candidates bound input cut active reference) with
  | some choice => .selected choice
  | none => .blocked (fun term => match inspect (Holds bound input cut active reference term) (rows bound input cut) with
      | .rejected row original broken => ⟨row, original, broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate, member, _⟩ := every_accepted_term_is_generated bound input cut active reference term
            ((rows_iff bound input cut active reference term).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_feasible_dominator (reference : Term bound input cut) (choice : Choice bound input cut active reference)
    (other : Term bound input cut) (feasible : Cut.Feasible bound.source input cut other) :
    ¬ Better bound input cut active choice.policy.term other := by
  intro improves
  obtain ⟨candidate, member, same⟩ := every_accepted_term_is_generated bound input cut active reference other
    ⟨feasible, noWorse_trans improves.1 choice.policy.no_regression⟩
  have maximal := choice.maximal candidate member
  apply maximal
  change Improves (axes bound input cut) (benefitCost bound input cut active) choice.policy.term candidate.term
  rw [same]
  exact ⟨no_worse_bounds_the_benefit_vector bound input cut active _ _ improves.1, improves.2⟩

theorem every_available_improvement_is_realized (reference : Term bound input cut) (choice : Choice bound input cut active reference)
    (available : ∃ term : Term bound input cut, Cut.Feasible bound.source input cut term ∧ Better bound input cut active reference term) :
    Better bound input cut active reference choice.policy.term := by
  refine ⟨choice.policy.no_regression, ?_⟩
  intro reverse
  obtain ⟨term, feasible, improves⟩ := available
  obtain ⟨candidate, member, same⟩ := every_accepted_term_is_generated bound input cut active reference term ⟨feasible, improves.1⟩
  apply choice.maximal candidate member
  change Improves (axes bound input cut) (benefitCost bound input cut active) choice.policy.term candidate.term
  rw [same]
  exact ⟨noWorse_trans (no_worse_bounds_the_benefit_vector bound input cut active _ _ improves.1) reverse,
    fun backward => improves.2 (noWorse_trans reverse backward)⟩

theorem feasible_original_cannot_be_blocked (reference : Term bound input cut)
    (feasible : Cut.Feasible bound.source input cut reference)
    (rejected : ∀ term : Term bound input cut, Rejection bound input cut active reference term) : False :=
  (rejected reference).broken ((rows_iff bound input cut active reference reference).mpr
    ⟨feasible, fun _ _ => le_refl _⟩ (rejected reference).row (rejected reference).original)

/-- This verifier scans all terms independently of the compiler's candidate filter and scan order. -/
def verify (reference term : Term bound input cut) : Bool := decide (
  acceptable bound input cut active reference term ∧
    ∀ other ∈ Cut.terms bound.source input cut, acceptable bound input cut active reference other →
      ¬ Improves (axes bound input cut) (benefitCost bound input cut active) term other)

theorem verify_iff (reference term : Term bound input cut) : verify bound input cut active reference term = true ↔
    acceptable bound input cut active reference term ∧
      ∀ other : Term bound input cut, acceptable bound input cut active reference other →
        ¬ Improves (axes bound input cut) (benefitCost bound input cut active) term other := by
  unfold verify
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨accepted, maximal⟩
    exact ⟨accepted, fun other => maximal other (List.mem_attach _ _)⟩
  · rintro ⟨accepted, maximal⟩
    exact ⟨accepted, fun other _ => maximal other⟩

/-- Every planner may supply its own term; fresh verification constructs the same typed
    executable Choice contract without rerunning choose or assuming its answer. -/
def choiceOfVerified (reference term : Term bound input cut)
    (verified : verify bound input cut active reference term = true) : Choice bound input cut active reference := by
  let checked := (verify_iff bound input cut active reference term).mp verified
  let candidate : Candidate bound input cut active reference := ⟨term, checked.1.1, checked.1.2⟩
  refine ⟨candidate, ?_, ?_⟩
  · exact List.mem_filterMap.mpr ⟨term, List.mem_attach _ _, by simp [check, checked.1, candidate]⟩
  · intro other _
    exact checked.2 other.term ⟨other.feasible, other.no_regression⟩

theorem verified_choice_keeps_the_supplied_term (reference term : Term bound input cut)
    (verified : verify bound input cut active reference term = true) :
    (choiceOfVerified bound input cut active reference term verified).policy.term = term := rfl

theorem independent_replay_accepts_selection (reference : Term bound input cut) (choice : Choice bound input cut active reference) :
    verify bound input cut active reference choice.policy.term = true := by
  apply (verify_iff bound input cut active reference _).mpr
  refine ⟨⟨choice.policy.feasible, choice.policy.no_regression⟩, ?_⟩
  intro other accepted
  obtain ⟨candidate, member, same⟩ := every_accepted_term_is_generated bound input cut active reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes bound input cut) (benefitCost bound input cut active) choice.policy.term candidate.term at maximal
  simpa only [same] using maximal

theorem independently_verified_term_realizes_every_available_improvement (reference term : Term bound input cut)
    (verified : verify bound input cut active reference term = true)
    (available : ∃ other : Term bound input cut, Cut.Feasible bound.source input cut other ∧ Better bound input cut active reference other) :
    Better bound input cut active reference term :=
  every_available_improvement_is_realized bound input cut active reference
    (choiceOfVerified bound input cut active reference term verified) available

include empty in
theorem selected_is_nondominated_against_every_future_opponent
    (reference : Term bound input cut) (choice : Choice bound input cut active reference) :
    Cut.FeasibleAgainstEveryOpponent bound.source input cut choice.policy.term ∧
      AgainstEveryOpponent bound input cut active choice.policy.term reference ∧
      ∀ other : Term bound input cut, Cut.FeasibleAgainstEveryOpponent bound.source input cut other →
        ¬ (AgainstEveryOpponent bound input cut active other choice.policy.term ∧
          ¬ BenefitAgainstEveryOpponent bound input cut active choice.policy.term other) := by
  refine ⟨(Cut.feasibility_iff_every_future_opponent bound.source input cut active empty _).mp choice.policy.feasible,
    (comparison_iff_every_future_opponent bound input cut active empty _ _).mp choice.policy.no_regression, ?_⟩
  intro other feasible improves
  exact selected_has_no_feasible_dominator bound input cut active reference choice other
    ((Cut.feasibility_iff_every_future_opponent bound.source input cut active empty _).mpr feasible)
    ⟨(comparison_iff_every_future_opponent bound input cut active empty _ _).mpr improves.1,
      fun reverse => improves.2 ((benefit_iff_every_future_opponent bound input cut active empty _ _).mp reverse)⟩


include empty in
theorem every_future_improvement_is_realized (reference : Term bound input cut)
    (choice : Choice bound input cut active reference)
    (available : ∃ other : Term bound input cut, Cut.FeasibleAgainstEveryOpponent bound.source input cut other ∧
      AgainstEveryOpponent bound input cut active other reference ∧
        ¬ BenefitAgainstEveryOpponent bound input cut active reference other) :
    AgainstEveryOpponent bound input cut active choice.policy.term reference ∧
      ¬ BenefitAgainstEveryOpponent bound input cut active reference choice.policy.term := by
  have improves : Better bound input cut active reference choice.policy.term := by
    apply every_available_improvement_is_realized bound input cut active reference choice
    obtain ⟨other, feasible, bounded, strict⟩ := available
    exact ⟨other, (Cut.feasibility_iff_every_future_opponent bound.source input cut active empty other).mpr feasible,
      (comparison_iff_every_future_opponent bound input cut active empty _ _).mpr bounded,
      fun reverse => strict ((benefit_iff_every_future_opponent bound input cut active empty _ _).mp reverse)⟩
  exact ⟨(comparison_iff_every_future_opponent bound input cut active empty _ _).mp improves.1,
    fun reverse => improves.2 ((benefit_iff_every_future_opponent bound input cut active empty _ _).mpr reverse)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection
