import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Comparison

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)

def LocalValidity (term : Term source input cut) (table : Table source input cut) : Prop :=
  (Residual.run source.code (Residual.scheduleAt source cut term.val)
    ⟨opponent source input cut table, input.budget⟩ (Residual.seed source input cut)
    (horizon source input cut)).frame.localLegal = true

def Service (term : Term source input cut) (table : Table source input cut)
    (index : Fin source.code.task.slots.length) : Prop :=
  (Identity.firstService (machine source input cut (opponent source input cut table) term)
    (finish source input cut - 1) index).isSome = true

def Feasible (term : Term source input cut) : Prop :=
  ∀ table ∈ tables source input cut, LocalValidity source input cut term table ∧
    ∀ index, Service source input cut term table index

instance (term : Term source input cut) : Decidable (Feasible source input cut term) := by
  unfold Feasible LocalValidity Service
  infer_instance

inductive Row where
  | validity (table : Table source input cut)
  | service (table : Table source input cut) (index : Fin source.code.task.slots.length)
  | regression (axis : Axis source input cut)

def rows : List (Row source input cut) := (tables source input cut).map .validity ++
  (tables source input cut).flatMap (fun table => (List.finRange source.code.task.slots.length).map (.service table)) ++
  (axes source input cut).map .regression

def Holds (reference term : Term source input cut) : Row source input cut → Prop
  | .validity table => LocalValidity source input cut term table
  | .service table index => Service source input cut term table index
  | .regression axis => cost source input cut term axis ≤ cost source input cut reference axis

instance (reference term : Term source input cut) (row : Row source input cut) : Decidable (Holds source input cut reference term row) := by
  cases row <;> unfold Holds LocalValidity Service <;> infer_instance

theorem rows_iff (reference term : Term source input cut) :
    (∀ row ∈ rows source input cut, Holds source input cut reference term row) ↔
      Feasible source input cut term ∧ NonRegression source input cut term reference := by
  constructor
  · intro all
    refine ⟨?_, fun axis inside => all (.regression axis) (by simp [rows, inside])⟩
    intro table generated
    exact ⟨all (.validity table) (by simp [rows, generated]),
      fun index => all (.service table index) (by simp [rows, generated])⟩
  · rintro ⟨feasible, bounded⟩ row inside
    cases row with
    | validity table => exact (feasible table (by simpa [rows] using inside)).1
    | service table index =>
      have generated : table ∈ tables source input cut := by simpa [rows] using inside
      exact (feasible table generated).2 index
    | regression axis => exact bounded axis (by simpa [rows] using inside)

structure Candidate (reference : Term source input cut) where
  term : Term source input cut
  feasible : Feasible source input cut term
  no_regression : NonRegression source input cut term reference

def acceptable (reference term : Term source input cut) : Prop :=
  Feasible source input cut term ∧ ValuesNoWorse source input cut term reference ∧
    ∀ table ∈ tables source input cut,
      profile source input cut (opponent source input cut table) term = profile source input cut (opponent source input cut table) reference

instance (reference term : Term source input cut) : Decidable (acceptable source input cut reference term) := by
  unfold acceptable
  infer_instance

theorem acceptable_iff (reference term : Term source input cut) :
    acceptable source input cut reference term ↔ Feasible source input cut term ∧ NonRegression source input cut term reference := by
  unfold acceptable
  rw [comparison_iff]

def check (reference term : Term source input cut) : Option (Candidate source input cut reference) :=
  if accepted : acceptable source input cut reference term then
    let checked := (acceptable_iff source input cut reference term).mp accepted
    some ⟨term, checked.1, checked.2⟩ else none

def candidates (reference : Term source input cut) := (terms source input cut).filterMap (check source input cut reference)

theorem every_accepted_term_is_generated (reference term : Term source input cut)
    (accepted : Feasible source input cut term ∧ NonRegression source input cut term reference) :
    ∃ candidate ∈ candidates source input cut reference, candidate.term = term := by
  refine ⟨⟨term, accepted.1, accepted.2⟩, ?_, rfl⟩
  exact List.mem_filterMap.mpr ⟨term, List.mem_attach _ _, by simp [check, (acceptable_iff source input cut reference term).mpr accepted]⟩

abbrev Selection (reference : Term source input cut) :=
  Selected (valueAxes source input cut) (fun candidate : Candidate source input cut reference => value source input cut candidate.term)
    (candidates source input cut reference)

structure Rejection (reference term : Term source input cut) where
  row : Row source input cut
  original : row ∈ rows source input cut
  broken : ¬ Holds source input cut reference term row

inductive Outcome (reference : Term source input cut) where
  | selected (choice : Selection source input cut reference)
  | blocked (rejected : ∀ term : Term source input cut, Rejection source input cut reference term)

def compile (reference : Term source input cut) : Outcome source input cut reference :=
  match result : choose (valueAxes source input cut)
    (fun candidate : Candidate source input cut reference => value source input cut candidate.term) (candidates source input cut reference) with
  | some choice => .selected choice
  | none => .blocked (fun term => match inspect (Holds source input cut reference term) (rows source input cut) with
      | .rejected row original broken => ⟨row, original, broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate, member, _⟩ := every_accepted_term_is_generated source input cut reference term
            ((rows_iff source input cut reference term).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_feasible_dominator (reference : Term source input cut) (choice : Selection source input cut reference)
    (other : Term source input cut) (feasible : Feasible source input cut other) : ¬ Better source input cut choice.policy.term other := by
  intro improves
  obtain ⟨candidate, member, same⟩ := every_accepted_term_is_generated source input cut reference other
    ⟨feasible, noWorse_trans improves.1 choice.policy.no_regression⟩
  apply choice.maximal candidate member
  change Improves (valueAxes source input cut) (value source input cut) choice.policy.term candidate.term
  rw [same]
  exact ((strictness_comes_from_actual_values source input cut _ _).mp improves).1

theorem every_available_improvement_is_realized (reference : Term source input cut) (choice : Selection source input cut reference)
    (available : ∃ term : Term source input cut, Feasible source input cut term ∧ Better source input cut reference term) :
    Better source input cut reference choice.policy.term := by
  refine ⟨choice.policy.no_regression, ?_⟩
  intro reverse
  obtain ⟨term, feasible, improves⟩ := available
  exact selected_has_no_feasible_dominator source input cut reference choice term feasible
    ⟨noWorse_trans improves.1 reverse, fun backward => improves.2 (noWorse_trans reverse backward)⟩

theorem feasible_original_cannot_be_blocked (reference : Term source input cut) (feasible : Feasible source input cut reference)
    (rejected : ∀ term : Term source input cut, Rejection source input cut reference term) : False :=
  (rejected reference).broken ((rows_iff source input cut reference reference).mpr ⟨feasible, fun _ _ => le_refl _⟩
    (rejected reference).row (rejected reference).original)

def verify (reference term : Term source input cut) : Bool := decide (acceptable source input cut reference term ∧
  ∀ other ∈ terms source input cut, acceptable source input cut reference other →
    ¬ Improves (valueAxes source input cut) (value source input cut) term other)

theorem verify_iff (reference term : Term source input cut) : verify source input cut reference term = true ↔
    Feasible source input cut term ∧ NonRegression source input cut term reference ∧
      ∀ other : Term source input cut, Feasible source input cut other → ¬ Better source input cut term other := by
  simp only [verify, decide_eq_true_eq]
  constructor
  · rintro ⟨accepted, maximal⟩
    have own := (acceptable_iff source input cut reference term).mp accepted
    refine ⟨own.1, own.2, ?_⟩
    intro other feasible improves
    have otherAccepted := (acceptable_iff source input cut reference other).mpr ⟨feasible, noWorse_trans improves.1 own.2⟩
    exact maximal other (List.mem_attach _ _) otherAccepted
      (((strictness_comes_from_actual_values source input cut term other).mp improves).1)
  · rintro ⟨feasible, bounded, maximal⟩
    refine ⟨(acceptable_iff source input cut reference term).mpr ⟨feasible, bounded⟩, ?_⟩
    intro other _ otherAccepted improves
    obtain ⟨otherFeasible, otherBounded⟩ := (acceptable_iff source input cut reference other).mp otherAccepted
    have ownNative := ((comparison_iff source input cut term reference).mp bounded).2
    have otherNative := ((comparison_iff source input cut other reference).mp otherBounded).2
    exact maximal other otherFeasible ((strictness_comes_from_actual_values source input cut term other).mpr
      ⟨improves, fun table generated => (otherNative table generated).trans (ownNative table generated).symm⟩)

theorem independent_replay_accepts_selection (reference : Term source input cut) (choice : Selection source input cut reference) :
    verify source input cut reference choice.policy.term = true := by
  simp only [verify, decide_eq_true_eq]
  refine ⟨(acceptable_iff source input cut reference _).mpr ⟨choice.policy.feasible, choice.policy.no_regression⟩, ?_⟩
  intro other _ accepted
  obtain ⟨candidate, member, same⟩ := every_accepted_term_is_generated source input cut reference other
    ((acceptable_iff source input cut reference other).mp accepted)
  have maximal := choice.maximal candidate member
  change ¬ Improves (valueAxes source input cut) (value source input cut) choice.policy.term candidate.term at maximal
  simpa only [same] using maximal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut
