import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Comparison

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

inductive Row where
  | localValidity (scenario : code.Scenario)
  | service (scenario : code.Scenario)
  | regression (axis : Axis code)

def rows : List (Row code) := code.scenarios.map .localValidity ++ code.scenarios.map .service ++ (axes code).map .regression

def Holds (reference policy : Program code) : Row code → Prop
  | .localValidity scenario => (code.executed policy.val scenario).localLegal = true
  | .service scenario => ServiceAdequate code.law (code.historyCurrent scenario.1) code.task (code.executed policy.val scenario).word
  | .regression axis => cost code policy axis ≤ cost code reference axis

instance (reference policy : Program code) (row : Row code) : Decidable (Holds code reference policy row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (reference policy : Program code) :
    (∀ row ∈ rows code, Holds code reference policy row) ↔ code.feasible policy.val ∧ NonRegression code policy reference := by
  constructor
  · intro all
    exact ⟨fun scenario inside => ⟨all (.localValidity scenario) (by simp [rows, inside]),
      all (.service scenario) (by simp [rows, inside])⟩,
      fun axis inside => all (.regression axis) (by simp [rows, inside])⟩
  · rintro ⟨feasible, bounded⟩ row inside
    cases row with
    | localValidity scenario => exact (feasible scenario (by simpa [rows] using inside)).1
    | service scenario => exact (feasible scenario (by simpa [rows] using inside)).2
    | regression axis => exact bounded axis (by simpa [rows] using inside)

structure Candidate (reference : Program code) where
  policy : Program code
  feasible : code.feasible policy.val
  no_regression : NonRegression code policy reference

def acceptable (reference policy : Program code) : Prop :=
  code.feasible policy.val ∧ ValuesNoWorse code policy reference ∧
    ∀ history ∈ code.histories.attach, ∀ table ∈ tables code,
      profile code policy history table = profile code reference history table

instance (reference policy : Program code) : Decidable (acceptable code reference policy) := by
  unfold acceptable
  infer_instance

theorem acceptable_iff (reference policy : Program code) : acceptable code reference policy ↔
    code.feasible policy.val ∧ NonRegression code policy reference := by
  unfold acceptable
  rw [comparison_iff]
  constructor
  · rintro ⟨feasible, original, native⟩
    exact ⟨feasible, original, fun history table generated => native history (List.mem_attach _ _) table generated⟩
  · rintro ⟨feasible, original, native⟩
    exact ⟨feasible, original, fun history _ table generated => native history table generated⟩

/-- Original admissions, newborn debts and realized rights are checked once
per history/table; the Pareto scan uses only actual material and unpaid coordinates. -/
def check (reference policy : Program code) : Option (Candidate code reference) :=
  if accepted : acceptable code reference policy then
    let checked := (acceptable_iff code reference policy).mp accepted
    some ⟨policy, checked.1, checked.2⟩ else none

def candidates (reference : Program code) : List (Candidate code reference) := code.policies.attach.filterMap (check code reference)

theorem every_accepted_program_is_generated (reference policy : Program code)
    (accepted : code.feasible policy.val ∧ NonRegression code policy reference) :
    ∃ candidate ∈ candidates code reference, candidate.policy = policy := by
  refine ⟨⟨policy, accepted.1, accepted.2⟩, ?_, rfl⟩
  exact List.mem_filterMap.mpr ⟨policy, List.mem_attach _ _, by simp [check, (acceptable_iff code reference policy).mpr accepted]⟩

abbrev Selection (reference : Program code) :=
  Selected (valueAxes code) (fun candidate : Candidate code reference => value code candidate.policy) (candidates code reference)

structure Rejection (reference policy : Program code) where
  row : Row code
  original : row ∈ rows code
  broken : ¬ Holds code reference policy row

inductive Outcome (reference : Program code) where
  | selected (choice : Selection code reference)
  | blocked (rejected : ∀ policy : Program code, Rejection code reference policy)

def compile (reference : Program code) : Outcome code reference :=
  match result : choose (valueAxes code) (fun candidate : Candidate code reference => value code candidate.policy) (candidates code reference) with
  | some choice => .selected choice
  | none => .blocked (fun policy => match inspect (Holds code reference policy) (rows code) with
      | .rejected row original broken => ⟨row, original, broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate, member, _⟩ := every_accepted_program_is_generated code reference policy ((rows_iff code reference policy).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_feasible_dominator (reference : Program code) (choice : Selection code reference)
    (other : Program code) (feasible : code.feasible other.val) : ¬ Better code choice.policy.policy other := by
  intro improves
  obtain ⟨candidate, member, same⟩ := every_accepted_program_is_generated code reference other
    ⟨feasible, noWorse_trans improves.1 choice.policy.no_regression⟩
  apply choice.maximal candidate member
  change Improves (valueAxes code) (value code) choice.policy.policy candidate.policy
  rw [same]
  exact ((strictness_comes_from_actual_values code _ _).mp improves).1

theorem every_available_improvement_is_realized (reference : Program code) (choice : Selection code reference)
    (available : ∃ policy : Program code, code.feasible policy.val ∧ Better code reference policy) :
    Better code reference choice.policy.policy := by
  refine ⟨choice.policy.no_regression, ?_⟩
  intro reverse
  obtain ⟨policy, feasible, improves⟩ := available
  exact selected_has_no_feasible_dominator code reference choice policy feasible
    ⟨noWorse_trans improves.1 reverse, fun backward => improves.2 (noWorse_trans reverse backward)⟩

theorem feasible_original_cannot_be_blocked (reference : Program code) (feasible : code.feasible reference.val)
    (rejected : ∀ policy : Program code, Rejection code reference policy) : False :=
  (rejected reference).broken ((rows_iff code reference reference).mpr ⟨feasible, fun _ _ => le_refl _⟩
    (rejected reference).row (rejected reference).original)

def verify (reference policy : Program code) : Bool := decide (acceptable code reference policy ∧
  ∀ other ∈ code.policies.attach, acceptable code reference other → ¬ Improves (valueAxes code) (value code) policy other)

theorem verify_iff (reference policy : Program code) : verify code reference policy = true ↔
    code.feasible policy.val ∧ NonRegression code policy reference ∧
      ∀ other : Program code, code.feasible other.val → ¬ Better code policy other := by
  simp only [verify, decide_eq_true_eq]
  constructor
  · rintro ⟨accepted, maximal⟩
    have own := (acceptable_iff code reference policy).mp accepted
    refine ⟨own.1, own.2, ?_⟩
    intro other feasible improves
    have otherAccepted := (acceptable_iff code reference other).mpr
      ⟨feasible, noWorse_trans improves.1 own.2⟩
    exact maximal other (List.mem_attach _ _) otherAccepted
      (((strictness_comes_from_actual_values code policy other).mp improves).1)
  · rintro ⟨feasible, bounded, maximal⟩
    refine ⟨(acceptable_iff code reference policy).mpr ⟨feasible, bounded⟩, ?_⟩
    intro other _ otherAccepted improves
    obtain ⟨otherFeasible, otherBounded⟩ := (acceptable_iff code reference other).mp otherAccepted
    have ownNative := ((comparison_iff code policy reference).mp bounded).2
    have otherNative := ((comparison_iff code other reference).mp otherBounded).2
    exact maximal other otherFeasible ((strictness_comes_from_actual_values code policy other).mpr
      ⟨improves, fun history table generated =>
        (otherNative history table generated).trans (ownNative history table generated).symm⟩)

theorem independent_replay_accepts_selection (reference : Program code) (choice : Selection code reference) :
    verify code reference choice.policy.policy = true := by
  simp only [verify, decide_eq_true_eq]
  refine ⟨(acceptable_iff code reference _).mpr ⟨choice.policy.feasible, choice.policy.no_regression⟩, ?_⟩
  intro other _ accepted
  obtain ⟨candidate, member, same⟩ := every_accepted_program_is_generated code reference other
    ((acceptable_iff code reference other).mp accepted)
  have maximal := choice.maximal candidate member
  change ¬ Improves (valueAxes code) (value code) choice.policy.policy candidate.policy at maximal
  simpa only [same] using maximal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement
