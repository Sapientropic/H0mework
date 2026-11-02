import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Comparison

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

inductive Row where
  | localValidity (scenario : code.Scenario)
  | service (scenario : code.Scenario)
  | regression (axis : Axis code)

def rows : List (Row code) :=
  code.scenarios.map .localValidity ++ code.scenarios.map .service ++ (axes code).map .regression

def Holds (reference policy : code.Policy) : Row code → Prop
  | .localValidity scenario => (code.executed policy scenario).localLegal = true
  | .service scenario => ServiceAdequate code.law (code.historyCurrent scenario.1)
      code.task (code.executed policy scenario).word
  | .regression axis => cost code policy axis ≤ cost code reference axis

instance (reference policy : code.Policy) (row : Row code) : Decidable (Holds code reference policy row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (reference policy : code.Policy) :
    (∀ row ∈ rows code, Holds code reference policy row) ↔
      code.feasible policy ∧ NonRegression code policy reference := by
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

structure Candidate (reference : code.Policy) where
  policy : code.Policy
  generated : policy ∈ code.policies
  feasible : code.feasible policy
  no_regression : NonRegression code policy reference

def check (reference policy : code.Policy) (generated : policy ∈ code.policies) : Option (Candidate code reference) :=
  if accepted : code.feasible policy ∧ NonRegression code policy reference then
    some ⟨policy, generated, accepted.1, accepted.2⟩ else none

def candidates (reference : code.Policy) : List (Candidate code reference) :=
  code.policies.attach.filterMap (fun policy => check code reference policy.val policy.property)

theorem every_accepted_program_is_generated (reference policy : code.Policy)
    (generated : policy ∈ code.policies)
    (accepted : code.feasible policy ∧ NonRegression code policy reference) :
    ∃ candidate ∈ candidates code reference, candidate.policy = policy := by
  refine ⟨⟨policy, generated, accepted.1, accepted.2⟩, ?_, rfl⟩
  exact List.mem_filterMap.mpr ⟨⟨policy, generated⟩, List.mem_attach _ _, by simp [check, accepted]⟩

abbrev Selection (reference : code.Policy) :=
  Selected (axes code) (fun candidate : Candidate code reference => cost code candidate.policy)
    (candidates code reference)

structure Rejection (reference policy : code.Policy) where
  row : Row code
  original : row ∈ rows code
  broken : ¬ Holds code reference policy row

inductive Outcome (reference : code.Policy) where
  | selected (choice : Selection code reference)
  | blocked (rejected : ∀ policy, policy ∈ code.policies → Rejection code reference policy)

def compile (reference : code.Policy) (_referenceGenerated : reference ∈ code.policies) : Outcome code reference :=
  match result : choose (axes code) (fun candidate : Candidate code reference => cost code candidate.policy)
      (candidates code reference) with
  | some choice => .selected choice
  | none => .blocked (fun policy generated =>
      match inspect (Holds code reference policy) (rows code) with
      | .rejected row original broken => ⟨row, original, broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate, member, _⟩ := every_accepted_program_is_generated code reference policy
            generated ((rows_iff code reference policy).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_feasible_dominator (reference : code.Policy) (choice : Selection code reference)
    (other : code.Policy) (generated : other ∈ code.policies) (feasible : code.feasible other) :
    ¬ Better code choice.policy.policy other := by
  intro improves
  obtain ⟨candidate, member, same⟩ := every_accepted_program_is_generated code reference other generated
    ⟨feasible, noWorse_trans improves.1 choice.policy.no_regression⟩
  apply choice.maximal candidate member
  change Improves (axes code) (cost code) choice.policy.policy candidate.policy
  rw [same]
  exact improves

theorem every_available_improvement_is_realized (reference : code.Policy) (choice : Selection code reference)
    (available : ∃ policy ∈ code.policies, code.feasible policy ∧ Better code reference policy) :
    Better code reference choice.policy.policy := by
  refine ⟨choice.policy.no_regression, ?_⟩
  intro reverse
  obtain ⟨policy, generated, feasible, improves⟩ := available
  exact selected_has_no_feasible_dominator code reference choice policy generated feasible
    ⟨noWorse_trans improves.1 reverse, fun backward => improves.2 (noWorse_trans reverse backward)⟩

theorem feasible_original_cannot_be_blocked (reference : code.Policy)
    (generated : reference ∈ code.policies) (feasible : code.feasible reference)
    (rejected : ∀ policy, policy ∈ code.policies → Rejection code reference policy) : False := by
  let failure := rejected reference generated
  exact failure.broken ((rows_iff code reference reference).mpr
    ⟨feasible, fun _ _ => le_refl _⟩ failure.row failure.original)

def verify (reference policy : code.Policy) : Bool :=
  decide (code.feasible policy ∧ NonRegression code policy reference ∧
    ∀ other ∈ code.policies, code.feasible other → ¬ Better code policy other)

theorem verify_iff (reference policy : code.Policy) : verify code reference policy = true ↔
    code.feasible policy ∧ NonRegression code policy reference ∧
      ∀ other ∈ code.policies, code.feasible other → ¬ Better code policy other := by simp [verify]

theorem independent_replay_accepts_selection (reference : code.Policy) (choice : Selection code reference) :
    verify code reference choice.policy.policy = true := by
  exact (verify_iff code _ _).mpr ⟨choice.policy.feasible, choice.policy.no_regression,
    selected_has_no_feasible_dominator code reference choice⟩

theorem selected_is_nondominated_against_every_same_opponent (reference : code.Policy)
    (choice : Selection code reference) (other : code.Policy) (generated : other ∈ code.policies)
    (feasible : code.feasible other) : ¬ StrictAgainstEveryOpponent code choice.policy.policy other := by
  intro improves
  exact selected_has_no_feasible_dominator code reference choice other generated feasible
    ((finite_strictness_iff_every_same_opponent code _ _ choice.policy.generated generated).mpr improves)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open
