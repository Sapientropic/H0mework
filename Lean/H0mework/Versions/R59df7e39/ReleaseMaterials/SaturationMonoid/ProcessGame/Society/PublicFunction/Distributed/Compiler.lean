import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Execution

/-! Robust Pareto synthesis from actual raw histories and asynchronous
deviations. The comparison vector contains every declared bearer/good and
claim address at every scenario. Assets and liabilities remain separate;
they are never netted against material expenditure. Native service/mandate
histories and unlimited future simulation are downstream consumers. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

inductive Responsibility (Party Good Instrument : Type) where
  | debit (bearer : Party) (good : Good)
  | credit (bearer : Party) (good : Good)
  | inventory (bearer : Party) (good : Good)
  | liability (instrument : Instrument) (debtor creditor : Party)
  | claim (instrument : Instrument) (debtor creditor : Party)
  | clock

namespace Code

variable (code : Code Party Good Port Technology Instrument)

abbrev Component (_code : Code Party Good Port Technology Instrument) := Responsibility Party Good Instrument
abbrev Coordinate := code.Scenario × code.Component

def components : List code.Component :=
  code.parties.flatMap (fun p => code.goods.flatMap (fun g => [.debit p g, .credit p g, .inventory p g])) ++
  code.instruments.flatMap (fun i => code.parties.flatMap (fun d => code.parties.flatMap
    (fun c => [.liability i d c, .claim i d c]))) ++ [.clock]

theorem every_responsibility_address_is_present (component : code.Component) :
    component ∈ code.components := by
  cases component <;> simp [components, code.parties_cover, code.goods_cover, code.instruments_cover]

def coordinates : List code.Coordinate := code.scenarios.product code.components

def cost (policy : code.Policy) (coordinate : code.Coordinate) : ℚ :=
  let current := code.historyCurrent coordinate.1.1
  let word := (code.executed policy coordinate.1).word
  match coordinate.2 with
  | .debit p g => code.law.totalDebit (code.law.rawItems current word) p g
  | .credit p g => - code.law.totalCredit (code.law.rawItems current word) p g
  | .inventory p g => - (code.law.next current word).stock p g
  | .liability i d c => (code.law.next current word).claims i d c
  | .claim i d c => - (code.law.next current word).claims i d c
  | .clock => (code.law.next current word).clock

abbrev NoWorseThan (new old : code.Policy) := NoWorse code.coordinates code.cost new old
abbrev StrictlyImproves (old new : code.Policy) := Improves code.coordinates code.cost old new

inductive Requirement where
  | localValidity (scenario : code.Scenario)
  | service (scenario : code.Scenario)
  | noRegression (coordinate : code.Coordinate)

def requirements : List code.Requirement :=
  code.scenarios.map .localValidity ++ code.scenarios.map .service ++ code.coordinates.map .noRegression

def Holds (reference policy : code.Policy) : code.Requirement → Prop
  | .localValidity scenario => (code.executed policy scenario).localLegal = true
  | .service scenario => ServiceAdequate code.law (code.historyCurrent scenario.1)
      code.task (code.executed policy scenario).word
  | .noRegression coordinate => code.cost policy coordinate ≤ code.cost reference coordinate

instance (reference policy : code.Policy) (row : code.Requirement) : Decidable (code.Holds reference policy row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem requirements_iff (reference policy : code.Policy) :
    (∀ row ∈ code.requirements, code.Holds reference policy row) ↔
      code.feasible policy ∧ code.NoWorseThan policy reference := by
  constructor
  · intro all
    constructor
    · intro scenario inside
      exact ⟨all (.localValidity scenario) (by simp [requirements, inside]),
        all (.service scenario) (by simp [requirements, inside])⟩
    · intro coordinate inside
      exact all (.noRegression coordinate) (by simp [requirements, inside])
  · rintro ⟨feasible, bounded⟩ row inside
    cases row with
    | localValidity scenario =>
      have h : scenario ∈ code.scenarios := by simpa [requirements] using inside
      exact (feasible scenario h).1
    | service scenario =>
      have h : scenario ∈ code.scenarios := by simpa [requirements] using inside
      exact (feasible scenario h).2
    | noRegression coordinate =>
      have h : coordinate ∈ code.coordinates := by simpa [requirements] using inside
      exact bounded coordinate h

structure Candidate (reference : code.Policy) where
  policy : code.Policy
  generated : policy ∈ code.policies
  feasible : code.feasible policy
  no_regression : code.NoWorseThan policy reference

def check (reference policy : code.Policy) (generated : policy ∈ code.policies) :
    Option (code.Candidate reference) :=
  if accepted : code.feasible policy ∧ code.NoWorseThan policy reference then
    some ⟨policy, generated, accepted.1, accepted.2⟩ else none

def candidates (reference : code.Policy) : List (code.Candidate reference) :=
  code.policies.attach.filterMap (fun policy => code.check reference policy.val policy.property)

theorem every_acceptable_policy_is_a_candidate (reference policy : code.Policy)
    (generated : policy ∈ code.policies)
    (accepted : code.feasible policy ∧ code.NoWorseThan policy reference) :
    ∃ candidate ∈ code.candidates reference, candidate.policy = policy := by
  refine ⟨⟨policy, generated, accepted.1, accepted.2⟩, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨⟨policy, generated⟩, List.mem_attach _ _, by simp [check, accepted]⟩

abbrev Selection (reference : code.Policy) :=
  Selected code.coordinates (fun candidate : code.Candidate reference => code.cost candidate.policy)
    (code.candidates reference)

structure Rejection (reference policy : code.Policy) where
  row : code.Requirement
  original : row ∈ code.requirements
  broken : ¬ code.Holds reference policy row

inductive Outcome (reference : code.Policy) where
  | selected (choice : code.Selection reference)
  | blocked (rejected : ∀ policy, policy ∈ code.policies → code.Rejection reference policy)

def compile (reference : code.Policy) : code.Outcome reference :=
  match result : choose code.coordinates (fun candidate : code.Candidate reference => code.cost candidate.policy)
      (code.candidates reference) with
  | some choice => .selected choice
  | none => .blocked (fun policy generated =>
      match inspected : inspect (code.Holds reference policy) code.requirements with
      | .rejected row original broken => ⟨row, original, broken⟩
      | .accepted all => False.elim (by
          have empty := (choose_none_iff_empty _ _ _).mp result
          obtain ⟨candidate, member, _⟩ := code.every_acceptable_policy_is_a_candidate reference policy
            generated ((code.requirements_iff reference policy).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_feasible_improvement (reference : code.Policy)
    (choice : code.Selection reference) (other : code.Policy)
    (generated : other ∈ code.policies) (feasible : code.feasible other) :
    ¬ code.StrictlyImproves choice.policy.policy other := by
  intro improves
  have below : code.NoWorseThan other reference := noWorse_trans improves.1 choice.policy.no_regression
  obtain ⟨candidate, member, same⟩ := code.every_acceptable_policy_is_a_candidate reference other
    generated ⟨feasible, below⟩
  apply choice.maximal candidate member
  change Improves code.coordinates code.cost choice.policy.policy candidate.policy
  rw [same]
  exact improves

theorem any_available_strict_improvement_is_realized (reference : code.Policy)
    (choice : code.Selection reference)
    (available : ∃ policy ∈ code.policies, code.feasible policy ∧ code.StrictlyImproves reference policy) :
    code.StrictlyImproves reference choice.policy.policy := by
  refine ⟨choice.policy.no_regression, ?_⟩
  intro reverse
  obtain ⟨policy, generated, feasible, improves⟩ := available
  apply code.selected_has_no_feasible_improvement reference choice policy generated feasible
  exact ⟨noWorse_trans improves.1 reverse, fun backward =>
    improves.2 (noWorse_trans reverse backward)⟩

theorem feasible_reference_cannot_be_blocked (reference : code.Policy)
    (generated : reference ∈ code.policies) (feasible : code.feasible reference)
    (rejected : ∀ policy, policy ∈ code.policies → code.Rejection reference policy) : False := by
  let refusal := rejected reference generated
  apply refusal.broken
  apply (code.requirements_iff reference reference).mpr
  exact ⟨feasible, fun _ _ => le_refl _⟩
  exact refusal.original

/-- Every verifier may replay these rows independently. Its name does not
contribute to acceptance and changing the enumeration cannot validate a bad
candidate or a dominated policy. -/
def verify (reference policy : code.Policy) : Bool :=
  decide (code.feasible policy ∧ code.NoWorseThan policy reference ∧
    ∀ other ∈ code.policies, code.feasible other → ¬ code.StrictlyImproves policy other)

theorem verify_iff (reference policy : code.Policy) : code.verify reference policy = true ↔
    code.feasible policy ∧ code.NoWorseThan policy reference ∧
      ∀ other ∈ code.policies, code.feasible other → ¬ code.StrictlyImproves policy other := by
  simp [verify]

theorem selection_passes_independent_replay (reference : code.Policy) (choice : code.Selection reference) :
    code.verify reference choice.policy.policy = true := by
  apply (code.verify_iff _ _).mpr
  exact ⟨choice.policy.feasible, choice.policy.no_regression,
    code.selected_has_no_feasible_improvement reference choice⟩

end Code
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed
