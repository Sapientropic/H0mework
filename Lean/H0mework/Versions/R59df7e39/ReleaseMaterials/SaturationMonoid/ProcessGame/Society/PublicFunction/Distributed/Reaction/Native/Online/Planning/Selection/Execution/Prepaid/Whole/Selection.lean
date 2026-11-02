import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Source
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Decision
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {baseReference : Term cursor} {actor : Party} {position : Nat}
  (scope : Scope cursor pricing n baseReference actor position) (span : Nat)

def NoWorse (new previous : Intent scope) : Prop :=
  Deployable scope new ∧ ∀ table ∈ tables scope, accepts cursor (tensor scope span new (opponent scope table))
    (tensor scope span previous (opponent scope table))
instance (new previous : Intent scope) : Decidable (NoWorse scope span new previous) := by
  unfold NoWorse;infer_instance

def Benefit (new previous : Intent scope) : Prop :=
  ∀ table ∈ tables scope, benefit cursor (tensor scope span new (opponent scope table))
    (tensor scope span previous (opponent scope table))
instance (new previous : Intent scope) : Decidable (Benefit scope span new previous) := by
  unfold Benefit;infer_instance

theorem noWorse_trans {first middle last : Intent scope}
    (left : NoWorse scope span first middle) (right : NoWorse scope span middle last) :
    NoWorse scope span first last := ⟨left.1,fun table inside =>
  accepts_trans cursor (left.2 table inside) (right.2 table inside)⟩
theorem no_worse_bounds_real_benefit {new previous : Intent scope}
    (accepted : NoWorse scope span new previous) : Benefit scope span new previous :=
  fun table inside => acceptance_bounds_every_real_benefit cursor (accepted.2 table inside)

abbrev Axis := Table scope × Intent scope
def axes : List (Axis scope) := (tables scope).flatMap fun table => (intents scope).map (table,·)
/-- Finite order embedding of the real-benefit preorder; archive admission is absent from its tests. -/
def cost (term : Intent scope) (axis : Axis scope) : ℚ :=
  if benefit cursor (tensor scope span term (opponent scope axis.1))
    (tensor scope span axis.2 (opponent scope axis.1)) then 0 else 1

theorem vector_iff (new previous : Intent scope) :
    Distributed.NoWorse (axes scope) (cost scope span) new previous ↔ Benefit scope span new previous := by
  constructor
  · intro vector table inside
    have tested := vector (table,previous) (List.mem_flatMap.mpr ⟨table,inside,
      List.mem_map.mpr ⟨previous,every_intent_is_generated scope _,rfl⟩⟩)
    have self := benefit_refl cursor (tensor scope span previous (opponent scope table))
    by_contra failed
    simp only [cost,if_pos self,if_neg failed] at tested
    norm_num at tested
  · intro all axis inside
    obtain ⟨table,generated,mapped⟩ := List.mem_flatMap.mp inside
    obtain ⟨probe,_,same⟩ := List.mem_map.mp mapped
    cases same
    by_cases old : benefit cursor (tensor scope span previous (opponent scope table))
        (tensor scope span probe (opponent scope table))
    · have current := benefit_trans cursor (all table generated) old
      simp only [cost,if_pos old,if_pos current,le_refl]
    · simp only [cost,if_neg old]
      split <;> norm_num

def Better (previous new : Intent scope) : Prop :=
  NoWorse scope span new previous ∧ ¬ Benefit scope span previous new

structure Candidate (reference : Intent scope) where
  term : Intent scope
  no_regression : NoWorse scope span term reference

def check (reference term : Intent scope) : Option (Candidate scope span reference) :=
  if valid : NoWorse scope span term reference then some ⟨term,valid⟩ else none

def candidates (reference : Intent scope) := (intents scope).filterMap (check scope span reference)

theorem every_accepted_term_is_generated (reference term : Intent scope)
    (valid : NoWorse scope span term reference) :
    ∃ candidate ∈ candidates scope span reference, candidate.term = term := by
  exact ⟨⟨term,valid⟩,List.mem_filterMap.mpr ⟨term,every_intent_is_generated scope _,by simp [check,valid]⟩,rfl⟩

abbrev Choice (reference : Intent scope) :=
  Selected (axes scope) (fun candidate : Candidate scope span reference => cost scope span candidate.term)
    (candidates scope span reference)

def strictBenefit (previous new : Intent scope) : Prop :=
  Benefit scope span new previous ∧ ¬ Benefit scope span previous new
instance (previous new : Intent scope) : Decidable (strictBenefit scope span previous new) := by
  unfold strictBenefit;infer_instance

theorem strictBenefit_iff (previous new : Intent scope) : strictBenefit scope span previous new ↔
    Improves (axes scope) (cost scope span) previous new := by
  simp only [strictBenefit,Improves,vector_iff]

def fastChoose (reference : Intent scope) (pool : List (Candidate scope span reference)) :
    Option (Selected (axes scope)
      (fun candidate : Candidate scope span reference => cost scope span candidate.term) pool) :=
  Distributed.choose (axes scope) (fun candidate => cost scope span candidate.term) pool

theorem fastChoose_none_iff_empty (reference : Intent scope) (pool : List (Candidate scope span reference)) :
    fastChoose scope span reference pool = none ↔ pool = [] :=
  Distributed.choose_none_iff_empty _ _ _

inductive Row where
  | deployment
  | present (table : Table scope)
  | future (table : Table scope) (word : List (Future.Recovery.Action cursor.model))
  | funding (table : Table scope) (word : List (Future.Recovery.Action cursor.model))

def economicRows : List (Row scope) := (tables scope).flatMap fun table =>
  [.present table] ++ (Future.Recovery.capabilities cursor.model cursor.depth).map (.future table) ++
    (Future.Recovery.capabilities cursor.model cursor.depth).map (.funding table)

def rows : List (Row scope) := (if scope.ownFamily then [.deployment] else []) ++ economicRows scope

def Holds (reference term : Intent scope) : Row scope → Prop
  | .deployment => Deployable scope term
  | .present table => Synthesis.accepts cursor.source.val.code (Window.axes cursor.model cursor.depth)
      (tensor scope span term (opponent scope table)).present
      (tensor scope span reference (opponent scope table)).present
  | .future table word => futureNoWorse cursor
      ((tensor scope span term (opponent scope table)).future cursor word)
      ((tensor scope span reference (opponent scope table)).future cursor word)
  | .funding table word =>
      ((tensor scope span reference (opponent scope table)).funding cursor word).isNone = true →
      ((tensor scope span term (opponent scope table)).funding cursor word).isNone = true
instance (reference term : Intent scope) (row : Row scope) : Decidable (Holds scope span reference term row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (reference term : Intent scope) :
    (∀ row ∈ rows scope, Holds scope span reference term row) ↔ NoWorse scope span term reference := by
  constructor
  · intro all
    refine ⟨?_,fun table inside => ⟨?_,?_,?_⟩⟩
    · cases mode : scope.ownFamily with
      | false => cases term <;> simp [Deployable,mode]
      | true => exact all .deployment (by simp [rows,mode])
    · exact all (.present table) (by simp [rows,economicRows,inside])
    · intro word member;exact all (.future table word) (by simp [rows,economicRows,inside,member])
    · intro word member;exact all (.funding table word) (by simp [rows,economicRows,inside,member])
  · rintro ⟨deployable,all⟩ row inside
    rcases List.mem_append.mp inside with gate | economic
    · have same : row = .deployment := by
        cases mode : scope.ownFamily <;> simp_all [rows]
      subst row;exact deployable
    · obtain ⟨table,member,generated⟩ := List.mem_flatMap.mp economic
      have valid := all table member
      simp only [List.mem_append,List.mem_singleton,List.mem_map] at generated
      rcases generated with (same | ⟨word,registered,same⟩) | ⟨word,registered,same⟩
      · subst row;exact valid.1
      · subst row;exact valid.2.1 word registered
      · subst row;exact valid.2.2 word registered

structure Rejection (reference term : Intent scope) where
  row : Row scope
  original : row ∈ rows scope
  broken : ¬ Holds scope span reference term row
inductive Outcome (reference : Intent scope) where
  | selected (choice : Choice scope span reference)
  | blocked (rejected : ∀ term : Intent scope, Rejection scope span reference term)

def compile (reference : Intent scope) : Outcome scope span reference :=
  match result : fastChoose scope span reference (candidates scope span reference) with
  | some choice => .selected choice
  | none => .blocked (fun term => match inspect (Holds scope span reference term) (rows scope) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
          have empty := (fastChoose_none_iff_empty scope span reference _).mp result
          obtain ⟨candidate,member,_⟩ := every_accepted_term_is_generated scope span reference term
            ((rows_iff scope span reference term).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_full_responsibility_dominator (reference : Intent scope)
    (choice : Choice scope span reference) (other : Intent scope) :
    ¬ Better scope span choice.policy.term other := by
  intro improves
  obtain ⟨candidate,member,same⟩ := every_accepted_term_is_generated scope span reference other
    (noWorse_trans scope span improves.1 choice.policy.no_regression)
  apply choice.maximal candidate member
  change Improves (axes scope) (cost scope span) choice.policy.term candidate.term
  rw [same]
  exact ⟨(vector_iff scope span _ _).mpr (no_worse_bounds_real_benefit scope span improves.1),
    fun reverse => improves.2 ((vector_iff scope span _ _).mp reverse)⟩

theorem every_available_real_improvement_is_realized (reference : Intent scope)
    (choice : Choice scope span reference)
    (available : ∃ term : Intent scope, Better scope span reference term) :
    Better scope span reference choice.policy.term := by
  refine ⟨choice.policy.no_regression,?_⟩
  intro reverse
  obtain ⟨term,improves⟩ := available
  obtain ⟨candidate,member,same⟩ := every_accepted_term_is_generated scope span reference term improves.1
  apply choice.maximal candidate member
  change Improves (axes scope) (cost scope span) choice.policy.term candidate.term
  rw [same]
  refine ⟨(vector_iff scope span _ _).mpr ?_,?_⟩
  · intro table inside
    exact benefit_trans cursor (no_worse_bounds_real_benefit scope span improves.1 table inside) (reverse table inside)
  · intro backward
    apply improves.2
    intro table inside
    exact benefit_trans cursor (reverse table inside) ((vector_iff scope span _ _).mp backward table inside)

/-- A replacement planner is checked by a separate scan of all generated terms. -/
def verify (reference term : Intent scope) : Bool := decide (
  NoWorse scope span term reference ∧
  ∀ other ∈ intents scope, NoWorse scope span other reference →
    ¬ strictBenefit scope span term other)

theorem verify_iff (reference term : Intent scope) : verify scope span reference term = true ↔
    NoWorse scope span term reference ∧
    ∀ other : Intent scope, NoWorse scope span other reference →
      ¬ Improves (axes scope) (cost scope span) term other := by
  simp only [verify,decide_eq_true_eq,strictBenefit_iff]
  constructor
  · rintro ⟨accepted,maximal⟩;exact ⟨accepted,fun other => maximal other (every_intent_is_generated scope _)⟩
  · rintro ⟨accepted,maximal⟩;exact ⟨accepted,fun other _ => maximal other⟩

def choiceOfVerified (reference term : Intent scope)
    (verified : verify scope span reference term = true) : Choice scope span reference := by
  let checked := (verify_iff scope span reference term).mp verified
  let candidate : Candidate scope span reference := ⟨term,checked.1⟩
  refine ⟨candidate,?_,?_⟩
  · exact List.mem_filterMap.mpr ⟨term,every_intent_is_generated scope _,by simp [check,checked.1,candidate]⟩
  · intro other _;exact checked.2 other.term other.no_regression

theorem independent_replay_accepts_selection (reference : Intent scope)
    (choice : Choice scope span reference) : verify scope span reference choice.policy.term = true := by
  apply (verify_iff scope span reference _).mpr
  refine ⟨choice.policy.no_regression,?_⟩
  intro other accepted
  obtain ⟨candidate,member,same⟩ := every_accepted_term_is_generated scope span reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes scope) (cost scope span) choice.policy.term candidate.term at maximal
  simpa only [same] using maximal

theorem selection_compares_every_same_future_adaptive_opponent (reference : Intent scope)
    (choice : Choice scope span reference) (oldBound : span ≤ cursor.state.remaining)
    (paidBound : n ≤ (paidPoint scope).state.remaining) :
    (∀ rival : Opponent cursor.source.val.code, accepts cursor
      (tensor scope span choice.policy.term rival) (tensor scope span reference rival)) ∧
    ∀ other : Intent scope, Deployable scope other → ¬ ((∀ rival : Opponent cursor.source.val.code, accepts cursor
      (tensor scope span other rival) (tensor scope span choice.policy.term rival)) ∧
      ¬ (∀ rival : Opponent cursor.source.val.code, benefit cursor
        (tensor scope span choice.policy.term rival) (tensor scope span other rival))) := by
  refine ⟨(finite_relation_iff_every_same_adaptive_opponent scope span (accepts cursor) _ _ oldBound paidBound).mp choice.policy.no_regression.2,?_⟩
  intro other deployable improves
  apply selected_has_no_full_responsibility_dominator scope span reference choice other
  exact ⟨⟨deployable,(finite_relation_iff_every_same_adaptive_opponent scope span (accepts cursor) _ _ oldBound paidBound).mpr improves.1⟩,
    fun reverse => improves.2 ((finite_relation_iff_every_same_adaptive_opponent scope span (benefit cursor) _ _ oldBound paidBound).mp reverse)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Decision
