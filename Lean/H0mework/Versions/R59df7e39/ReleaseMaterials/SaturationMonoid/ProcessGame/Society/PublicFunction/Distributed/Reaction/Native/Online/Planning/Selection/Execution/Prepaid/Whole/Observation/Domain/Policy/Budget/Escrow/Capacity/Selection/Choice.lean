import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Policy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
open Comparison
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

abbrev Axis := Sigma fun index : Index prepared => Comparison.Table pool index × Section pool
def axes : List (Axis pool) := (keys prepared).flatMap fun index => (Comparison.tables pool index).flatMap fun table =>
  (sections pool).map fun probe => ⟨index,table,probe⟩
def cost (policy : Section pool) (axis : Axis pool) : ℚ :=
  if benefit (initial input prepared.saved[axis.1].point)
    ((read pool policy axis.1).tensor (Comparison.rival pool axis.1 axis.2.1))
    ((read pool axis.2.2 axis.1).tensor (Comparison.rival pool axis.1 axis.2.1)) then 0 else 1

theorem vector_iff (new previous : Section pool) :
    Distributed.NoWorse (axes pool) (cost pool) new previous ↔ Benefit pool new previous := by
  constructor
  · intro vector index table inside
    have tested := vector ⟨index,table,previous⟩ (List.mem_flatMap.mpr ⟨index,List.mem_finRange _,
      List.mem_flatMap.mpr ⟨table,inside,List.mem_map.mpr ⟨previous,every_section_is_generated pool previous,rfl⟩⟩⟩)
    have self := Planning.benefit_refl (initial input prepared.saved[index].point) ((read pool previous index).tensor (Comparison.rival pool index table))
    by_contra failed
    simp only [cost,if_pos self,if_neg failed] at tested
    norm_num at tested
  · intro all axis inside
    obtain ⟨index,_,mapped⟩ := List.mem_flatMap.mp inside
    obtain ⟨table,listed,mapped⟩ := List.mem_flatMap.mp mapped
    obtain ⟨probe,_,same⟩ := List.mem_map.mp mapped
    subst axis
    by_cases old : benefit (initial input prepared.saved[index].point) ((read pool previous index).tensor (Comparison.rival pool index table))
        ((read pool probe index).tensor (Comparison.rival pool index table))
    · have now := Planning.benefit_trans _ (all index table listed) old
      simp only [cost,if_pos old,if_pos now,le_refl]
    · simp only [cost,if_neg old]
      split <;> norm_num

structure Candidate where
  term : Section pool
  accepted : Accepted pool term

def check (term : Section pool) : Option (Candidate pool) :=
  if accepted : Accepted pool term then some ⟨term,accepted⟩ else none
def candidates := (sections pool).filterMap (check pool)
theorem every_accepted_section_is_generated (term : Section pool) (accepted : Accepted pool term) :
    ∃ candidate ∈ candidates pool,candidate.term = term :=
  ⟨⟨term,accepted⟩,List.mem_filterMap.mpr ⟨term,every_section_is_generated pool term,by simp only [check,dif_pos accepted]⟩,rfl⟩

abbrev Choice := Selected (axes pool) (fun candidate : Candidate pool => cost pool candidate.term) (candidates pool)
def select : Option (Choice pool) := Distributed.choose (axes pool) (fun candidate => cost pool candidate.term) (candidates pool)

theorem selected_has_no_cross_quota_public_policy_dominator (choice : Choice pool) (other : Section pool) :
    ¬ Better pool choice.policy.term other := by
  rintro ⟨admissible,accepted,strict⟩
  obtain ⟨candidate,listed,same⟩ := every_accepted_section_is_generated pool other
    ⟨admissible,accepts_base_trans pool accepted choice.policy.accepted.2⟩
  apply choice.maximal candidate listed
  change Improves (axes pool) (cost pool) choice.policy.term candidate.term
  rw [same]
  exact ⟨(vector_iff pool _ _).mpr (cross_acceptance_bounds_benefit pool accepted),fun reverse => strict ((vector_iff pool _ _).mp reverse)⟩

theorem every_available_real_improvement_is_selected (choice : Choice pool)
    (available : ∃ other : Section pool,Accepted pool other ∧ ¬ ReverseBaseBenefit pool other) :
    Accepted pool choice.policy.term ∧ ¬ ReverseBaseBenefit pool choice.policy.term := by
  refine ⟨choice.policy.accepted,?_⟩
  intro reverse
  obtain ⟨other,accepted,strict⟩ := available
  obtain ⟨candidate,listed,same⟩ := every_accepted_section_is_generated pool other accepted
  apply choice.maximal candidate listed
  change Improves (axes pool) (cost pool) choice.policy.term candidate.term
  rw [same]
  refine ⟨(vector_iff pool _ _).mpr (fun index table inside => Planning.benefit_trans _
    (acceptance_bounds_every_real_benefit _ (accepted.2 index table inside)) (reverse index table inside)),?_⟩
  intro backwards
  exact strict (fun index table inside => Planning.benefit_trans _ (reverse index table inside)
    ((vector_iff pool _ _).mp backwards index table inside))

def verify (term : Section pool) : Bool := decide (Accepted pool term ∧
  ∀ other ∈ sections pool,Accepted pool other → ¬ Improves (axes pool) (cost pool) term other)
theorem independent_verifier_accepts (choice : Choice pool) : verify pool choice.policy.term = true := by
  apply decide_eq_true
  refine ⟨choice.policy.accepted,?_⟩
  intro other _ accepted
  obtain ⟨candidate,listed,same⟩ := every_accepted_section_is_generated pool other accepted
  intro improves
  apply choice.maximal candidate listed
  change Improves (axes pool) (cost pool) choice.policy.term candidate.term
  simpa only [same] using improves

namespace Choice
variable {pool} (choice : Choice pool)
def actualRelease (index : Index prepared) : ReleasedEntry (read pool choice.policy.term index).entry.2 :=
  releaseOf _ (choice.policy.accepted.1.2.2.2 index).1

def endpoint (index : Index prepared) := Whole.execute (read pool choice.policy.term index).scope input.span (read pool choice.policy.term index).intent

theorem same_uniform_quota (first second : Index prepared) :
    (read pool choice.policy.term first).entry.1 = (read pool choice.policy.term second).entry.1 := choice.policy.accepted.1.2.1 first second

theorem same_quota_has_the_same_generated_attempt (first second : Index prepared) :
    HEq (read pool choice.policy.term first).entry.2.attempt (read pool choice.policy.term second).entry.2.attempt := by
  have same := choice.same_uniform_quota first second
  generalize left : (read pool choice.policy.term first).entry = a at *
  generalize right : (read pool choice.policy.term second).entry = b at *
  rcases a with ⟨qa,ea⟩
  rcases b with ⟨qb,eb⟩
  cases same
  exact heq_of_eq (ea.generated.trans eb.generated.symm)

theorem actual_window_is_the_selected_common_cut_tensor (index : Index prepared) :
    HEq (Window.evaluate (choice.endpoint index).model (initial input prepared.saved[index].point).depth
      ((choice.endpoint index).depth-(initial input prepared.saved[index].point).depth))
      ((read pool choice.policy.term index).tensor (initial input prepared.saved[index].point).input.opponent).present :=
  Whole.actual_installation_is_the_compared_full_initial_cut_window (read pool choice.policy.term index).scope input.span (read pool choice.policy.term index).intent
end Choice
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy
