import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Common
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} (all : Candidates source catalogue)

abbrev scopes := Common.scopes all

theorem every_offer_scope_is_included (offer : Offer all) (index : Index prepared) :
    (offer.view index).scope ∈ scopes all index := Common.every_offer_scope_is_included all index offer

abbrev Table (index : Index prepared) := QuotaJoint.Table (scopes all index)
def tables (index : Index prepared) := QuotaJoint.tables (scopes all index)
abbrev rival (index : Index prepared) (table : Table all index) := QuotaJoint.opponent (scopes all index) table

theorem finite_relation_iff_every_same_adaptive_opponent (first second : Offer all) (index : Index prepared)
    (relation : Planning.Tensor (initial input prepared.saved[index].point) →
      Planning.Tensor (initial input prepared.saved[index].point) → Prop) :
    (∀ table ∈ tables all index,relation ((first.view index).tensor (rival all index table))
      ((second.view index).tensor (rival all index table))) ↔
    ∀ opponent : Opponent (initial input prepared.saved[index].point).source.val.code,
      relation ((first.view index).tensor opponent) ((second.view index).tensor opponent) :=
  QuotaJoint.finite_comparison_iff_every_same_adaptive_opponent (scopes all index) input.span
    (first.view index).scope (second.view index).scope
    (every_offer_scope_is_included all first index) (every_offer_scope_is_included all second index)
    (first.view index).intent (second.view index).intent (first.view index).oldBound
    (first.view index).paidBound (second.view index).paidBound relation

theorem the_source_domain_preserves_every_old_pair_relation (first second : Offer all) (index : Index prepared)
    (relation : Planning.Tensor (initial input prepared.saved[index].point) →
      Planning.Tensor (initial input prepared.saved[index].point) → Prop) :
    (∀ table ∈ tables all index,relation ((first.view index).tensor (rival all index table))
      ((second.view index).tensor (rival all index table))) ↔
    let oldScopes := (offers all).map fun offer => (offer.view index).scope
    ∀ table ∈ QuotaJoint.tables oldScopes,
      relation ((first.view index).tensor (QuotaJoint.opponent oldScopes table))
        ((second.view index).tensor (QuotaJoint.opponent oldScopes table)) := by
  let oldScopes := (offers all).map fun offer => (offer.view index).scope
  have firstIn : (first.view index).scope ∈ oldScopes :=
    List.mem_map.mpr ⟨first,every_paid_accepted_policy_is_retained all first,rfl⟩
  have secondIn : (second.view index).scope ∈ oldScopes :=
    List.mem_map.mpr ⟨second,every_paid_accepted_policy_is_retained all second,rfl⟩
  exact (finite_relation_iff_every_same_adaptive_opponent all first second index relation).trans
    (QuotaJoint.finite_comparison_iff_every_same_adaptive_opponent oldScopes input.span
      (first.view index).scope (second.view index).scope firstIn secondIn
      (first.view index).intent (second.view index).intent (first.view index).oldBound
      (first.view index).paidBound (second.view index).paidBound relation).symm

def Benefit (new previous : Offer all) : Prop := ∀ index : Index prepared,∀ table ∈ tables all index,
  benefit (initial input prepared.saved[index].point) ((new.view index).tensor (rival all index table))
    ((previous.view index).tensor (rival all index table))
instance (new previous : Offer all) : Decidable (Benefit all new previous) := by unfold Benefit;infer_instance

def Accepts (new previous : Offer all) : Prop := ∀ index : Index prepared,∀ table ∈ tables all index,
  accepts (initial input prepared.saved[index].point) ((new.view index).tensor (rival all index table))
    ((previous.view index).tensor (rival all index table))
instance (new previous : Offer all) : Decidable (Accepts all new previous) := by unfold Accepts;infer_instance

def Better (previous new : Offer all) : Prop := Accepts all new previous ∧ ¬ Benefit all previous new

theorem benefit_iff_every_same_adaptive_opponent (new previous : Offer all) : Benefit all new previous ↔
    ∀ index : Index prepared,∀ opponent : Opponent (initial input prepared.saved[index].point).source.val.code,
      benefit (initial input prepared.saved[index].point) ((new.view index).tensor opponent) ((previous.view index).tensor opponent) := by
  constructor
  · intro valid index;exact (finite_relation_iff_every_same_adaptive_opponent all new previous index _).mp (valid index)
  · intro valid index;exact (finite_relation_iff_every_same_adaptive_opponent all new previous index _).mpr (valid index)

theorem accepts_iff_every_same_adaptive_opponent (new previous : Offer all) : Accepts all new previous ↔
    ∀ index : Index prepared,∀ opponent : Opponent (initial input prepared.saved[index].point).source.val.code,
      accepts (initial input prepared.saved[index].point) ((new.view index).tensor opponent) ((previous.view index).tensor opponent) := by
  constructor
  · intro valid index;exact (finite_relation_iff_every_same_adaptive_opponent all new previous index _).mp (valid index)
  · intro valid index;exact (finite_relation_iff_every_same_adaptive_opponent all new previous index _).mpr (valid index)

theorem acceptance_bounds_benefit {new previous : Offer all} (accepted : Accepts all new previous) : Benefit all new previous :=
  fun index table inside => acceptance_bounds_every_real_benefit _ (accepted index table inside)

abbrev Axis := Sigma fun index : Index prepared => Table all index × Offer all
def axes : List (Axis all) := (keys prepared).flatMap fun index => (tables all index).flatMap fun table =>
  (offers all).map fun probe => ⟨index,table,probe⟩
def cost (offer : Offer all) (axis : Axis all) : ℚ :=
  if benefit (initial input prepared.saved[axis.1].point)
      ((offer.view axis.1).tensor (rival all axis.1 axis.2.1))
      ((axis.2.2.view axis.1).tensor (rival all axis.1 axis.2.1)) then 0 else 1

theorem vector_iff (new previous : Offer all) :
    Distributed.NoWorse (axes all) (cost all) new previous ↔ Benefit all new previous := by
  constructor
  · intro vector index table inside
    have tested := vector ⟨index,table,previous⟩ (List.mem_flatMap.mpr ⟨index,List.mem_finRange _,
      List.mem_flatMap.mpr ⟨table,inside,List.mem_map.mpr ⟨previous,every_paid_accepted_policy_is_retained all previous,rfl⟩⟩⟩)
    have self := Planning.benefit_refl (initial input prepared.saved[index].point) ((previous.view index).tensor (rival all index table))
    by_contra failed
    simp only [cost,if_pos self,if_neg failed] at tested
    norm_num at tested
  · intro valid axis inside
    obtain ⟨index,_,mapped⟩ := List.mem_flatMap.mp inside
    obtain ⟨table,listed,mapped⟩ := List.mem_flatMap.mp mapped
    obtain ⟨probe,_,same⟩ := List.mem_map.mp mapped
    subst axis
    by_cases old : benefit (initial input prepared.saved[index].point) ((previous.view index).tensor (rival all index table))
        ((probe.view index).tensor (rival all index table))
    · have now := Planning.benefit_trans _ (valid index table listed) old
      simp only [cost,if_pos old,if_pos now,le_refl]
    · simp only [cost,if_neg old]
      split <;> norm_num

abbrev Choice := Selected (axes all) (cost all) (offers all)
def select : Option (Choice all) := Distributed.choose (axes all) (cost all) (offers all)

theorem selected_has_no_full_cross_record_responsibility_dominator (choice : Choice all) (other : Offer all) :
    ¬ Better all choice.policy other := by
  rintro ⟨accepted,strict⟩
  apply choice.maximal other (every_paid_accepted_policy_is_retained all other)
  exact ⟨(vector_iff all _ _).mpr (acceptance_bounds_benefit all accepted),fun reverse => strict ((vector_iff all _ _).mp reverse)⟩

def baseTensor (index : Index prepared) (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :=
  Planning.tensor (initial input prepared.saved[index].point) input.pricing (reference input prepared.saved[index].point) rival input.span

def ReverseBase (offer : Offer all) : Prop := ∀ index : Index prepared,∀ table ∈ tables all index,
  benefit (initial input prepared.saved[index].point) (baseTensor index (rival all index table))
    ((offer.view index).tensor (rival all index table))
instance (offer : Offer all) : Decidable (ReverseBase all offer) := by unfold ReverseBase;infer_instance

theorem every_available_strict_improvement_is_selected (choice : Choice all)
    (available : ∃ other : Offer all,¬ ReverseBase all other) : ¬ ReverseBase all choice.policy := by
  intro reverse
  obtain ⟨other,strict⟩ := available
  apply choice.maximal other (every_paid_accepted_policy_is_retained all other)
  refine ⟨(vector_iff all _ _).mpr (fun index table inside => Planning.benefit_trans _
    (acceptance_bounds_every_real_benefit _ ((other.view index).baseline (rival all index table))) (reverse index table inside)),?_⟩
  intro backwards
  exact strict (fun index table inside => Planning.benefit_trans _ (reverse index table inside)
    ((vector_iff all _ _).mp backwards index table inside))

def verify (offer : Offer all) : Bool := decide (∀ other ∈ offers all,
  ¬ Improves (axes all) (cost all) offer other)
theorem independent_verification_accepts (choice : Choice all) : verify all choice.policy = true :=
  decide_eq_true choice.maximal

def choiceOfVerified (offer : Offer all) (verified : verify all offer = true) : Choice all :=
  ⟨offer,every_paid_accepted_policy_is_retained all offer,of_decide_eq_true verified⟩

inductive Result where
  | selected (choice : Choice all)
  | blocked (empty : offers all = [])

def compile : Result all := match found : select all with
  | some choice => .selected choice
  | none => .blocked ((Distributed.choose_none_iff_empty _ _ _).mp found)

def Result.checked : Result all → Bool
  | .selected choice => verify all choice.policy
  | .blocked _ => decide (offers all = [])

theorem Result.checks (result : Result all) : result.checked all = true := by
  cases result with
  | selected choice => exact independent_verification_accepts all choice
  | blocked empty => exact decide_eq_true empty

structure Decision where
  private mk ::
  result : Result all
  checked : result.checked all = true

def decideAll : Decision all := ⟨compile all,(compile all).checks all⟩
def decisionOfVerified (offer : Offer all) (verified : verify all offer = true) : Decision all :=
  ⟨.selected (choiceOfVerified all offer verified),verified⟩

inductive Debt where
  | alternative (quota : catalogue.Quota) (record : Record prepared quota.val)
      (listed : ⟨quota,record⟩ ∈ all.entries) (debt : Paid.Debt (prepared := prepared) (units := quota.val))
  | sourceEnumeration | sourceJoin | pointTransport | globalComparison | globalVerification
  | endpointConstruction | ledgerInstallation | storage | announcement

def pending : List (Debt all) := all.entries.attach.flatMap (fun entry =>
    entry.val.2.pending.map (Debt.alternative entry.val.1 entry.val.2 entry.property)) ++
  [.sourceEnumeration,.sourceJoin,.pointTransport,.globalComparison,.globalVerification,
    .endpointConstruction,.ledgerInstallation,.storage,.announcement]

theorem every_original_record_debt_is_retained (quota : catalogue.Quota) (record : Record prepared quota.val)
    (listed : ⟨quota,record⟩ ∈ all.entries) (debt : Paid.Debt (prepared := prepared) (units := quota.val))
    (inside : debt ∈ record.pending) : Debt.alternative quota record listed debt ∈ pending all :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨⟨quota,record⟩,listed⟩,List.mem_attach _ _,List.mem_map.mpr ⟨debt,inside,rfl⟩⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic
