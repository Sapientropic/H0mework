import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Comparison
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
  {catalogue : Catalogue snapshot}

def readyFlag {units : Nat} : (attempt : EscrowBudget.Attempt prepared units) → Continued attempt → Bool
  | .empty ..,_ | .unpaid ..,_ => false
  | .running _,.ready .. => true
  | .running _,.exhausted .. | .running _,.shortfall .. => false

def released {quota : catalogue.Quota} (entry : Comparison.Entry catalogue quota) : Bool := readyFlag entry.attempt entry.continuation

structure ReleasedEntry {quota : catalogue.Quota} (entry : Comparison.Entry catalogue quota) where
  private mk ::
  programme : EscrowBudget.Programme prepared quota.val
  actual : entry.attempt = .running programme
  value : Nat
  release : EscrowBudget.Programme.Release programme value
  continuation : HEq entry.continuation (.ready value release : Continued (.running programme))

def releaseOf {quota : catalogue.Quota} (entry : Comparison.Entry catalogue quota) (ready : released entry = true) : ReleasedEntry entry := by
  rcases entry with ⟨attempt,generated,continuation,same⟩
  cases attempt with
  | empty | unpaid => cases ready
  | running programme =>
      cases continuation with
      | exhausted | shortfall => cases ready
      | ready value release => exact ⟨programme,rfl,value,release,HEq.rfl⟩

variable (pool : Comparison.Pool catalogue)
abbrev Section := ∀ index ∈ keys prepared,Comparison.Branch pool index
abbrev read (policy : Section pool) (index : Index prepared) := policy index (List.mem_finRange index)
def sections : List (Section pool) := List.pi (keys prepared) (fun index => Comparison.branches pool index)
theorem every_section_is_generated (policy : Section pool) : policy ∈ sections pool :=
  (List.mem_pi _ _).mpr (fun _ _ => Comparison.Branch.generated _)

def Uniform (policy : Section pool) : Prop :=
  ∀ first second : Index prepared,(read pool policy first).entry.1 = (read pool policy second).entry.1
instance (policy : Section pool) : Decidable (Uniform pool policy) := by unfold Uniform;infer_instance

def Coherent (policy : Section pool) : Prop :=
  ∀ first second : Index prepared,
    Policy.shape (.ready (read pool policy first).scope) (read pool policy first).intent =
      Policy.shape (.ready (read pool policy second).scope) (read pool policy second).intent
instance (policy : Section pool) : Decidable (Coherent pool policy) := by unfold Coherent;infer_instance

def Admissible (policy : Section pool) : Prop :=
  prepared.saved ≠ [] ∧ Uniform pool policy ∧ Coherent pool policy ∧
    ∀ index : Index prepared,released (read pool policy index).entry.2 = true ∧
      Comparison.OldCovered index ∧ (read pool policy index).Covered ∧ (read pool policy index).Deployable
instance (policy : Section pool) : Decidable (Admissible pool policy) := by unfold Admissible;infer_instance

def oldTensor (index : Index prepared) (opponent : Opponent (initial input prepared.saved[index].point).source.val.code) :=
  Planning.tensor (initial input prepared.saved[index].point) input.pricing (reference input prepared.saved[index].point) opponent input.span

def AcceptsBase (policy : Section pool) : Prop := ∀ index : Index prepared,∀ table ∈ Comparison.tables pool index,
  accepts (initial input prepared.saved[index].point) ((read pool policy index).tensor (Comparison.rival pool index table))
    (oldTensor index (Comparison.rival pool index table))
instance (policy : Section pool) : Decidable (AcceptsBase pool policy) := by unfold AcceptsBase;infer_instance

def CrossAccepts (new previous : Section pool) : Prop := ∀ index : Index prepared,∀ table ∈ Comparison.tables pool index,
  accepts (initial input prepared.saved[index].point) ((read pool new index).tensor (Comparison.rival pool index table))
    ((read pool previous index).tensor (Comparison.rival pool index table))
instance (new previous : Section pool) : Decidable (CrossAccepts pool new previous) := by unfold CrossAccepts;infer_instance

def Benefit (new previous : Section pool) : Prop := ∀ index : Index prepared,∀ table ∈ Comparison.tables pool index,
  benefit (initial input prepared.saved[index].point) ((read pool new index).tensor (Comparison.rival pool index table))
    ((read pool previous index).tensor (Comparison.rival pool index table))
instance (new previous : Section pool) : Decidable (Benefit pool new previous) := by unfold Benefit;infer_instance

theorem benefit_refl (policy : Section pool) : Benefit pool policy policy := fun _ _ _ => Planning.benefit_refl _ _
theorem benefit_trans {first middle last : Section pool} (left : Benefit pool first middle) (right : Benefit pool middle last) :
    Benefit pool first last := fun index table inside => Planning.benefit_trans _ (left index table inside) (right index table inside)
theorem cross_acceptance_bounds_benefit {new previous : Section pool} (accepted : CrossAccepts pool new previous) : Benefit pool new previous :=
  fun index table inside => acceptance_bounds_every_real_benefit _ (accepted index table inside)
theorem accepts_base_trans {new previous : Section pool} (accepted : CrossAccepts pool new previous) (prior : AcceptsBase pool previous) :
    AcceptsBase pool new := fun index table inside => accepts_trans _ (accepted index table inside) (prior index table inside)

def Accepted (policy : Section pool) : Prop := Admissible pool policy ∧ AcceptsBase pool policy
instance (policy : Section pool) : Decidable (Accepted pool policy) := by unfold Accepted;infer_instance

def ReverseBaseBenefit (policy : Section pool) : Prop := ∀ index : Index prepared,∀ table ∈ Comparison.tables pool index,
  benefit (initial input prepared.saved[index].point) (oldTensor index (Comparison.rival pool index table))
    ((read pool policy index).tensor (Comparison.rival pool index table))
instance (policy : Section pool) : Decidable (ReverseBaseBenefit pool policy) := by unfold ReverseBaseBenefit;infer_instance

def Better (previous new : Section pool) : Prop := Admissible pool new ∧ CrossAccepts pool new previous ∧ ¬ Benefit pool previous new

theorem old_tensor_is_preserved_by_the_joint_table (index : Index prepared) (branch : Comparison.Branch pool index)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (oldBound : Comparison.OldCovered index) (newBound : branch.Covered) :
    oldTensor index (Comparison.rival pool index (QuotaJoint.restrict (pool.scopes index) rival)) = oldTensor index rival := by
  have same := QuotaJoint.same_table_preserves_the_complete_initial_cut_tensor branch.scope branch.scope_included input.span
    .keep rival oldBound newBound
  simpa only [oldTensor,Whole.keep_is_the_original_unpaid_tensor] using same

theorem accepted_policy_covers_every_same_adaptive_opponent (policy : Section pool) (accepted : Accepted pool policy) :
    ∀ index : Index prepared,∀ opponent : Opponent (initial input prepared.saved[index].point).source.val.code,
      accepts (initial input prepared.saved[index].point) ((read pool policy index).tensor opponent) (oldTensor index opponent) := by
  intro index opponent
  have admissible := accepted.1.2.2.2 index
  have tested := accepted.2 index (QuotaJoint.restrict (pool.scopes index) opponent)
    (QuotaJoint.restriction_is_generated (pool.scopes index) opponent)
  rw [old_tensor_is_preserved_by_the_joint_table pool index (read pool policy index) opponent admissible.2.1 admissible.2.2.1] at tested
  have current := QuotaJoint.same_table_preserves_the_complete_initial_cut_tensor (read pool policy index).scope
    (read pool policy index).scope_included input.span (read pool policy index).intent opponent admissible.2.1 admissible.2.2.1
  exact (congrArg (fun tensor => accepts (initial input prepared.saved[index].point) tensor (oldTensor index opponent)) current).mp tested

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy
