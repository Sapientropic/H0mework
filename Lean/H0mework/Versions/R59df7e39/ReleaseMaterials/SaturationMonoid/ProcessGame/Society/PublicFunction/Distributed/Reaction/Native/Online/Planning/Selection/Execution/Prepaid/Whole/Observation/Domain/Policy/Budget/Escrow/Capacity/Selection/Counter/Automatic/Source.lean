import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Installation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

def paidIndex (funding : EscrowBudget.Funding prepared units) (index : Index prepared) : Index funding.installed :=
  ⟨index.val,by
    have sizes : funding.installed.saved.length = prepared.saved.length := by
      simpa only [List.length_map] using congrArg List.length funding.source_order_and_multiplicity
    exact sizes.symm ▸ index.isLt⟩

theorem paid_point (funding : EscrowBudget.Funding prepared units) (index : Index prepared) :
    funding.installed.saved[paidIndex funding index].point = prepared.saved[index].point := by
  have same := congrArg (fun xs : List (NativePoint input) => xs[index.val]?) funding.source_order_and_multiplicity
  have bounded : index.val < funding.installed.saved.length := (paidIndex funding index).isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem bounded,List.getElem?_eq_getElem index.isLt,Option.map_some] at same
  exact Option.some.inj same

structure Local (point : NativePoint input) where
  scope : Whole.Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position
  intent : Whole.Intent scope
  oldBound : input.span ≤ (initial input point).state.remaining
  paidBound : input.future ≤ (comparisonPoint scope).state.remaining
  deployable : Whole.Deployable scope intent
  baseline : ∀ rival : Opponent (initial input point).source.val.code,
    accepts (initial input point) (Whole.tensor scope input.span intent rival)
      (Planning.tensor (initial input point) input.pricing (reference input point) rival input.span)
namespace Local
variable {first second : NativePoint input}
def tensor {point : NativePoint input} (view : Local point) (rival : Opponent (initial input point).source.val.code) :=
  Whole.tensor view.scope input.span view.intent rival
def endpoint {point : NativePoint input} (view : Local point) : Binding.NativeCursor point :=
  Whole.execute view.scope input.span view.intent
def shape {point : NativePoint input} (view : Local point) := Policy.shape (.ready view.scope) view.intent

theorem transported_shape (same : first = second) (view : Local first) :
    (same ▸ view : Local second).shape = view.shape := by cases same;rfl

theorem transported_endpoint_is_the_same_actual_source (same : first = second) (view : Local first) :
    ((same ▸ view : Local second).endpoint).source.val.input = view.endpoint.source.val.input := by cases same;rfl

theorem actual_window_is_the_complete_initial_cut_tensor {point : NativePoint input} (view : Local point) :
    HEq (Window.evaluate view.endpoint.model (initial input point).depth
      (view.endpoint.depth-(initial input point).depth))
      (view.tensor (initial input point).input.opponent).present :=
  Whole.actual_installation_is_the_compared_full_initial_cut_window view.scope input.span view.intent
end Local

variable {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  (all : Candidates source catalogue)

structure Ready where
  private mk ::
  quota : catalogue.Quota
  record : Record prepared quota.val
  listed : ⟨quota,record⟩ ∈ all.entries
  release : Release prepared quota.val
  observed : record.outcome = .released release

def readyOf (entry : { entry : ((quota : catalogue.Quota) × Record prepared quota.val) // entry ∈ all.entries }) : Option (Ready all) :=
  match observed : entry.val.2.outcome with
  | .released release => some ⟨entry.val.1,entry.val.2,entry.property,release,observed⟩
  | .unfunded _ | .unavailable .. | .exhausted .. | .shortfall .. => none

def ready := all.entries.attach.filterMap (readyOf all)

theorem every_ready_record_is_retained (item : Ready all) : item ∈ ready all := by
  rcases item with ⟨quota,record,listed,release,observed⟩
  apply List.mem_filterMap.mpr
  refine ⟨⟨⟨quota,record⟩,listed⟩,List.mem_attach _ _,?_⟩
  dsimp only [readyOf]
  split
  · rename_i actual same
    cases Outcome.released.inj (observed.symm.trans same)
    rfl
  all_goals
    rename_i same
    cases observed.symm.trans same

structure Offer where
  ready : Ready all
  policy : PublicPolicy.Candidate ready.release.programme.actual.pool

def offers : List (Offer all) := (ready all).flatMap fun item =>
  (PublicPolicy.candidates item.release.programme.actual.pool).map fun policy => ⟨item,policy⟩

private theorem accepted_candidate_is_retained {family : Prepared input} {snapshot : SourceQuota.Snapshot family}
    {domain : SourceQuota.Catalogue snapshot} (pool : Comparison.Pool domain) (policy : PublicPolicy.Candidate pool) :
    policy ∈ PublicPolicy.candidates pool := by
  rcases policy with ⟨term,accepted⟩
  exact List.mem_filterMap.mpr ⟨term,every_section_is_generated pool term,by simp only [PublicPolicy.check,dif_pos accepted]⟩

theorem every_paid_accepted_policy_is_retained (offer : Offer all) : offer ∈ offers all :=
  List.mem_flatMap.mpr ⟨offer.ready,every_ready_record_is_retained all offer.ready,
    List.mem_map.mpr ⟨offer.policy,accepted_candidate_is_retained _ offer.policy,rfl⟩⟩

theorem every_nonselected_accepted_section_is_also_retained (quota : catalogue.Quota) (record : Record prepared quota.val)
    (listed : ⟨quota,record⟩ ∈ all.entries) (release : Release prepared quota.val)
    (observed : record.outcome = .released release) (term : Section release.programme.actual.pool)
    (accepted : Accepted release.programme.actual.pool term) :
    ∃ offer ∈ offers all,offer.ready.quota = quota ∧ HEq offer.ready.release release ∧ HEq offer.policy.term term := by
  let offer : Offer all := ⟨⟨quota,record,listed,release,observed⟩,⟨term,accepted⟩⟩
  exact ⟨offer,every_paid_accepted_policy_is_retained all offer,rfl,HEq.rfl,HEq.rfl⟩

namespace Offer
variable {all} (offer : Offer all)
abbrev funding := offer.ready.release.programme.paid.funding
abbrev actualIndex (index : Index prepared) := paidIndex offer.funding index
abbrev branch (index : Index prepared) := read offer.ready.release.programme.actual.pool offer.policy.term (offer.actualIndex index)

def paidLocal (index : Index offer.ready.release.programme.paid.family) :
    Local offer.ready.release.programme.paid.family.saved[index].point :=
  let branch := read offer.ready.release.programme.actual.pool offer.policy.term index
  let valid := offer.policy.accepted.1.2.2.2 index
  ⟨branch.scope,branch.intent,valid.2.1,valid.2.2.1,valid.2.2.2,
    accepted_policy_covers_every_same_adaptive_opponent _ _ offer.policy.accepted index⟩

def view (index : Index prepared) : Local prepared.saved[index].point :=
  paid_point offer.funding index ▸ offer.paidLocal (offer.actualIndex index)

theorem local_shape (index : Index prepared) : (offer.view index).shape =
    Policy.shape (.ready (offer.branch index).scope) (offer.branch index).intent :=
  Local.transported_shape (paid_point offer.funding index) (offer.paidLocal (offer.actualIndex index))

theorem coherent_at_every_original_point (first second : Index prepared) :
    (offer.view first).shape = (offer.view second).shape := by
  rw [offer.local_shape first,offer.local_shape second]
  exact offer.policy.accepted.1.2.2.1 _ _

theorem every_original_invoice_already_covers_counter_body_and_complete_inner_selection :
    offer.ready.release.programme.calculation.run.spent+offer.ready.release.body.budget.work.length+
      offer.ready.release.work.work.length ≤ offer.ready.quota.val :=
  offer.ready.release.counter_body_and_full_selection_fit_the_actual_invoice

theorem native_point_transport_preserves_the_selected_paid_source (index : Index prepared) :
    (offer.view index).endpoint.source.val.input =
      (offer.paidLocal (offer.actualIndex index)).endpoint.source.val.input :=
  Local.transported_endpoint_is_the_same_actual_source (paid_point offer.funding index) _
end Offer
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic
