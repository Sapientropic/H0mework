import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Machine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue} (owner : Ready all)

abbrev Owned := PublicPolicy.Candidate owner.release.programme.actual.pool
def offer (policy : Owned owner) : Offer all := ⟨owner,policy⟩
def policies := PublicPolicy.candidates owner.release.programme.actual.pool
def Rejected (policy : Owned owner) : Prop := ∃ other ∈ offers all,Strict all (offer owner policy) other

def Cleared (remaining : List (Owned owner)) :=
  (∀ policy ∈ remaining,Rejected owner policy) → ∀ policy ∈ policies owner,Rejected owner policy

private theorem reject_head {head : Owned owner} {tail : List (Owned owner)}
    (safe : Cleared owner (head::tail)) (broken : Rejected owner head) : Cleared owner tail := by
  intro later
  apply safe
  intro policy member
  rcases List.mem_cons.mp member with same | inside
  · subst policy;exact broken
  · exact later policy inside

inductive Search where
  | candidates (remaining : List (Owned owner)) (safe : Cleared owner remaining)
  | checking (policy : Owned owner) (rest : List (Owned owner)) (safe : Cleared owner (policy::rest))
      (frame : Frame all (offer owner policy))
  | released (policy : Owned owner) (maximal : Maximal all (offer owner policy))
  | excluded (rejected : ∀ policy ∈ policies owner,Rejected owner policy)

def start : Search owner := .candidates (policies owner) (fun all => all)
inductive Action where
  | load | release | discard | empty
  | native (event : Event all)

def move : Search owner → Option (Search owner × Action (all := all))
  | .released .. | .excluded _ => none
  | .candidates [] safe => some (.excluded (safe (by intro policy inside;cases inside)),.empty)
  | .candidates (head::tail) safe => some (.checking head tail safe (initial all (offer owner head)),.load)
  | .checking policy rest safe frame => match looked : advance all frame with
    | some (after,event) => some (.checking policy rest safe after,.native event)
    | none => match frame with
      | .verified maximal => some (.released policy maximal,.release)
      | .dominated other listed strict => some (.candidates rest (reject_head owner safe ⟨other,listed,strict⟩),.discard)
      | .rivals .. | .forward .. | .reverse .. => False.elim (by
          have impossible := (unfinished_has_an_actual_next all _).mp looked
          cases impossible)

def moveUsing (supplied : List (Probe all)) (exact_source : supplied = probes all) : Search owner → Option (Search owner × Action (all := all))
  | .released .. | .excluded _ => none
  | .candidates [] safe => some (.excluded (safe (by intro policy inside;cases inside)),.empty)
  | .candidates (head::tail) safe => some (.checking head tail safe (initial all (offer owner head)),.load)
  | .checking policy rest safe frame => match looked : advanceUsing all supplied exact_source frame with
    | some (after,event) => some (.checking policy rest safe after,.native event)
    | none => match frame with
      | .verified maximal => some (.released policy maximal,.release)
      | .dominated other listed strict => some (.candidates rest (reject_head owner safe ⟨other,listed,strict⟩),.discard)
      | .rivals .. | .forward .. | .reverse .. => False.elim (by
          have impossible := (unfinished_has_an_actual_next all _).mp (by simpa only [advanceUsing_eq] using looked)
          cases impossible)

theorem moveUsing_eq (supplied : List (Probe all)) (exact_source : supplied = probes all) (before : Search owner) :
    moveUsing owner supplied exact_source before = move owner before := by
  cases exact_source
  cases before with
  | released | excluded => rfl
  | candidates remaining safe => cases remaining <;> rfl
  | checking policy rest safe frame =>
    cases frame with
    | rivals remaining listed safe => cases remaining <;> rfl
    | forward other listed rest rest_listed safe todo within passed => cases todo <;> rfl
    | reverse other listed rest rest_listed safe forward todo within passed => cases todo <;> rfl
    | verified | dominated => rfl

def moveWith (supplied : List (Probe all)) (exact_source : supplied = probes all) (challengers : List (Offer all)) (exact_challengers : challengers = offers all) : Search owner → Option (Search owner × Action (all := all))
  | .released .. | .excluded _ => none
  | .candidates [] safe => some (.excluded (safe (by intro policy inside;cases inside)),.empty)
  | .candidates (head::tail) safe => some (.checking head tail safe (initialUsing all challengers exact_challengers (offer owner head)),.load)
  | .checking policy rest safe frame => match looked : advanceUsing all supplied exact_source frame with
    | some (after,event) => some (.checking policy rest safe after,.native event)
    | none => match frame with
      | .verified maximal => some (.released policy maximal,.release)
      | .dominated other listed strict => some (.candidates rest (reject_head owner safe ⟨other,listed,strict⟩),.discard)
      | .rivals .. | .forward .. | .reverse .. => False.elim (by
          have impossible := (unfinished_has_an_actual_next all _).mp (by simpa only [advanceUsing_eq] using looked)
          cases impossible)

theorem moveWith_eq (supplied : List (Probe all)) (exact_source : supplied = probes all) (challengers : List (Offer all)) (exact_challengers : challengers = offers all) (before : Search owner) :
    moveWith owner supplied exact_source challengers exact_challengers before = move owner before := by
  cases exact_source
  cases exact_challengers
  cases before with
  | released | excluded => rfl
  | candidates remaining safe => cases remaining <;> rfl
  | checking policy rest safe frame =>
    cases frame with
    | rivals remaining listed safe => cases remaining <;> rfl
    | forward other listed rest rest_listed safe todo within passed => cases todo <;> rfl
    | reverse other listed rest rest_listed safe forward todo within passed => cases todo <;> rfl
    | verified | dominated => rfl

def Search.finished : Search owner → Bool
  | .released .. | .excluded _ => true
  | _ => false

def innerBound := 1+(offers all).length*(2*(probes all).length+3)
def Search.rank : Search owner → Nat
  | .candidates remaining _ => 1+remaining.length*(innerBound (all := all)+2)
  | .checking _ rest _ frame => rest.length*(innerBound (all := all)+2)+frame.rank all+2
  | .released .. | .excluded _ => 0

theorem each_search_step_decreases_the_source_rank {before after : Search owner} {action : Action (all := all)}
    (step : move owner before = some (after,action)) : after.rank owner < before.rank owner := by
  cases before with
  | released | excluded => cases step
  | candidates remaining safe =>
    cases remaining <;> dsimp only [move] at step
    all_goals cases Option.some.inj step
    all_goals (simp only [Search.rank,initial,Frame.rank,innerBound,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]; omega)
  | checking policy rest safe frame =>
    dsimp only [move] at step
    split at step
    · rename_i after event observed
      cases Option.some.inj step
      have smaller := each_actual_step_decreases_the_source_rank all observed
      simp only [Search.rank];omega
    · rename_i stopped
      cases frame with
      | verified | dominated =>
        dsimp only at step;cases Option.some.inj step
        simp only [Search.rank,Frame.rank];omega
      | rivals | forward | reverse =>
        have impossible := (unfinished_has_an_actual_next all _).mp stopped
        cases impossible

inductive History : Search owner → Search owner → List (Action (all := all)) → Prop
  | nil (before) : History before before []
  | step {before middle after action work} (observed : move owner before = some (middle,action))
      (later : History middle after work) : History before after (action::work)

structure SearchRun (before : Search owner) (capacity : Nat) where
  private mk ::
  endpoint : Search owner
  work : List (Action (all := all))
  history : History owner before endpoint work
  fits : work.length ≤ capacity

def run : (capacity : Nat) → (before : Search owner) → SearchRun owner before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match step : move owner before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,action) =>
      let later := run capacity after
      ⟨later.endpoint,action::later.work,.step step later.history,by
        have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_credit_preserves_the_unread_search (before : Search owner) :
    (run owner 0 before).endpoint = before ∧ (run owner 0 before).work = [] := ⟨rfl,rfl⟩

theorem move_none_iff_finished (before : Search owner) : move owner before = none ↔ before.finished owner = true := by
  cases before with
  | released | excluded => simp [move,Search.finished]
  | candidates remaining safe => cases remaining <;> simp [move,Search.finished]
  | checking policy rest safe frame =>
    dsimp only [move,Search.finished]
    split
    · simp
    · rename_i stopped
      cases frame with
      | verified | dominated => simp
      | rivals | forward | reverse =>
        have impossible := (unfinished_has_an_actual_next all _).mp stopped
        cases impossible

theorem source_rank_completes_the_entire_owner_search (capacity : Nat) (before : Search owner)
    (enough : before.rank owner ≤ capacity) : (run owner capacity before).endpoint.finished owner = true := by
  induction capacity generalizing before with
  | zero => cases before <;> simp_all [Search.rank,Search.finished,run]
  | succ capacity ih =>
    unfold run
    split
    · rename_i stopped;exact (move_none_iff_finished owner before).mp stopped
    · rename_i after action observed
      exact ih after (by have smaller := each_search_step_decreases_the_source_rank owner observed;omega)

/-- The old selection slots use budget envelopes rather than actual work lengths. -/
def offset := owner.release.programme.calculation.run.spent+owner.release.value
def capacity := owner.quota.val-offset owner

theorem offset_is_covered_by_the_same_invoice : offset owner ≤ owner.quota.val := owner.release.covered

theorem every_old_work_slot_precedes_the_new_tail (token : owner.release.Token) :
    owner.release.ordinal token < offset owner := by
  have count := owner.release.programme.calculation.run.work_count
  have body := owner.release.body_fits
  have selection := owner.release.selection_fits
  have correct := owner.release.correct
  cases token with
  | inl counter => have := counter.isLt;dsimp only [Paid.Release.ordinal,offset];omega
  | inr token => cases token with
    | inl bodyToken => have := bodyToken.isLt;dsimp only [Paid.Release.ordinal,offset];omega
    | inr selectionToken => have := selectionToken.isLt;dsimp only [Paid.Release.ordinal,offset];omega

structure Generated where
  private mk ::
  execution : SearchRun owner (start owner) (capacity owner)
  generated : execution = run owner (capacity owner) (start owner)

def generate : Generated owner := ⟨run owner (capacity owner) (start owner),rfl⟩

namespace Generated
variable {owner} (made : Generated owner)
def spent := made.execution.work.length
def ordinal (event : Fin made.execution.work.length) := offset owner+event.val

theorem ordinal_bound (event : Fin made.execution.work.length) : made.ordinal event < owner.quota.val := by
  have fits := made.execution.fits;have covered := offset_is_covered_by_the_same_invoice owner;have := event.isLt
  dsimp [ordinal,capacity] at *;omega

def slot (index : Index prepared) (event : Fin made.execution.work.length) :
    Fin (((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).bill.units) :=
  ⟨made.ordinal event,by
    rw [((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).size]
    exact made.ordinal_bound event⟩

theorem new_slots_are_injective (index : Index prepared) : Function.Injective (made.slot index) := by
  intro first second same;apply Fin.ext
  have equal := congrArg (fun slot => slot.val) same
  dsimp only [slot,ordinal] at equal;omega

theorem no_new_event_reuses_any_old_slot (index : Index prepared) (old : owner.release.Token)
    (event : Fin made.execution.work.length) : made.slot index event ≠ owner.release.slot index old := by
  intro same
  have different := every_old_work_slot_precedes_the_new_tail owner old
  have equal := congrArg (fun slot => slot.val) same
  change offset owner+event.val = owner.release.ordinal old at equal
  omega

structure Allocation (index : Index prepared) (event : Fin made.execution.work.length) where
  private mk ::
  invoice : EscrowBudget.Charge.Invoice (owner.release.programme.paid.funding.resultAt index)
  slot : Fin invoice.bill.units
  operation : Action (all := all)
  slot_exact : slot.val = made.ordinal event
  operation_exact : operation = made.execution.work[event]

def allocation (index : Index prepared) (event : Fin made.execution.work.length) : Allocation made index event :=
  ⟨(owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index),
    made.slot index event,made.execution.work[event],rfl,rfl⟩

theorem every_search_step_uses_its_original_successful_invoice (index : Index prepared) (event : Fin made.execution.work.length) :
    (made.allocation index event).invoice.bill.payment.succeeded = true ∧
    (made.allocation index event).invoice.bill.units = owner.quota.val ∧
    (made.allocation index event).operation = made.execution.work[event] :=
  ⟨(made.allocation index event).invoice.paid,(made.allocation index event).invoice.size,rfl⟩

def unused := capacity owner-made.spent
theorem the_shared_owner_tail_is_consumed_once_or_retained : made.spent+made.unused = capacity owner := by
  have := made.execution.fits;dsimp [spent,unused];omega

theorem sufficient_actual_tail_finishes_every_own_candidate (enough : (start owner).rank owner ≤ capacity owner) :
    made.execution.endpoint.finished owner = true := by
  rw [made.generated];exact source_rank_completes_the_entire_owner_search owner _ _ enough

def completed : Option (Choice all) := match made.execution.endpoint with
  | .released policy maximal => some (choice all (offer owner policy) maximal)
  | _ => none

def retained (index : Index prepared) : Binding.NativeCursor prepared.saved[index].point :=
  paid_point owner.release.programme.paid.funding index ▸
    SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Protocol.retained owner.release.programme.paid.family.saved[paidIndex owner.release.programme.paid.funding index].stage

def endpoint (index : Index prepared) : Binding.NativeCursor prepared.saved[index].point :=
  match made.execution.endpoint with
  | .released policy _ => ((offer owner policy).view index).endpoint
  | _ => retained (owner := owner) index

theorem only_the_verified_global_policy_is_executed (policy : Owned owner) (maximal : Maximal all (offer owner policy))
    (released : made.execution.endpoint = .released policy maximal) (index : Index prepared) :
    made.endpoint index = ((offer owner policy).view index).endpoint := by simp only [endpoint,released]

end Generated
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review
