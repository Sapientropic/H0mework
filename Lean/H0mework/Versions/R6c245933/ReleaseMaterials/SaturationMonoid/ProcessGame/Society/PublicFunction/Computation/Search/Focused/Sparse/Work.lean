import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Tail
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Decision

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (past : List (Rule model.source.code)) (reference : Program model.source.code (horizon domain))

def classify (proposal : Program model.source.code (horizon domain)) : Segmented.Entry model domain original past reference :=
  ⟨proposal,Decision.inspect model domain original reference (Prefix.extension (horizon domain) past proposal)⟩

theorem classification_keeps_the_submitted_tail (proposal : Program model.source.code (horizon domain)) :
    (classify model domain original past reference proposal).tail = proposal := by
  rfl

private def ruleDecidableEq : DecidableEq (Rule model.source.code) := fun first second =>
  decidable_of_iff (∀ key : model.source.code.Key,
    first.work.val key (model.source.code.key_mem key) = second.work.val key (model.source.code.key_mem key) ∧
    (first.events key (model.source.code.key_mem key)).val = (second.events key (model.source.code.key_mem key)).val) (by
    constructor
    · intro same
      have work : first.work = second.work := Subtype.ext (funext fun key => funext fun _ => (same key).1)
      have events : first.events = second.events := funext fun key => funext fun _ => Subtype.ext (same key).2
      cases first;cases second;cases work;cases events;rfl
    · intro same;subst second;exact fun _ => ⟨rfl,rfl⟩)
local instance : DecidableEq (Rule model.source.code) := ruleDecidableEq model

private def programmeDecidableEq : DecidableEq (Program model.source.code (horizon domain)) := fun first second =>
  decidable_of_iff (first.controls = second.controls) (by
    constructor
    · intro same;exact (Continuation.Whole.Program.mk.injEq ..).mpr same
    · intro same;exact congrArg (fun programme => programme.controls) same)
local instance : DecidableEq (Program model.source.code (horizon domain)) := programmeDecidableEq model domain

structure Work where
  done : List (Segmented.Entry model domain original past reference)
  todo : List (Program model.source.code (horizon domain))
  partition : done.map Segmented.Entry.tail ++ todo = tails domain past

def initial : Work model domain original past reference := ⟨[],tails domain past,rfl⟩

def advance (quota : Nat) (work : Work model domain original past reference) :
    Work model domain original past reference where
  done := work.done ++ (work.todo.take quota).map (classify model domain original past reference)
  todo := work.todo.drop quota
  partition := by
    simpa [List.map_append,List.map_map,Function.comp_def,classification_keeps_the_submitted_tail,
      List.append_assoc,List.take_append_drop] using work.partition

theorem each_paid_batch_retains_cached_decisions_and_consumes_only_its_quoted_suffix
    (quota : Nat) (work : Work model domain original past reference) :
    (advance model domain original past reference quota work).done.take work.done.length = work.done ∧
    (advance model domain original past reference quota work).todo = work.todo.drop quota ∧
    (advance model domain original past reference quota work).done.length = work.done.length+min quota work.todo.length := by
  simp only [advance,List.take_append_length,List.length_append,List.length_map,List.length_take,and_self]

def pool (work : Work model domain original past reference) :=
  work.done.filterMap (Segmented.Entry.accepted model domain original past reference)

def comparisonCandidate (candidate : Prefix.Candidate model domain original past reference) :
    Selection.Candidate model domain original reference := ⟨candidate.protocol,candidate.accepted⟩

def comparisonPool (work : Work model domain original past reference) :=
  (pool model domain original past reference work).map (comparisonCandidate model domain original past reference)

/-- Recover the cached tail by executable lookup; the comparison proof cannot choose data. -/
def recover (work : Work model domain original past reference)
    (chosen : Selection.Candidate model domain original reference)
    (member : chosen ∈ comparisonPool model domain original past reference work) :
    {candidate : Prefix.Candidate model domain original past reference //
      candidate ∈ pool model domain original past reference work ∧ candidate.protocol = chosen.protocol} :=
  match found : (pool model domain original past reference work).find? (fun candidate => decide (candidate.protocol = chosen.protocol)) with
  | some candidate => ⟨candidate,List.mem_of_find?_eq_some found,of_decide_eq_true
      (List.find?_some (p := fun candidate : Prefix.Candidate model domain original past reference =>
        decide (candidate.protocol = chosen.protocol)) found)⟩
  | none => False.elim (by
      obtain ⟨candidate,inside,same⟩ := List.mem_map.mp member
      have protocols := congrArg (fun item : Selection.Candidate model domain original reference => item.protocol) same
      exact (List.find?_eq_none.mp found candidate inside) (decide_eq_true protocols))

theorem every_cached_candidate_belongs_to_the_original_full_pool
    (work : Work model domain original past reference)
    (candidate : Prefix.Candidate model domain original past reference)
    (_inside : candidate ∈ pool model domain original past reference work) :
    candidate ∈ Prefix.candidates model domain original past reference :=
  List.mem_filterMap.mpr ⟨candidate.tail,Continuation.Whole.every_bounded_program_is_source_generated _ _ _,by
    simp only [Prefix.check,dif_pos candidate.accepted]⟩

theorem every_original_accepted_candidate_has_a_paid_sparse_representative
    (room : past.length ≤ horizon domain) (work : Work model domain original past reference)
    (complete : work.todo = []) (candidate : Prefix.Candidate model domain original past reference) :
    representative model domain original past reference room candidate ∈ pool model domain original past reference work := by
  have generated := the_generated_normal_tail_is_in_the_direct_catalogue model domain original past room candidate.tail
  have covered := work.partition
  rw [complete,List.append_nil] at covered
  rw [←covered] at generated
  obtain ⟨entry,inside,same⟩ := List.mem_map.mp generated
  apply List.mem_filterMap.mpr
  refine ⟨entry,inside,?_⟩
  cases entry with
  | mk tail decision =>
      change tail = (representative model domain original past reference room candidate).tail at same
      cases same
      cases decision with
      | accepted checked => rfl
      | rejected row listed broken =>
          exact False.elim (broken ((representative model domain original past reference room candidate).accepted row listed))

def finish (room : past.length ≤ horizon domain)
    (work : Work model domain original past reference) (complete : work.todo = []) :
    Option (Prefix.Choice model domain original past reference) :=
  match Review.choose model domain original reference (comparisonPool model domain original past reference work) with
  | none => none
  | some chosen =>
    let retained := recover model domain original past reference work chosen.policy chosen.original
    some ⟨retained.val,
      every_cached_candidate_belongs_to_the_original_full_pool model domain original past reference work retained.val retained.property.1,by
        intro other _
        have maximal := chosen.maximal (comparisonCandidate model domain original past reference (representative model domain original past reference room other))
          (List.mem_map.mpr ⟨representative model domain original past reference room other,
            every_original_accepted_candidate_has_a_paid_sparse_representative model domain original past reference room work complete other,rfl⟩)
        change ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
          (fun proposal : Prefix.Candidate model domain original past reference => Selection.benefit model domain original proposal.protocol)
          retained.val other
        simpa only [Distributed.Improves,Distributed.NoWorse,
          comparisonCandidate,retained.property.2,
          congrFun (representative_preserves_every_original_benefit model domain original past reference room other)] using maximal⟩


theorem an_empty_finished_selection_has_no_cached_accepted_candidate
    (room : past.length ≤ horizon domain) (work : Work model domain original past reference)
    (complete : work.todo = []) (empty : finish model domain original past reference room work complete = none) :
    pool model domain original past reference work = [] := by
  unfold finish at empty
  split at empty
  · have emptyComparison := (Review.choose_none_iff_empty _ _ _ _ _).mp (by assumption)
    exact List.map_eq_nil_iff.mp emptyComparison
  · cases empty

/-- Locate the already paid failure row; no original candidate is reclassified. -/
def rejection (room : past.length ≤ horizon domain) (work : Work model domain original past reference)
    (complete : work.todo = []) (empty : finish model domain original past reference room work complete = none)
    (raw : Program model.source.code (horizon domain)) :
    Selection.Rejection model domain original reference (Prefix.extension (horizon domain) past raw) := by
  let wanted := tail domain past (normal model domain original past raw)
  cases found : work.done.find? (fun entry => decide (entry.tail = wanted)) with
  | none =>
      exact False.elim (by
        have generated := the_generated_normal_tail_is_in_the_direct_catalogue model domain original past room raw
        have covered := work.partition
        rw [complete,List.append_nil] at covered
        rw [←covered] at generated
        obtain ⟨entry,inside,same⟩ := List.mem_map.mp generated
        exact (List.find?_eq_none.mp found entry inside) (decide_eq_true same))
  | some entry =>
      have included := List.mem_of_find?_eq_some found
      have matched : decide (entry.tail = wanted) = true :=
        List.find?_some (p := fun item : Segmented.Entry model domain original past reference => decide (item.tail = wanted)) found
      have same : entry.tail = wanted := of_decide_eq_true matched
      cases inspected : entry.decision with
      | rejected row listed broken =>
          refine ⟨row,listed,fun accepted => broken ?_⟩
          rw [same,the_sparse_tail_rebuilds_its_complete_normal_protocol model domain original past room raw]
          exact (normalization_preserves_each_original_test model domain original past reference raw row).mpr accepted
      | accepted checked =>
          exact False.elim (by
            have inside : (⟨entry.tail,checked⟩ : Prefix.Candidate model domain original past reference) ∈ pool model domain original past reference work :=
              List.mem_filterMap.mpr ⟨entry,included,by simp only [Segmented.Entry.accepted,inspected]⟩
            rw [an_empty_finished_selection_has_no_cached_accepted_candidate model domain original past reference room work complete empty] at inside
            cases inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse
