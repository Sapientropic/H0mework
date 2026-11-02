import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (past : List (Distributed.Recall.Information.Agency.Protocol.Rule model.source.code))
  (reference : Program model.source.code (horizon domain))

/-- Cached decisions always use the entire precommitted fee schedule. -/
structure Entry where
  tail : Program model.source.code (horizon domain)
  decision : Inspection
    (Selection.holds model domain original reference (Prefix.extension (horizon domain) past tail))
    (Replanning.rows model domain)

def classify (tail : Program model.source.code (horizon domain)) : Entry model domain original past reference :=
  ⟨tail,Distributed.inspect
    (Selection.holds model domain original reference (Prefix.extension (horizon domain) past tail))
    (Replanning.rows model domain)⟩

def Entry.accepted (entry : Entry model domain original past reference) :
    Option (Prefix.Candidate model domain original past reference) :=
  match entry.decision with
  | .accepted checked => some ⟨entry.tail,checked⟩
  | .rejected .. => none

structure Work where
  done : List (Entry model domain original past reference)
  todo : List (Program model.source.code (horizon domain))
  partition : done.map Entry.tail ++ todo = programs model.source.code (horizon domain)

def initial : Work model domain original past reference := ⟨[],programs _ _,rfl⟩

def advance (quota : Nat) (work : Work model domain original past reference) :
    Work model domain original past reference where
  done := work.done ++ (work.todo.take quota).map (classify model domain original past reference)
  todo := work.todo.drop quota
  partition := by
    simpa [List.map_append,List.map_map,Function.comp_def,classify,
      List.append_assoc,List.take_append_drop] using work.partition

theorem each_segment_preserves_every_cached_decision_and_exactly_its_unprocessed_suffix
    (quota : Nat) (work : Work model domain original past reference) :
    (advance model domain original past reference quota work).done.take work.done.length = work.done ∧
    (advance model domain original past reference quota work).todo = work.todo.drop quota ∧
    (advance model domain original past reference quota work).done.length =
      work.done.length + min quota work.todo.length := by
  simp only [advance,List.take_append_length,List.length_append,List.length_map,List.length_take,and_self]

def pool (work : Work model domain original past reference) := work.done.filterMap (Entry.accepted model domain original past reference)

theorem a_complete_cache_contains_exactly_all_accepted_candidates
    (work : Work model domain original past reference) (complete : work.todo = [])
    (candidate : Prefix.Candidate model domain original past reference) :
    candidate ∈ pool model domain original past reference work ↔
      candidate ∈ Prefix.candidates model domain original past reference := by
  constructor
  · intro inside
    obtain ⟨entry,_,kept⟩ := List.mem_filterMap.mp inside
    have generated := every_bounded_program_is_source_generated model.source.code (horizon domain) candidate.tail
    apply List.mem_filterMap.mpr
    exact ⟨candidate.tail,generated,by simp only [Prefix.check,dif_pos candidate.accepted]⟩
  · intro _
    have generated := every_bounded_program_is_source_generated model.source.code (horizon domain) candidate.tail
    have covered := work.partition
    rw [complete,List.append_nil] at covered
    change _ ∈ programs model.source.code (horizon domain) at generated
    rw [←covered] at generated
    obtain ⟨entry,inside,same⟩ := List.mem_map.mp generated
    apply List.mem_filterMap.mpr
    refine ⟨entry,inside,?_⟩
    cases entry with
    | mk tail decision =>
      change tail = candidate.tail at same
      subst tail
      cases decision with
      | accepted checked => rfl
      | rejected row listed broken => exact False.elim (broken (candidate.accepted row listed))

/-- Selection consumes the stored accepted entries, without reclassifying any tail. -/
def finish (work : Work model domain original past reference) (complete : work.todo = []) :
    Option (Prefix.Choice model domain original past reference) :=
  match Distributed.choose (Selection.axes (fuel := horizon domain) model domain)
    (fun candidate : Prefix.Candidate model domain original past reference =>
      Selection.benefit model domain original candidate.protocol)
    (pool model domain original past reference work) with
  | none => none
  | some choice => some ⟨choice.policy,
      (a_complete_cache_contains_exactly_all_accepted_candidates model domain original past reference work complete _).mp choice.original,
      fun other inside => choice.maximal other
        ((a_complete_cache_contains_exactly_all_accepted_candidates model domain original past reference work complete _).mpr inside)⟩

theorem an_exhausted_unsuccessful_cache_rejects_every_finite_tail
    (work : Work model domain original past reference) (complete : work.todo = [])
    (empty : finish model domain original past reference work complete = none)
    (tail : Complete.FiniteProgram model.source.code) :
    ∃ entry ∈ work.done,
      Prefix.extension (horizon domain) past entry.tail = Prefix.extension (horizon domain) past tail.2 ∧
      ∃ row listed broken, entry.decision = .rejected row listed broken := by
  have poolEmpty : pool model domain original past reference work = [] := by
    unfold finish at empty
    split at empty
    · exact (Distributed.choose_none_iff_empty _ _ _).mp (by assumption)
    · cases empty
  have generated := every_bounded_program_is_source_generated model.source.code (horizon domain) (clip (horizon domain) tail.2)
  have covered := work.partition
  rw [complete,List.append_nil] at covered
  change _ ∈ programs model.source.code (horizon domain) at generated
  rw [←covered] at generated
  obtain ⟨entry,inside,same⟩ := List.mem_map.mp generated
  refine ⟨entry,inside,?_,?_⟩
  · rw [same]
    exact Prefix.tail_normalization_does_not_change_any_consumed_prefix_extension _ _ _
  · cases decision : entry.decision with
    | rejected row listed broken => exact ⟨row,listed,broken,rfl⟩
    | accepted checked =>
      have member : (⟨entry.tail,checked⟩ : Prefix.Candidate model domain original past reference) ∈ pool model domain original past reference work :=
        List.mem_filterMap.mpr ⟨entry,inside,by simp only [Entry.accepted,decision]⟩
      rw [poolEmpty] at member
      cases member

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented
