import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded.Eligibility
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Work

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Segmented.Publication Segmented.Publication.Reservation.Feedback.Asynchronous

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (announcements : List (Rule model.source.code))

abbrev past := Segmented.reserved model original worker quote quotas
abbrev Candidate := Prefix.Candidate model domain original (past model original worker quote quotas) reference

structure Work where
  done : List (Segmented.Entry model domain original (past model original worker quote quotas) reference)
  todo : List (Program model.source.code (horizon domain))
  partition : done.map Segmented.Entry.tail ++ todo =
    Guarded.eligibleTails model domain original worker receiver quote quotas announcements

def initial : Work model domain original reference worker receiver quote quotas announcements :=
  ⟨[],Guarded.eligibleTails model domain original worker receiver quote quotas announcements,rfl⟩

def advance (quota : Nat) (work : Work model domain original reference worker receiver quote quotas announcements) :
    Work model domain original reference worker receiver quote quotas announcements where
  done := work.done ++ (work.todo.take quota).map (Sparse.classify model domain original (past model original worker quote quotas) reference)
  todo := work.todo.drop quota
  partition := by
    simpa [List.map_append,List.map_map,Function.comp_def,Sparse.classification_keeps_the_submitted_tail,
      List.append_assoc,List.take_append_drop] using work.partition

theorem each_batch_keeps_its_paid_cache_and_consumes_only_its_own_quota
    (quota : Nat) (work : Work model domain original reference worker receiver quote quotas announcements) :
    (advance model domain original reference worker receiver quote quotas announcements quota work).done.take work.done.length = work.done ∧
    (advance model domain original reference worker receiver quote quotas announcements quota work).todo = work.todo.drop quota ∧
    (advance model domain original reference worker receiver quote quotas announcements quota work).done.length =
      work.done.length+min quota work.todo.length := by
  simp only [advance,List.take_append_length,List.length_append,List.length_map,List.length_take,and_self]

def pool (work : Work model domain original reference worker receiver quote quotas announcements) :
    List (Candidate model domain original reference worker quote quotas) :=
  work.done.filterMap (Segmented.Entry.accepted model domain original (past model original worker quote quotas) reference)

theorem every_cached_candidate_belongs_to_the_original_full_pool
    (candidate : Candidate model domain original reference worker quote quotas) :
    candidate ∈ Prefix.candidates model domain original (past model original worker quote quotas) reference :=
  List.mem_filterMap.mpr ⟨candidate.tail,every_bounded_program_is_source_generated _ _ _,by
    simp only [Prefix.check,dif_pos candidate.accepted]⟩

theorem every_original_eligible_candidate_has_a_cached_qualified_representative
    (work : Work model domain original reference worker receiver quote quotas announcements)
    (complete : work.todo = []) (point : View (code := model.source.code)) (send : Rule model.source.code)
    (candidate : Candidate model domain original reference worker quote quotas)
    (suitable : Renewal.eligible model domain original reference worker receiver quote quotas point send announcements candidate = true) :
    Guarded.representative model domain original reference worker receiver quote quotas point send announcements candidate suitable ∈
      pool model domain original reference worker receiver quote quotas announcements work := by
  have generated := Guarded.every_original_eligible_candidate_has_a_generated_eligible_tail model domain original reference worker receiver quote quotas point send announcements candidate suitable
  have covered := work.partition
  rw [complete,List.append_nil] at covered
  rw [←covered] at generated
  obtain ⟨entry,inside,same⟩ := List.mem_map.mp generated
  apply List.mem_filterMap.mpr
  refine ⟨entry,inside,?_⟩
  cases entry with
  | mk tail decision =>
    change tail = (Guarded.representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).tail at same
    cases same
    cases decision with
    | accepted checked => rfl
    | rejected row listed broken =>
      exact False.elim (broken ((Guarded.representative model domain original reference worker receiver quote quotas point send announcements candidate suitable).accepted row listed))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
