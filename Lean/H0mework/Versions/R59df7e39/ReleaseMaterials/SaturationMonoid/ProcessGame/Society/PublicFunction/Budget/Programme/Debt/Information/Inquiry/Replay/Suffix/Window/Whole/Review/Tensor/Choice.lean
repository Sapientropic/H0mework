import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review.Tensor

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review.Tensor.Choice
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code fuel)
  (saved : Snapshot model domain original reference)

structure Candidate where
  index : Index model reference
  accepted : Tensor.accepted model domain original reference saved index

def Candidate.sourceCandidate (candidate : Candidate model domain original reference saved) :
    Selection.Candidate model domain original reference :=
  ⟨(programmes model reference)[candidate.index.val],
    (accepted_exact model domain original reference saved candidate.index).mp candidate.accepted⟩

def check (index : Index model reference) : Option (Candidate model domain original reference saved) :=
  if valid : Tensor.accepted model domain original reference saved index then some ⟨index,valid⟩ else none

def candidates := (List.finRange (programmes model reference).length).filterMap
  (check model domain original reference saved)

theorem every_accepted_index_is_generated (index : Index model reference)
    (valid : Tensor.accepted model domain original reference saved index) :
    (⟨index,valid⟩ : Candidate model domain original reference saved) ∈ candidates model domain original reference saved := by
  apply List.mem_filterMap.mpr
  refine ⟨index,List.mem_finRange _,?_⟩
  simp only [check,dif_pos valid]

private theorem original_candidate_ext (first second : Selection.Candidate model domain original reference)
    (same : first.protocol = second.protocol) : first = second := by
  cases first;cases second;cases same;rfl

theorem every_cached_candidate_is_original (candidate : Candidate model domain original reference saved) :
    candidate.sourceCandidate ∈ Selection.candidates model domain original reference := by
  obtain ⟨other,inside,same⟩ := Selection.every_accepted_protocol_is_generated model domain original reference
    candidate.sourceCandidate.protocol candidate.sourceCandidate.accepted
  exact original_candidate_ext model domain original reference other candidate.sourceCandidate same ▸ inside

theorem every_original_candidate_has_a_cached_representative
    (candidate : Selection.Candidate model domain original reference) :
    ∃ cached ∈ candidates model domain original reference saved,cached.sourceCandidate = candidate := by
  have member : candidate.protocol ∈ programmes model reference :=
    List.mem_cons_of_mem _ (every_bounded_program_is_source_generated _ _ _)
  obtain ⟨index,bounded,same⟩ := List.getElem_of_mem member
  let position : Index model reference := ⟨index,bounded⟩
  have valid : Tensor.accepted model domain original reference saved position := by
    apply (accepted_exact model domain original reference saved position).mpr
    change Selection.acceptable model domain original reference ((programmes model reference)[index])
    rw [same]
    exact candidate.accepted
  let cached : Candidate model domain original reference saved := ⟨position,valid⟩
  refine ⟨cached,every_accepted_index_is_generated model domain original reference saved position valid,?_⟩
  apply original_candidate_ext model domain original reference
  exact same

private structure Scanned (seed : Candidate model domain original reference saved) (remaining : List (Candidate model domain original reference saved)) where
  policy : Candidate model domain original reference saved
  lineage : policy = seed ∨ policy ∈ remaining
  advances : policy = seed ∨ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) seed policy
  maximal : ∀ other ∈ remaining, ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) policy other

private theorem cannot_improve_seed {seed : Candidate model domain original reference saved} {remaining : List (Candidate model domain original reference saved)}
    (result : Scanned model domain original reference saved seed remaining) : ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) result.policy seed := by
  intro backward
  rcases result.advances with same | forward
  · apply improves_irrefl (Selection.axes (fuel := fuel) model domain) (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) seed
    simpa only [same] using backward
  · exact improves_irrefl (Selection.axes (fuel := fuel) model domain) (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) seed (improves_trans forward backward)

private def scan (seed : Candidate model domain original reference saved) : (remaining : List (Candidate model domain original reference saved)) → Scanned model domain original reference saved seed remaining
  | [] => ⟨seed, .inl rfl, .inl rfl, by simp⟩
  | head :: tail =>
    if compact : Tensor.improves model domain original reference saved seed.index head.index then
      have improves : Distributed.Improves (Selection.axes (fuel := fuel) model domain)
          (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) seed head :=
        (Tensor.improves_exact model domain original reference saved seed.index head.index).mp compact
      let result := scan head tail
      { policy := result.policy
        lineage := .inr (by
          rcases result.lineage with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head :: tail)
          · exact List.mem_cons_of_mem _ inside)
        advances := .inr (by
          rcases result.advances with same | further
          · exact same.symm ▸ improves
          · exact improves_trans improves further)
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other; exact cannot_improve_seed model domain original reference saved result
          · exact result.maximal other later }
    else
      have improves : ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain)
          (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) seed head :=
        fun better => compact ((Tensor.improves_exact model domain original reference saved seed.index head.index).mpr better)
      let result := scan seed tail
      { policy := result.policy
        lineage := result.lineage.imp_right (List.mem_cons_of_mem _)
        advances := result.advances
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            intro backward
            rcases result.advances with same | forward
            · exact improves (same ▸ backward)
            · exact improves (improves_trans forward backward)
          · exact result.maximal other later }

def choose (pool : List (Candidate model domain original reference saved)) :
    Option (Selected (Selection.axes (fuel := fuel) model domain)
      (fun candidate : Candidate model domain original reference saved => Selection.benefit model domain original candidate.sourceCandidate.protocol) pool) :=
  match same : pool with
  | [] => none
  | head :: tail =>
      let result := scan model domain original reference saved head tail
      some ⟨result.policy,by
        rcases result.lineage with same | inside
        · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
        · exact List.mem_cons_of_mem _ inside,by
        intro other inside
        rcases List.mem_cons.mp inside with same | inside
        · subst other;exact cannot_improve_seed model domain original reference saved result
        · exact result.maximal other inside⟩

theorem choose_none_iff_empty (pool : List (Candidate model domain original reference saved)) :
    choose model domain original reference saved pool = none ↔ pool = [] := by
  unfold choose
  split <;> simp_all

/-- The complete source-generated tensor is the only computational input. -/
def compileWith : Selection.Outcome model domain original reference :=
  match chosen : choose model domain original reference saved (candidates model domain original reference saved) with
  | some selection => .selected
      { policy := selection.policy.sourceCandidate
        original := every_cached_candidate_is_original model domain original reference saved selection.policy
        maximal := by
          intro other _ better
          obtain ⟨cached,inside,same⟩ := every_original_candidate_has_a_cached_representative model domain original reference saved other
          apply selection.maximal cached inside
          change Distributed.Improves (Selection.axes (fuel := fuel) model domain)
            (Selection.benefit model domain original) selection.policy.sourceCandidate.protocol cached.sourceCandidate.protocol
          change Distributed.Improves (Selection.axes (fuel := fuel) model domain)
            (Selection.benefit model domain original) selection.policy.sourceCandidate.protocol other.protocol at better
          rw [same]
          exact better }
  | none => .blocked (fun programme =>
      match Distributed.inspect (Selection.holds model domain original reference programme) (Replanning.rows model domain) with
      | .rejected row inside broken => ⟨row,inside,broken⟩
      | .accepted all => False.elim (by
          let prior : Selection.Candidate model domain original reference := ⟨programme,all⟩
          obtain ⟨cached,inside,_⟩ := every_original_candidate_has_a_cached_representative model domain original reference saved prior
          rw [choose_none_iff_empty] at chosen
          simp only [chosen,List.not_mem_nil] at inside))

def compile : Selection.Outcome model domain original reference :=
  compileWith model domain original reference (snapshot model domain original reference)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review.Tensor.Choice
