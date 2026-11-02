import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Programme

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Distributed.Recall.Information.Agency.Protocol.Continuation.Whole
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

private def workMenu (active : List (Fin code.sites)) : List code.Policy :=
  List.pi code.keys (fun key => if key.1 ∈ active then words code.actions code.actionLimit else [[]])

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem supported_work (active : List (Fin code.sites)) (work : code.Policy)
    (inside : work ∈ workMenu active) : work ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key listed
  have selected := (List.mem_pi _ _).mp inside key listed
  unfold workMenu at inside
  split at selected
  · exact selected
  · have empty : work key listed = [] := List.mem_singleton.mp selected
    rw [empty]
    exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩

private def eventMenu (active : List (Fin code.sites)) : List (EventTable code) :=
  List.pi code.keys (fun key => if key.1 ∈ active then (ownMoves code key.1).attach else [⟨none,List.mem_cons_self⟩])

/-- Each slot enumerates only its source-generated active rows. -/
def rowMenu (active : List (Fin code.sites)) : List (Rule code) :=
  (workMenu active).attach.flatMap fun work =>
    (eventMenu active).map fun events => ⟨⟨work.val,supported_work active work.val work.property⟩,events⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_focused_rule_is_in_the_sparse_row_menu (active : List (Fin code.sites)) (rule : Rule code) :
    focus code active rule ∈ rowMenu active := by
  have work : (focus code active rule).work.val ∈ workMenu active := by
    apply (List.mem_pi _ _).mpr
    intro key listed
    by_cases owned : key.1 ∈ active
    · simp only [focus,if_pos owned]
      exact (List.mem_pi _ _).mp rule.work.property key listed
    · simp only [focus,if_neg owned,List.mem_singleton]
  have events : (focus code active rule).events ∈ eventMenu active := by
    apply (List.mem_pi _ _).mpr
    intro key listed
    by_cases owned : key.1 ∈ active
    · simp only [focus,if_pos owned]
      exact List.mem_attach _ _
    · simp only [focus,if_neg owned,List.mem_singleton]
  apply List.mem_flatMap.mpr
  refine ⟨⟨(focus code active rule).work.val,work⟩,List.mem_attach _ _,List.mem_map.mpr ?_⟩
  exact ⟨(focus code active rule).events,events,rfl⟩

def stageMenu (domain : List (Cursor code)) (past : List (Rule code)) (ordinal : Nat) : List (Rule code) :=
  match past[ordinal]? with | some rule => [rule] | none => rowMenu (owners domain ordinal)

def catalogue (domain : List (Cursor code)) (past : List (Rule code)) : List (Program code (Continuation.Whole.Complete.horizon domain)) :=
  (List.pi (List.range (Continuation.Whole.Complete.horizon domain)) (stageMenu domain past)).map fun table =>
    ⟨(List.range (Continuation.Whole.Complete.horizon domain)).attach.map (fun index => table index.val index.property),by simp⟩

theorem every_normalized_paid_programme_has_a_generated_sparse_representative
    (domain : List (Cursor code)) (past : List (Rule code)) (original : Rule code)
    (programme : Program code fuel) (retained : programme.controls.take past.length = past) :
    normalize domain original programme past.length ∈ catalogue domain past := by
  have stages (ordinal : Nat) : projected domain original programme past.length ordinal ∈ stageMenu domain past ordinal := by
    by_cases earlier : ordinal < past.length
    · have same := congrArg (fun controls : List (Rule code) => controls[ordinal]?) retained
      rw [List.getElem?_take_of_lt earlier] at same
      have present : ordinal < programme.controls.length := by
        have size := congrArg List.length retained
        simp only [List.length_take] at size
        omega
      unfold stageMenu projected
      rw [←same,List.getElem?_eq_getElem present,if_pos earlier]
      simp only [Program.at,List.getElem?_eq_getElem present,Option.getD_some,List.mem_singleton]
    · unfold stageMenu projected
      rw [List.getElem?_eq_none (by omega),if_neg earlier]
      exact every_focused_rule_is_in_the_sparse_row_menu _ _
  apply List.mem_map.mpr
  refine ⟨(fun index _ => projected domain original programme past.length index),(List.mem_pi _ _).mpr (fun index _ => stages index),?_⟩
  apply (Program.mk.injEq ..).mpr
  simp only [List.attach_map_val]


theorem normalization_keeps_the_literal_paid_prefix
    (domain : List (Cursor code)) (past : List (Rule code)) (original : Rule code)
    (programme : Program code fuel) (retained : programme.controls.take past.length = past)
    (room : past.length ≤ Continuation.Whole.Complete.horizon domain) :
    (normalize domain original programme past.length).controls.take past.length = past := by
  have size : past.length ≤ programme.controls.length := by
    have sizes := congrArg List.length retained
    simp only [List.length_take] at sizes
    omega
  apply Eq.trans (b := programme.controls.take past.length) ?_ retained
  apply List.ext_getElem
  · simp only [normalize,List.length_take,List.length_map,List.length_range]
    omega
  · intro index left right
    have inside : index < past.length := by
      have upper := List.length_take_le past.length (normalize domain original programme past.length).controls
      omega
    have present : index < programme.controls.length := inside.trans_le size
    simp only [List.getElem_take,normalize,List.getElem_map,List.getElem_range,projected,if_pos inside,
      Program.at,List.getElem?_eq_getElem present,Option.getD_some]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
