import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded.Rule
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Programme

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation Continuation.Whole
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

private def workMenu (active : List (Fin code.sites)) (pinned : List code.Key) : List code.Policy :=
  List.pi code.keys (fun key => if keep code active pinned key then words code.actions code.actionLimit else [[]])

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem supported_work (active : List (Fin code.sites)) (pinned : List code.Key) (work : code.Policy)
    (inside : work ∈ workMenu active pinned) : work ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key listed
  have selected := (List.mem_pi _ _).mp inside key listed
  unfold workMenu at inside
  split at selected
  · exact selected
  · have empty : work key listed = [] := List.mem_singleton.mp selected
    rw [empty]
    exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩

private def eventMenu (active : List (Fin code.sites)) (pinned : List code.Key) : List (EventTable code) :=
  List.pi code.keys (fun key => if keep code active pinned key then (ownMoves code key.1).attach else [⟨none,List.mem_cons_self⟩])

def rowMenu (active : List (Fin code.sites)) (pinned : List code.Key) : List (Rule code) :=
  (workMenu active pinned).attach.flatMap fun work =>
    (eventMenu active pinned).map fun events => ⟨⟨work.val,supported_work active pinned work.val work.property⟩,events⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_masked_rule_is_directly_generated (active : List (Fin code.sites)) (pinned : List code.Key) (rule : Rule code) :
    mask code active pinned rule ∈ rowMenu active pinned := by
  have work : (mask code active pinned rule).work.val ∈ workMenu active pinned := by
    apply (List.mem_pi _ _).mpr
    intro key listed
    by_cases retained : keep code active pinned key
    · simp only [mask,if_pos retained]
      exact (List.mem_pi _ _).mp rule.work.property key listed
    · simp only [mask,if_neg retained,List.mem_singleton]
  have events : (mask code active pinned rule).events ∈ eventMenu active pinned := by
    apply (List.mem_pi _ _).mpr
    intro key listed
    by_cases retained : keep code active pinned key
    · simp only [mask,if_pos retained]
      exact List.mem_attach _ _
    · simp only [mask,if_neg retained,List.mem_singleton]
  exact List.mem_flatMap.mpr ⟨⟨(mask code active pinned rule).work.val,work⟩,List.mem_attach _ _,
    List.mem_map.mpr ⟨(mask code active pinned rule).events,events,rfl⟩⟩

/-- Only the active rows and at most one literal-identity escape row vary. -/
def menu (active : List (Fin code.sites)) (fee : Rule code) : List (Rule code) :=
  fee :: (rowMenu active [] ++ code.keys.flatMap (fun key => rowMenu active [key]))

theorem every_projected_rule_is_directly_generated (active : List (Fin code.sites)) (fee rule : Rule code) :
    project code active fee rule ∈ menu active fee := by
  unfold project
  split
  · exact List.mem_cons_self
  · split
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (every_masked_rule_is_directly_generated _ _ _))
    · split
      · rename_i key _
        exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨key,code.key_mem key,every_masked_rule_is_directly_generated _ _ _⟩))
      · contradiction

def projected (domain : List (Cursor code)) (original fee : Rule code) (programme : Program code fuel)
    (frozen ordinal : Nat) : Rule code :=
  if ordinal < frozen then programme.at original ordinal
  else project code (owners domain ordinal) fee (programme.at original ordinal)

def normalize (domain : List (Cursor code)) (original fee : Rule code) (programme : Program code fuel)
    (frozen : Nat) : Program code (Complete.horizon domain) :=
  ⟨(List.range (Complete.horizon domain)).map (projected domain original fee programme frozen),by simp⟩

theorem each_normalized_stage_is_generated (domain : List (Cursor code))
    (original fee : Rule code) (programme : Program code fuel) (frozen ordinal : Nat)
    (inside : ordinal < Complete.horizon domain) :
    (normalize domain original fee programme frozen).at original ordinal = projected domain original fee programme frozen ordinal := by
  simp only [normalize,Program.at,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

def stageMenu (domain : List (Cursor code)) (past : List (Rule code)) (fee : Rule code) (ordinal : Nat) : List (Rule code) :=
  match past[ordinal]? with | some rule => [rule] | none => menu (owners domain ordinal) fee

def catalogue (domain : List (Cursor code)) (past : List (Rule code)) (fee : Rule code) : List (Program code (Complete.horizon domain)) :=
  (List.pi (List.range (Complete.horizon domain)) (stageMenu domain past fee)).map fun table =>
    ⟨(List.range (Complete.horizon domain)).attach.map (fun index => table index.val index.property),by simp⟩

theorem every_guarded_programme_has_a_direct_representative
    (domain : List (Cursor code)) (past : List (Rule code)) (original fee : Rule code)
    (programme : Program code fuel) (retained : programme.controls.take past.length = past) :
    normalize domain original fee programme past.length ∈ catalogue domain past fee := by
  have stages (ordinal : Nat) : projected domain original fee programme past.length ordinal ∈ stageMenu domain past fee ordinal := by
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
      exact every_projected_rule_is_directly_generated _ _ _
  apply List.mem_map.mpr
  refine ⟨(fun index _ => projected domain original fee programme past.length index),
    (List.mem_pi _ _).mpr (fun index _ => stages index),?_⟩
  apply (Program.mk.injEq ..).mpr
  simp only [List.attach_map_val]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Guarded
