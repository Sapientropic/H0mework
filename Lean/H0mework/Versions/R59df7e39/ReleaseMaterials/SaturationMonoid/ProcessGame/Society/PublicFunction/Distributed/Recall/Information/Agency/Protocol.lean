import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

section Core

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

def ownMoves (site : Fin code.sites) : List (Move code) :=
  none :: ((code.eventAlphabet.attach.filter fun event => match event.val with
    | .send sender _ => decide (sender = site)
    | .activate worker => decide (worker = site)
    | _ => false).map some)

abbrev LocalMove (site : Fin code.sites) := {move // move ∈ ownMoves code site}
abbrev EventTable := ∀ key ∈ code.keys, LocalMove code key.1

def eventTables : List (EventTable code) := List.pi code.keys fun key => (ownMoves code key.1).attach

structure Rule where
  work : {policy // policy ∈ code.policies}
  events : EventTable code

def rules : List (Rule code) := code.policies.attach.flatMap fun work =>
  (eventTables code).map fun events => ⟨work,events⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_rule_is_source_generated (rule : Rule code) : rule ∈ rules code := by
  apply List.mem_flatMap.mpr
  refine ⟨rule.work,List.mem_attach _ _,List.mem_map.mpr ⟨rule.events,?_,rfl⟩⟩
  apply (List.mem_pi _ _).mpr
  intro key inside
  exact List.mem_attach _ _

def localEvent (rule : Rule code) (site : Fin code.sites) (signal : Fin code.signals) : Move code :=
  (rule.events (site,signal) (code.key_mem _)).val

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_local_event_has_its_own_worker (rule : Rule code) (site : Fin code.sites)
    (signal : Fin code.signals) (event : Reaction.Choice code)
    (chosen : localEvent code rule site signal = some event) :
    match event.val with
    | .send sender _ => sender = site
    | .activate worker => worker = site
    | _ => False := by
  have generated := (rule.events (site,signal) (code.key_mem _)).property
  change localEvent code rule site signal ∈ ownMoves code site at generated
  rw [chosen] at generated
  have present := (List.mem_cons.mp generated).resolve_left (by simp)
  obtain ⟨other,inside,same⟩ := List.mem_map.mp present
  have equal := Option.some.inj same
  subst other
  have allowed := (List.mem_filter.mp inside).2
  rcases event with ⟨event,supported⟩
  cases event <;> simp only [Bool.false_eq_true,decide_eq_true_eq] at allowed <;> exact allowed

def driver (start : Nat) (rule : Rule code) (rival : Opponent code) : Opponent code :=
  fun history past frame => match ownerAt code start history.length with
    | some site => localEvent code rule site (frame.inbox site)
    | none => externalChoice code (rival history past frame)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem own_action_uses_only_its_actual_local_record (start : Nat) (rule : Rule code)
    (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : ownerAt code start history.length = some site)
    (same : left.inbox site = right.inbox site) :
    driver code start rule first history past left = driver code start rule second history past right := by
  simp only [driver,owned,same]

variable (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat) (rule : Rule source.code)

def term : Cut.Term source input cut := by
  refine ⟨List.replicate (source.feedbackState input cut).remaining (some rule.work.val),?_⟩
  apply (mem_sequences_iff _ _ _).mpr
  refine ⟨by simp,?_⟩
  intro control inside
  have same := (List.mem_replicate.mp inside).2
  subst control
  exact List.mem_append_right _ (List.mem_map.mpr ⟨rule.work.val,rule.work.property,rfl⟩)

abbrev controller (rival : Opponent source.code) := driver source.code (Agency.start source cut) rule rival
abbrev target (rival : Opponent source.code) := Future.target source input cut (controller source cut rule rival) (term source input cut rule).val
abbrev targetInput (rival : Opponent source.code) := Future.takeover source input cut (controller source cut rule rival)

/-- The guard is the original finite decision domain, shared by every rule. -/
abbrev tableController (table : Cut.Table source input cut) :=
  Future.jointOpponent source input cut (controller source cut rule (Cut.opponent source input cut table))

theorem one_external_restriction_controls_every_own_rule (rival : Opponent source.code) :
    tableController source input cut rule
        (Residual.restrict source.code (Residual.seed source input cut) (Residual.schedules source input cut) rival) =
      Future.jointOpponent source input cut (controller source cut rule rival) := by
  funext history past frame
  change (if member : (history,past,frame) ∈ Residual.keys source.code (Residual.seed source input cut) (Residual.schedules source input cut)
    then controller source cut rule (Cut.opponent source input cut
      (Residual.restrict source.code (Residual.seed source input cut) (Residual.schedules source input cut) rival)) history past frame
    else none) = _
  by_cases member : (history,past,frame) ∈ Residual.keys source.code (Residual.seed source input cut) (Residual.schedules source input cut)
  · simp only [dif_pos member,Future.jointOpponent,Residual.respond,Residual.restrict]
    change driver source.code (Agency.start source cut) rule (Cut.opponent source input cut _) history past frame =
      driver source.code (Agency.start source cut) rule rival history past frame
    simp only [driver]
    cases ownerAt source.code (Agency.start source cut) history.length with
    | some site => rfl
    | none => simp only [Cut.opponent,Residual.respond,dif_pos member,Residual.restrict]
  · simp only [Future.jointOpponent,Residual.respond,dif_neg member]


end Core

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol
