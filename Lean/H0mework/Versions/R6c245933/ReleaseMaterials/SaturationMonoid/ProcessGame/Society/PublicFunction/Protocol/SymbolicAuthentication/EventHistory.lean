import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistory

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev Stage := Rule code × Opponent code

def execute (current : Cursor code) : List (Stage (code := code)) → Cursor code
  | [] => current
  | (protocol, rival) :: tail => execute (current.after protocol rival) tail

def history (domain : List (Cursor code)) : List (Rule code) → List (Cursor code)
  | [] => domain
  | protocol :: tail => history (EventStep.advance protocol domain) tail

theorem every_finite_actual_trace_has_a_generated_raw_prefix
    (domain : List (Cursor code)) (left right : Cursor code) (inside : left ∈ domain)
    (same : EventStep.Matches left right) (stages : List (Stage (code := code))) :
    ∃ representative ∈ history domain (stages.map Prod.fst), EventStep.Matches representative (execute right stages) := by
  induction stages generalizing domain left right with
  | nil => exact ⟨left, inside, same⟩
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    have generated : EventStep.next left protocol (EventStep.selected right rival) ∈ EventStep.advance protocol domain :=
      List.mem_flatMap.mpr ⟨left, inside, List.mem_map.mpr
        ⟨EventStep.selected right rival, every_move_is_generated code _, rfl⟩⟩
    exact ih (EventStep.advance protocol domain) _ _ generated (EventStep.matches_step protocol left right same rival)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat)

abbrev publicDomain (installed : List (Rule model.source.code)) := history (Continuation.initial model budget) installed

/-- The public input contains only the installed rules, never the actual
external choices, actual world, content or coverage certificate. -/
def generate (installed : List (Rule model.source.code))
    (site : Fin model.source.code.sites) (reading : Fin model.source.code.signals) (scope : Scope) :=
  LocalContent.produce model.source.code (publicDomain model budget installed) site reading scope

theorem all_finite_adaptive_installations_are_covered
    (world : Distributed.Recall.Information.World model budget) (stages : List (Stage (code := model.source.code))) :
    ∃ representative ∈ publicDomain model budget (stages.map Prod.fst),
      EventStep.Matches representative (execute (ofWorld model budget world) stages) :=
  every_finite_actual_trace_has_a_generated_raw_prefix (Continuation.initial model budget) _ _
    (every_original_world_is_in_the_initial_domain model budget world) (EventStep.matches_self _) stages

theorem available_is_correct_after_any_finite_adaptive_installation
    (world : Distributed.Recall.Information.World model budget) (stages : List (Stage (code := model.source.code)))
    (site : Fin model.source.code.sites) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : generate model budget (stages.map Prod.fst) site
      (CursorSettlement.observation (execute (ofWorld model budget world) stages) site) scope = .available body) :
    CursorSettlement.quote (execute (ofWorld model budget world) stages) scope = some body := by
  obtain ⟨representative, inside, same⟩ := all_finite_adaptive_installations_are_covered model budget world stages
  have reading := congrArg (fun state : State model.source.code => state.frame.inbox site) same.state
  change CursorSettlement.observation representative site =
    CursorSettlement.observation (execute (ofWorld model budget world) stages) site at reading
  have quoted := LocalContent.available_is_correct_for_every_compatible_cursor model.source.code
    (publicDomain model budget (stages.map Prod.fst)) site _ scope body known representative inside reading
  rw [EventStep.matches_quote representative _ same scope] at quoted
  exact quoted

/-- A fresh public installation has no hidden previously installed programme
or unknown phase. All lawful original histories and source responses remain. -/
def ofOrigin (origin : Distributed.Recall.Information.Origin model) : Cursor model.source.code :=
  let source := Distributed.Recall.Information.originSource model budget origin
  ⟨source.reference, source.reference_generated, source.history, source.original, source.opponent, source.side,
    Distributed.Recall.Information.initialInput model budget, [], 0, source.history.length + 1⟩

def genesis := (Distributed.Recall.Information.origins model).map (ofOrigin model budget)

def fromOrigins (installed : List (Rule model.source.code))
    (site : Fin model.source.code.sites) (reading : Fin model.source.code.signals) (scope : Scope) :=
  LocalContent.produce model.source.code (history (genesis model budget) installed) site reading scope

theorem an_origin_query_recovers_the_actual_complete_body
    (origin : Distributed.Recall.Information.Origin model) (stages : List (Stage (code := model.source.code)))
    (site : Fin model.source.code.sites) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : fromOrigins model budget (stages.map Prod.fst) site
      (CursorSettlement.observation (execute (ofOrigin model budget origin) stages) site) scope = .available body) :
    CursorSettlement.quote (execute (ofOrigin model budget origin) stages) scope = some body := by
  have member : ofOrigin model budget origin ∈ genesis model budget :=
    List.mem_map.mpr ⟨origin, Distributed.Recall.Information.every_origin_is_generated model origin, rfl⟩
  obtain ⟨representative, inside, same⟩ := every_finite_actual_trace_has_a_generated_raw_prefix
    (genesis model budget) _ _ member (EventStep.matches_self _) stages
  have reading := congrArg (fun state : State model.source.code => state.frame.inbox site) same.state
  change CursorSettlement.observation representative site =
    CursorSettlement.observation (execute (ofOrigin model budget origin) stages) site at reading
  have quoted := LocalContent.available_is_correct_for_every_compatible_cursor model.source.code
    (history (genesis model budget) (stages.map Prod.fst)) site _ scope body known representative inside reading
  rw [EventStep.matches_quote representative _ same scope] at quoted
  exact quoted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistory
