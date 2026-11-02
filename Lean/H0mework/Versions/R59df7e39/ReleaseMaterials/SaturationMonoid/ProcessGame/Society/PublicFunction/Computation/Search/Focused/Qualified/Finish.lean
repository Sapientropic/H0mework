import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Scan
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Selection

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (allocation : List Allocation) (announcements : List (Rule model.source.code))
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)
  (send : Rule model.source.code)

/-- Both completed queues retain their original physical payment source. -/
structure Finished where
  global : GlobalCache model domain original reference worker quote allocation
  global_present : (execution model domain original reference worker quote allocation rival point).cached = some global
  global_complete : global.todo = []
  qualified : Cache model domain original reference worker receiver quote allocation announcements
  qualified_present : (observed model domain original reference worker receiver quote allocation announcements rival point).cached = some qualified
  qualified_complete : qualified.todo = []
  room : (past model original worker quote (globalQuotas allocation)).length ≤ horizon domain
  executed : (execution model domain original reference worker quote allocation rival point).remaining = []
  closing : (execution model domain original reference worker quote allocation rival point).closingPaid = true
  choice : Option {choice : Choice model domain original reference worker quote (globalQuotas allocation) //
    eligible model domain original reference worker receiver quote (globalQuotas allocation) announcements point send choice.policy = true}
  generated : choice = choose model domain original reference worker receiver quote (globalQuotas allocation) announcements
    point send room global global_complete qualified

def finish : Option (Finished model domain original reference worker receiver quote allocation announcements point rival send) :=
  if ready : (past model original worker quote (globalQuotas allocation)).length ≤ horizon domain ∧
      (execution model domain original reference worker quote allocation rival point).remaining = [] ∧
      (execution model domain original reference worker quote allocation rival point).closingPaid = true then
    match globalSeen : (execution model domain original reference worker quote allocation rival point).cached with
    | none => none
    | some global => if globalComplete : global.todo = [] then
        match qualifiedSeen : (observed model domain original reference worker receiver quote allocation announcements rival point).cached with
        | none => none
        | some qualified => if qualifiedComplete : qualified.todo = [] then
            some ⟨global,globalSeen,globalComplete,qualified,qualifiedSeen,qualifiedComplete,ready.1,ready.2.1,ready.2.2,
              choose model domain original reference worker receiver quote (globalQuotas allocation) announcements
                point send ready.1 global globalComplete qualified,rfl⟩
          else none
      else none
  else none

inductive CloseReason where
  | outsideWindow (outside : ¬ (past model original worker quote (globalQuotas allocation)).length ≤ horizon domain)
  | pending (left : (execution model domain original reference worker quote allocation rival point).remaining ≠ [])
  | unpaidClosing (unpaid : (execution model domain original reference worker quote allocation rival point).closingPaid ≠ true)
  | noGlobal (missing : (execution model domain original reference worker quote allocation rival point).cached = none)
  | globalRemaining (work : GlobalCache model domain original reference worker quote allocation)
      (present : (execution model domain original reference worker quote allocation rival point).cached = some work) (left : work.todo ≠ [])
  | noQualified (missing : (observed model domain original reference worker receiver quote allocation announcements rival point).cached = none)
  | qualifiedRemaining (work : Cache model domain original reference worker receiver quote allocation announcements)
      (present : (observed model domain original reference worker receiver quote allocation announcements rival point).cached = some work) (left : work.todo ≠ [])

def closing_obstruction
    (absent : finish model domain original reference worker receiver quote allocation announcements point rival send = none) :
    CloseReason model domain original reference worker receiver quote allocation announcements point rival := by
  unfold finish at absent
  split at absent
  · rename_i ready
    split at absent
    · apply CloseReason.noGlobal
      assumption
    · rename_i global globalSeen
      split at absent
      · split at absent
        · apply CloseReason.noQualified
          assumption
        · rename_i qualified qualifiedSeen
          split at absent
          · cases absent
          · apply CloseReason.qualifiedRemaining qualified qualifiedSeen
            assumption
      · apply CloseReason.globalRemaining global globalSeen
        assumption
  · rename_i notReady
    by_cases space : (past model original worker quote (globalQuotas allocation)).length ≤ horizon domain
    · by_cases complete : (execution model domain original reference worker quote allocation rival point).remaining = []
      · exact .unpaidClosing (fun paid => notReady ⟨space,complete,paid⟩)
      · exact .pending complete
    · exact .outsideWindow space

theorem a_finished_selection_uses_only_the_original_actual_paid_queues
    (finished : Finished model domain original reference worker receiver quote allocation announcements point rival send) :
    Sparse.replayPayments model domain original reference worker quote (globalQuotas allocation) rival none
      (execution model domain original reference worker quote allocation rival point).payments = some finished.global ∧
    replayPayments model domain original reference worker receiver quote allocation announcements none
      (observed model domain original reference worker receiver quote allocation announcements rival point).payments = some finished.qualified := by
  constructor
  · rw [←Sparse.Scan.the_entire_cache_replays_only_its_own_ordered_actual_paid_slots]
    exact finished.global_present
  · rw [←(observed model domain original reference worker receiver quote allocation announcements rival point).replayed]
    exact finished.qualified_present

theorem a_finished_absence_rejects_every_original_eligible_global_choice
    (finished : Finished model domain original reference worker receiver quote allocation announcements point rival send)
    (member : point.point ∈ domain) (absent : finished.choice = none)
    (choice : Choice model domain original reference worker quote (globalQuotas allocation)) :
    eligible model domain original reference worker receiver quote (globalQuotas allocation) announcements point send choice.policy ≠ true := by
  apply absence_rejects_every_original_eligible_global_choice model domain original reference worker receiver quote (globalQuotas allocation)
    announcements point send finished.room finished.global finished.global_complete finished.qualified
    finished.qualified_complete member
  exact finished.generated.symm.trans absent

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
