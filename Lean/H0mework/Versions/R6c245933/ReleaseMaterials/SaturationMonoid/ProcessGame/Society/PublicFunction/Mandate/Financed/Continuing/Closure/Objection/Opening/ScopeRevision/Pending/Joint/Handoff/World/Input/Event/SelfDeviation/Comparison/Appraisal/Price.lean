import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Appraisal

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Appraisal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Future.Expiry.Progress
noncomputable section

def parties : List Bool := [false,true]
def methods : List Input.Method := [.direct,.productive,.supplied,.financed]

/-- Local declared values in one numeraire. None receives an Observation,
branch label or financial row. Rates declare values, not currency conversion. -/
structure Prices (unit : Good) where
  rate : Good → ℚ
  normalized : rate unit = 1
  nonnegative : ∀ good, 0 ≤ rate good
  slot : (origin : Responsibility.Origin) → ObligationSlot origin.V → Bool → ℚ
  event : (origin : Responsibility.Origin) → LifecycleEvent origin.V → Bool → ℚ
  time : Bool → ℚ
  time_nonnegative : ∀ actor, 0 ≤ time actor
  holder : Bool → Bool → ℚ
  offer : Bool → Bool → ℚ
  standing : Bool → Bool → ℚ
  eligible : Input.Intent → Bool → ℚ
  method : Input.Intent → Bool → Input.Method → Bool → ℚ
  exitMaterial : Bool → ℚ
  paid : Bool → ℚ
  version : Bool → ℚ
  last : Option (Command Bool) → Bool → ℚ

variable {unit : Good} (price : Prices unit) {first : Packet} (observed : Observation first) (actor : Bool)

def nativeSlots := ((slots observed).map fun item => price.slot item.origin item.value actor).sum
def nativeEvents := ((events observed).map fun item => price.event item.origin item.value actor).sum

def agencyScore (state : Agency) :=
  ((parties.map fun party =>
    (if state.technology.holder = some party then price.holder party actor else 0) +
    (if state.technology.offered = some party then price.offer party actor else 0) +
    (if state.standing party then price.standing party actor else 0)).sum) +
  ((intents.map fun intent =>
    (if state.eligible intent then price.eligible intent actor else 0) +
    ((parties.map fun party => ((methods.map fun method =>
      if method ∈ state.available intent party then price.method intent party method actor else 0).sum)).sum)).sum) +
  (if state.exitMaterial then price.exitMaterial actor else 0) +
  (if state.kind = .paid then price.paid actor else 0) +
  price.version actor * state.technology.version + price.last state.technology.last actor

def agencyValue := agencyScore price actor (agency observed)

def timeCost := price.time actor * observed.elapsed actor

def value := nativeSlots price observed actor + nativeEvents price observed actor +
  agencyValue price observed actor - timeCost price observed actor

def expense := (goods.map fun good => price.rate good * observed.netExpense actor good).sum

def linked := (goods.map fun good => price.rate good *
  Input.Event.Funding.account observed.native true actor good).sum
def remainder := (goods.map fun good => price.rate good *
  Input.Event.Funding.account observed.native false actor good).sum

theorem the_complete_financing_partition_is_counted_once :
    linked price observed actor + remainder price observed actor = expense price observed actor := by
  unfold linked remainder expense
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro good _
  rw [← mul_add,Input.Event.Funding.actual_net_position_change,
    Observation.expense_is_the_actual_net_position_change]
  rfl

theorem expense_is_one_actual_first_to_last_net_change :
    expense price observed actor = (goods.map fun good => price.rate good *
      (FinancialBalance.quotedNet first actor good - observed.quotedNet actor good)).sum := by
  unfold expense
  apply congrArg List.sum
  apply List.map_congr_left
  intro good _
  rw [Observation.expense_is_the_actual_net_position_change]

/-- Complete native histories are valued along their original origin. A shared
past cancels by prefix, not by equating the two complete response histories. -/
def historyValue (origin : Responsibility.Origin) (history : List (LifecycleEvent origin.V)) :=
  (history.map fun event => price.event origin event actor).sum

theorem common_native_history_is_not_recharged
    (origin : Responsibility.Origin) (past left right : List (LifecycleEvent origin.V)) :
    historyValue price actor origin (past ++ left) - historyValue price actor origin (past ++ right) =
      historyValue price actor origin left - historyValue price actor origin right := by
  simp only [historyValue,List.map_append,List.sum_append]
  ring

theorem the_actual_original_history_has_its_own_priced_residual
    (row : Responsibility.Row first) :
    historyValue price actor row.origin (observed.originalRow row).state.history =
      historyValue price actor row.origin row.state.history +
        historyValue price actor row.origin ((observed.originalRow row).state.history.drop row.state.history.length) := by
  obtain ⟨tail,same⟩ := (observed.all_original_rows_and_histories_are_retained row).2.1
  rw [← same]
  unfold historyValue
  dsimp only [Responsibility.Row.origin]
  rw [List.drop_left,List.map_append,List.sum_append]

def payoff : Utility first := fun observed actor => value price observed actor - expense price observed actor

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Appraisal
