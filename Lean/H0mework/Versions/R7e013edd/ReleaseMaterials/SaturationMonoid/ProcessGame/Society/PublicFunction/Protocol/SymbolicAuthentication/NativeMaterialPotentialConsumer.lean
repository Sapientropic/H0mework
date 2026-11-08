import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter)
open NativeMaterialPotentialSource
variable (code : Emitter) (same : code.law = law)

def cost (row : StageTrace.Record (code := code)) : ℚ := spent (StageTrace.items row)
def bill (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) : ℚ :=
  ((StageTrace.records cursor stages).map (cost code)).sum
def charged (rows : List (StageTrace.Record (code := code))) : Nat :=
  (rows.filter fun row => decide (2 ≤ cost code row)).length
def capacity (cursor : Cursor code) : Nat := ⌊potential (EventStep.seed cursor).current / 2⌋₊

theorem every_charged_stage_is_paid_from_the_actual_bill (rows : List (StageTrace.Record (code := code))) :
    2 * (charged code rows : ℚ) ≤ (rows.map (cost code)).sum := by
  induction rows with
  | nil => simp [charged]
  | cons row tail ih =>
    have nonnegative := spent_is_nonnegative (StageTrace.items row)
    change 0 ≤ cost code row at nonnegative
    by_cases paid : 2 ≤ cost code row
    · simpa only [charged,List.filter_cons,decide_eq_true_eq,if_pos paid,List.length_cons,Nat.cast_add,Nat.cast_one,
        List.map_cons,List.sum_cons] using (show 2 * ((charged code tail : ℚ) + 1) ≤
          cost code row + (tail.map (cost code)).sum by linarith)
    · simpa only [charged,List.filter_cons,decide_eq_true_eq,if_neg paid,List.map_cons,List.sum_cons] using
        (show 2 * (charged code tail : ℚ) ≤ cost code row + (tail.map (cost code)).sum by linarith)

include same
theorem every_actual_stage_retains_its_exact_original_material_balance
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) :
    potential (EventStep.seed (cursor.after protocol rival)).current +
      cost code (StageTrace.material cursor protocol rival) = potential (EventStep.seed cursor).current := by
  rw [← (StageTrace.material_is_the_actual_step cursor protocol rival).1]
  change potential (code.law.next (EventStep.seed cursor).current
      (StageTrace.material cursor protocol rival).submitted) +
    spent (code.law.rawItems (EventStep.seed cursor).current (StageTrace.material cursor protocol rival).submitted) = _
  rw [same]
  exact every_original_word_generates_its_complete_material_account _ 0 _

theorem arbitrary_actual_continuations_have_one_telescoping_material_account
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    potential (EventStep.seed (EventHistory.execute cursor stages)).current + bill code cursor stages =
      potential (EventStep.seed cursor).current := by
  induction stages generalizing cursor with
  | nil => simp [bill,StageTrace.records,EventHistory.execute]
  | cons stage tail ih =>
    have first := every_actual_stage_retains_its_exact_original_material_balance code same cursor stage.1 stage.2
    have later := ih (cursor.after stage.1 stage.2)
    simp only [EventHistory.execute,bill,StageTrace.records,List.map_cons,List.sum_cons]
    simp only [bill] at later
    linarith

theorem every_actual_next_preserves_nonnegative_stock
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (stocks : ∀ party good, 0 ≤ (EventStep.seed cursor).current.stock party good) :
    ∀ party good, 0 ≤ (EventStep.seed (cursor.after protocol rival)).current.stock party good := by
  rw [← (StageTrace.material_is_the_actual_step cursor protocol rival).1]
  change ∀ party good, 0 ≤ (code.law.next (EventStep.seed cursor).current
    (StageTrace.material cursor protocol rival).submitted).stock party good
  rw [same]
  exact execute_stocks_are_nonnegative _ 0 _ stocks

theorem arbitrary_continuations_preserve_nonnegative_stock
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (stocks : ∀ party good, 0 ≤ (EventStep.seed cursor).current.stock party good) :
    ∀ party good, 0 ≤ (EventStep.seed (EventHistory.execute cursor stages)).current.stock party good := by
  induction stages generalizing cursor with
  | nil => exact stocks
  | cons stage tail ih =>
    exact ih (cursor.after stage.1 stage.2)
      (every_actual_next_preserves_nonnegative_stock code same cursor stage.1 stage.2 stocks)

theorem the_actual_initial_inventory_funds_all_continuation_spending
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (stocks : ∀ party good, 0 ≤ (EventStep.seed cursor).current.stock party good) :
    bill code cursor stages ≤ potential (EventStep.seed cursor).current := by
  have balance := arbitrary_actual_continuations_have_one_telescoping_material_account code same cursor stages
  have remaining := nonnegative_potential _
    (arbitrary_continuations_preserve_nonnegative_stock code same cursor stages stocks)
  linarith

theorem original_stocks_generate_a_uniform_paid_stage_budget
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (stocks : ∀ party good, 0 ≤ (EventStep.seed cursor).current.stock party good) :
    charged code (StageTrace.records cursor stages) ≤ capacity code cursor := by
  have actual := every_charged_stage_is_paid_from_the_actual_bill code (StageTrace.records cursor stages)
  have funded := the_actual_initial_inventory_funds_all_continuation_spending code same cursor stages stocks
  apply Nat.le_floor
  change (charged code (StageTrace.records cursor stages) : ℚ) ≤ potential (EventStep.seed cursor).current / 2
  dsimp only [bill] at funded
  linarith
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialConsumer
