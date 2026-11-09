import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Allocate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Tick

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next endAt_append)
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (answers : ReceiptAnswers seed) (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

local notation "Posted" => StateAt seed community (next (endAt seed past) input)
local notation "At" => Position seed past input

def atPosition (position : At) (state : Posted) :=
  allocate (jointOffer answers past input position) (limitAt past input position)
    (fun key receipt issued => (the_original_limit_is_the_selected_quantity answers past input position key receipt issued).le)
    state.stack (Available.full (limitAt_nonnegative past input position))

/-- The write uses the canonical motion of all the original layers. -/
def writePosition (position : At) (state : Posted) : Posted :=
  let plan := atPosition answers past input position state
  let changed := state.stack.balances.any fun row => decide (0 < plan.used row.1.key.2.2)
  state.consumeMotion plan.move changed

theorem writePosition_balances (position : At) (state : Posted) :
    (writePosition answers past input position state).stack.balances =
      (atPosition answers past input position state).after.balances :=
  state.consumeMotion_balances _ _

theorem writePosition_origins (position : At) (state : Posted) :
    (writePosition answers past input position state).stack.balances.map Prod.fst =
      state.stack.balances.map Prod.fst := by
  rw [writePosition_balances]
  exact (atPosition answers past input position state).move.keeps_origins

theorem a_position_consumes_at_most_its_actual_joint_delivery (position : At) (state : Posted) (good : Good) :
    let amount := outstanding good state.stack.balances -
      outstanding good (writePosition answers past input position state).stack.balances
    0 ≤ amount ∧ amount ≤ limitAt past input position good := by
  let plan := atPosition answers past input position state
  have conservation := plan.conservation good
  have tight := plan.tight good
  have cap : ((Available.full (limitAt_nonnegative past input position)).balance good).remaining =
      limitAt past input position good := rfl
  have rest := (plan.left.balance good).nonnegative
  have eligible : 0 ≤ min (limitAt past input position good)
      (demand (jointOffer answers past input position) good state.stack.balances) := by
    rw [← cap, ← tight]
    exact sub_nonneg.mpr (plan.left.within good)
  rw [cap] at conservation tight
  dsimp only
  rw [writePosition_balances]
  change 0 ≤ outstanding good state.stack.balances - outstanding good plan.after.balances ∧
    outstanding good state.stack.balances - outstanding good plan.after.balances ≤ _
  constructor <;> linarith only [conservation, tight, rest, eligible]

def writePositions : List At → Posted → Posted
  | [], state => state
  | position :: rest, state =>
    writePositions rest (writePosition answers past input position state)

theorem writePositions_origins (positions : List At) (state : Posted) :
    (writePositions answers past input positions state).stack.balances.map Prod.fst =
      state.stack.balances.map Prod.fst := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
    rw [writePositions, ih, writePosition_origins]

theorem writePositions_bound (positions : List At) (state : Posted) (good : Good) :
    let amount := outstanding good state.stack.balances -
      outstanding good (writePositions answers past input positions state).stack.balances
    0 ≤ amount ∧ amount ≤ (positions.map (fun position => limitAt past input position good)).sum := by
  induction positions generalizing state with
  | nil => simp [writePositions]
  | cons position rest ih =>
    have head := a_position_consumes_at_most_its_actual_joint_delivery answers past input position state good
    have tail := ih (writePosition answers past input position state)
    dsimp only at head tail ⊢
    simp only [writePositions, List.map_cons, List.sum_cons]
    constructor <;> linarith only [head.1, head.2, tail.1, tail.2]

variable {past input}

/-- Post the original physical and native effects, then consume each
original item once on the actual successor's old liability layers. -/
def writeTick (state : State seed community past) (input : Reparation.Actual.Input Party Good Port Technology Instrument) :
    State seed community (past ++ [input]) :=
  (writePositions answers past input (itemPositions past input) (posted state input)).rebase
    (endAt_append seed past [input]).symm

theorem writeTick_balances (state : State seed community past) :
    (writeTick answers state input).stack.balances =
      (writePositions answers past input (itemPositions past input) (posted state input)).stack.balances :=
  StateAt.rebase_balances (cut := next (endAt seed past) input) _ _

theorem writeTick_origins (state : State seed community past) :
    (writeTick answers state input).stack.balances.map Prod.fst =
      state.stack.balances.map Prod.fst ++ openings seed community past input := by
  rw [writeTick_balances, writePositions_origins, posted_balances, List.map_append, List.map_map]
  rw [show (Prod.fst ∘ fun origin => (origin, opening origin)) = id from rfl, List.map_id]

theorem the_joint_tick_carries_its_original_whole_write_and_budget (state : State seed community past) (good : Good) :
    let positions := itemPositions (seed := seed) past input
    let before := outstanding good (posted state input).stack.balances
    let after := outstanding good (writeTick answers state input).stack.balances
    Quantities.Recorded (endAt seed past) [input] ∧ positions.Nodup ∧
      0 ≤ before - after ∧ before - after ≤ (positions.map (fun position => limitAt past input position good)).sum := by
  refine ⟨Quantities.record _ _, (Reparation.Actual.Allocation.each_input_visits_every_original_position_once (seed := seed) past input).1, ?_⟩
  rw [writeTick_balances]
  exact writePositions_bound answers past input _ (posted state input) good

#print axioms the_joint_tick_carries_its_original_whole_write_and_budget

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
