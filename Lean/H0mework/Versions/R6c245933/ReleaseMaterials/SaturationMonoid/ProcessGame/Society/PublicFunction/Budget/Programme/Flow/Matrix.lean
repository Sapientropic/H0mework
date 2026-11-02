import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

abbrev Axis := Party × Good

private def snapshot (technology : Technology) : RawCurrent Party Good Technology Instrument :=
  ⟨fun _ _ => 0,fun _ _ _ => 0,technology,0,0⟩

def creditAt (technology : Technology) (request : Request Party Good Port Technology Instrument)
    (axis : Axis (Party := Party) (Good := Good)) : ℚ :=
  flowAt (code.law.credit (snapshot technology) request) axis.1 axis.2

theorem the_technology_reading_is_the_original_material_credit
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (axis : Axis (Party := Party) (Good := Good)) :
    creditAt code current.technology request axis = flowAt (code.law.credit current request) axis.1 axis.2 := by
  cases request.operation <;> rfl

def primitives (menu : List Technology) :=
  (Dynamic.requests code).flatMap fun request => menu.map fun technology => (request,technology)

/-- Physical output per input, generated from the original source recipes. -/
def coefficient (primitive : Request Party Good Port Technology Instrument × Technology)
    (output input : Axis (Party := Party) (Good := Good)) : ℚ :=
  if 0 < Dynamic.Cost.amountAt code primitive.2 primitive.1 input then
    max 0 (creditAt code primitive.2 primitive.1 output / Dynamic.Cost.amountAt code primitive.2 primitive.1 input)
  else 0

def matrix (menu : List Technology) (output input : Axis (Party := Party) (Good := Good)) : ℚ :=
  ((primitives code menu).map fun primitive => coefficient code primitive output input).foldr max 0

theorem the_generated_matrix_is_nonnegative (menu : List Technology)
    (output input : Axis (Party := Party) (Good := Good)) : 0 ≤ matrix code menu output input := by
  unfold matrix
  generalize ((primitives code menu).map fun primitive => coefficient code primitive output input) = values
  induction values with
  | nil => exact le_rfl
  | cons value values ih => exact ih.trans (le_max_right _ _)

def applyMatrix (menu : List Technology) (values : Axis (Party := Party) (Good := Good) → ℚ)
    (output : Axis (Party := Party) (Good := Good)) : ℚ :=
  ((Dynamic.Cost.axes code).map fun input => matrix code menu output input * values input).sum

def sourceCheck (menu : List Technology) : Prop :=
  ∀ request ∈ Dynamic.requests code,∀ technology ∈ menu,∀ output ∈ Dynamic.Cost.axes code,
    creditAt code technology request output ≤
      applyMatrix code menu (Dynamic.Cost.amountAt code technology request) output

instance (menu : List Technology) : Decidable (sourceCheck code menu) := by unfold sourceCheck;infer_instance

theorem matrix_sum (menu : List Technology) {α : Type} (items : List α)
    (values : α → Axis (Party := Party) (Good := Good) → ℚ)
    (output : Axis (Party := Party) (Good := Good)) :
    ((items.map fun item => applyMatrix code menu (values item) output).sum) =
      applyMatrix code menu (fun input => (items.map fun item => values item input).sum) output := by
  induction items with
  | nil => simp [applyMatrix]
  | cons item items ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    simp only [applyMatrix,mul_add,List.sum_map_add]

theorem each_original_execution_respects_the_source_envelope (menu : List Technology)
    (checked : sourceCheck code menu) (item : ExecutionItem Party Good Port Technology Instrument)
    (original : item.request ∈ Dynamic.requests code) (reachable : item.before.technology ∈ menu)
    (output : Axis (Party := Party) (Good := Good)) (inside : output ∈ Dynamic.Cost.axes code) :
    flowAt (code.law.actualCredit item.before item.request) output.1 output.2 ≤
      applyMatrix code menu (fun input => flowAt (code.law.actualDebit item.before item.request) input.1 input.2) output := by
  by_cases legal : code.law.Valid item.before item.request
  · simp only [RawLaw.actualCredit,RawLaw.actualDebit,if_pos legal]
    have bound := checked item.request original item.before.technology reachable output inside
    simpa only [applyMatrix,the_technology_reading_is_the_original_material_credit,
      Dynamic.Cost.the_technology_reading_is_the_original_material_debit] using bound
  · simp only [RawLaw.actualCredit,RawLaw.actualDebit,if_neg legal]
    simp [applyMatrix,flowAt,amount]

theorem each_original_word_respects_the_source_envelope (menu : List Technology)
    (checked : sourceCheck code menu) (items : List (ExecutionItem Party Good Port Technology Instrument))
    (original : ∀ item ∈ items,item.request ∈ Dynamic.requests code)
    (reachable : ∀ item ∈ items,item.before.technology ∈ menu)
    (output : Axis (Party := Party) (Good := Good)) (inside : output ∈ Dynamic.Cost.axes code) :
    code.law.totalCredit items output.1 output.2 ≤ applyMatrix code menu
      (fun input => code.law.totalDebit items input.1 input.2) output := by
  simp only [RawLaw.totalCredit,RawLaw.totalDebit]
  rw [← matrix_sum]
  exact List.sum_le_sum (fun item member => each_original_execution_respects_the_source_envelope
    code menu checked item (original item member) (reachable item member) output inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow
