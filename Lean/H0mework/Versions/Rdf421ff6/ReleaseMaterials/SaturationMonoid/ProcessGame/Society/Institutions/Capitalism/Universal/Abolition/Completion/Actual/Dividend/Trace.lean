import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

local notation "C" => Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "R" => Compile.RawInput Party Good Port Technology Instrument

def traceItems (before : C) : List R → List (ExecutionItem Party Good Port Technology Instrument)
  | [] => []
  | raw :: later =>
      (Physical.Public.compile input before raw).execution.items ++
        traceItems (Physical.Public.compile input before raw).next later

def traceCells (before : C) : List R → List (Party × Good)
  | [] => []
  | raw :: later =>
      stepCells input before (Physical.Public.compile input before raw) ++
        traceCells (Physical.Public.compile input before raw).next later

def traceNet (before : C) : List R → Party → Good → ℚ
  | [], _, _ => 0
  | raw :: later, person, good =>
      stepNet input before (Physical.Public.compile input before raw) person good +
        traceNet (Physical.Public.compile input before raw).next later person good

theorem actual_prefix_stock_is_exactly_its_complete_net_flow
    (before : C) (past : List R) (person : Party) (good : Good) :
    (past.foldl (fun current raw => (Physical.Public.compile input current raw).next) before).raw.stock person good =
      before.raw.stock person good + traceNet input before past person good := by
  induction past generalizing before with
  | nil => simp only [List.foldl_nil, traceNet, add_zero]
  | cons raw later inherited =>
    rw [List.foldl_cons, inherited, every_actual_step_includes_both_original_gross_flows]
    exact add_assoc _ _ _

theorem complete_net_flow_counts_each_original_debit_and_credit_once
    (before : C) (past : List R) (person : Party) (good : Good) :
    traceNet input before past person good =
      (Physical.Public.interpreter input).totalCredit (traceItems input before past) person good -
        (Physical.Public.interpreter input).totalDebit (traceItems input before past) person good := by
  induction past generalizing before with
  | nil => simp only [traceNet, traceItems, RawLaw.totalCredit, RawLaw.totalDebit,
      List.map_nil, List.sum_nil, sub_self]
  | cons raw later inherited =>
    simp only [traceNet, traceItems, stepNet, RawLaw.totalCredit, RawLaw.totalDebit,
      List.map_append, List.sum_append] at *
    rw [inherited]
    ring

theorem no_prefix_effect_is_outside_the_actual_affected_cells
    (before : C) (past : List R) (person : Party) (good : Good)
    (absent : (person, good) ∉ traceCells input before past) :
    traceNet input before past person good = 0 := by
  induction past generalizing before with
  | nil => rfl
  | cons raw later inherited =>
    have head : (person, good) ∉ stepCells input before (Physical.Public.compile input before raw) :=
      fun present => absent (List.mem_append_left _ present)
    have tail : (person, good) ∉ traceCells input (Physical.Public.compile input before raw).next later :=
      fun present => absent (List.mem_append_right _ present)
    rw [traceNet, no_actual_step_cost_is_outside_its_original_effect_support input before _ person good head,
      inherited _ tail, add_zero]

#print axioms actual_prefix_stock_is_exactly_its_complete_net_flow
#print axioms complete_net_flow_counts_each_original_debit_and_credit_once
#print axioms no_prefix_effect_is_outside_the_actual_affected_cells

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend
