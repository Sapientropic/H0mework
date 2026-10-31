import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

/-- All entries of the original material flow count, one good at a time.
No roster, price conversion or selected beneficiary filters this sum. -/
def physicalQuantity (flow : Flow Party Good) (good : Good) : ℚ :=
  (flow.map fun entry => if entry.1.2 = good then entry.2 else 0).sum

omit [DecidableEq Party] in
theorem quantity_at_any_bearer (party : Party) (bundle : Bundle Good) (good : Good) :
    physicalQuantity (locate party bundle) good = amount Good bundle good := by
  simp only [physicalQuantity, locate, List.map_map, Function.comp_def, amount]

def stepOutput (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) : ℚ :=
  match item.request.operation with
  | .produce _ => physicalQuantity (law.actualCredit item.before item.request) good
  | _ => 0

def stepCost (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) : ℚ :=
  match item.request.operation with
  | .produce _ | .use .. | .revise .. =>
      physicalQuantity (law.actualDebit item.before item.request) good
  | _ => 0

def stepNet (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) : ℚ :=
  physicalQuantity (law.actualCredit item.before item.request) good -
    physicalQuantity (law.actualDebit item.before item.request) good

theorem each_real_step_separates_production_cost_and_internal_transfers
    (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (good : Good) :
    stepNet law item good = stepOutput law item good - stepCost law item good := by
  by_cases accepted : law.Valid item.before item.request
  · cases operation : item.request.operation <;>
      simp [stepNet, stepOutput, stepCost, operation, RawLaw.actualCredit,
        RawLaw.actualDebit, accepted, RawLaw.credit, RawLaw.debit,
        physicalQuantity, locate, List.map_map, Function.comp_def]
  · cases operation : item.request.operation <;>
      simp [stepNet, stepOutput, stepCost, operation, RawLaw.actualCredit,
        RawLaw.actualDebit, accepted, physicalQuantity]

def output (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) : ℚ :=
  (items.map fun item => stepOutput law item good).sum

def cost (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) : ℚ :=
  (items.map fun item => stepCost law item good).sum

def net (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) : ℚ :=
  (items.map fun item => stepNet law item good).sum

theorem the_complete_original_inventory_counts_every_real_cost
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) :
    net law items good = output law items good - cost law items good := by
  induction items with
  | nil => simp [net, output, cost]
  | cons item items ih =>
      simp only [net, output, cost, List.map_cons, List.sum_cons] at ih ⊢
      rw [each_real_step_separates_production_cost_and_internal_transfers, ih]
      ring

theorem cancelling_a_rent_transfer_is_not_a_productivity_gain
    (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (sender recipient : Party)
    (bundle : Bundle Good) (kind : item.request.operation = .transfer sender recipient bundle)
    (good : Good) : stepNet law item good = 0 := by
  rw [each_real_step_separates_production_cost_and_internal_transfers]
  simp [stepOutput, stepCost, kind]

/-- The two inventories must be supplied by their own actual source
executions; this arithmetic does not identify their occurrences. -/
def controlLoss (controlledLaw openLaw : RawLaw Party Good Port Technology Instrument)
    (controlled openItems : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) : ℚ :=
  net openLaw openItems good - net controlledLaw controlled good

theorem control_loss_is_foregone_output_after_all_additional_costs
    (controlledLaw openLaw : RawLaw Party Good Port Technology Instrument)
    (controlled openItems : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good) :
    controlLoss controlledLaw openLaw controlled openItems good =
      (output openLaw openItems good - output controlledLaw controlled good) -
        (cost openLaw openItems good - cost controlledLaw controlled good) := by
  unfold controlLoss
  rw [the_complete_original_inventory_counts_every_real_cost,
    the_complete_original_inventory_counts_every_real_cost]
  ring

theorem genuine_extra_output_pays_every_extra_cost_before_a_strict_gain
    (controlledLaw openLaw : RawLaw Party Good Port Technology Instrument)
    (controlled openItems : List (ExecutionItem Party Good Port Technology Instrument)) (good : Good)
    (paid : cost openLaw openItems good - cost controlledLaw controlled good <
      output openLaw openItems good - output controlledLaw controlled good) :
    0 < controlLoss controlledLaw openLaw controlled openItems good := by
  rw [control_loss_is_foregone_output_after_all_additional_costs]
  linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control
