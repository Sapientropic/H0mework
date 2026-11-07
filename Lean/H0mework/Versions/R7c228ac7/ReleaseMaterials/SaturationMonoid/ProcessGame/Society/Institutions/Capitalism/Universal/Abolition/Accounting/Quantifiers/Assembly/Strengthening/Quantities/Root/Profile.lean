import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Joint
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Linear

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def elapsed (source : C) (script : Script) : ℚ :=
  (Execution.endAt source script).raw.clock - source.raw.clock

theorem elapsed_is_original_clock_cost (source : C) (script : Script) :
    Optimality.Programme.clockCost source.native.input (Evolving.Epoch.Source.originalState source.native)
      (Execution.programme source script) = elapsed source script := by
  unfold Optimality.Programme.clockCost elapsed
  rw [Execution.physical_is_the_folded_actual_end]
  rfl

def suffixCost (source : C) (reading : Optimality.Cost.LinearReadout Party Good)
    (script : Script) : EReal :=
  ((Optimality.Cost.value reading source.native.input (Evolving.Epoch.Source.originalState source.native)
    (Execution.programme source script) : ℝ) : EReal)

theorem suffix_cost_is_the_same_native_material_and_clock
    (source : C) (reading : Optimality.Cost.LinearReadout Party Good) (script : Script) :
    suffixCost source reading script = ((((Execution.inventory source script).map
      (Optimality.Cost.itemValue reading source.native.handlerFace.rootRead)).sum +
        reading.timeWeight * elapsed source script : ℚ) : ℝ) := by
  unfold suffixCost Optimality.Cost.value
  rw [Execution.material_is_the_folded_actual_inventory, elapsed_is_original_clock_cost]
  rfl

theorem full_suffix_cost_has_a_finite_tight_lower_bound_when_feasible
    (source : C) (reading : Optimality.Cost.LinearReadout Party Good)
    (script : Script) (paid : Feasible source script) :
    (0 : EReal) ≤ Bounds.lower source (suffixCost source reading) ∧
      Bounds.lower source (suffixCost source reading) < ⊤ := by
  constructor
  · apply (Bounds.lower_is_tight source _).2
    rintro value ⟨candidate, _, rfl⟩
    exact EReal.coe_nonneg.mpr (Rat.cast_nonneg.mpr (Optimality.Cost.value_nonnegative reading
      source.native.input (Evolving.Epoch.Source.originalState source.native)
      (Execution.programme source candidate)))
  · exact (Bounds.lower_le source _ script paid).trans_lt (EReal.coe_lt_top _)

/-- Cost and loss coordinates share the same execution, with original row
and stock addresses. A fall in retained stock is a positive stock draw. -/
inductive CostAddress (source : C)
  | elapsed
  | resource (channel : Optimality.Cost.Channel) (bearer : Party) (good : Good)
  | stockDraw (bearer : Party) (good : Good)
  | outstandingClaim (instrument : Instrument) (debtor holder : Party)
  | remainingProgress (row : Execution.RowAt source)

def costProfile (source : C) (script : Script) : CostAddress source → EReal
  | .elapsed => ((elapsed source script : ℝ) : EReal)
  | .resource channel bearer good =>
      ((Optimality.Cost.resource source.native.input (Evolving.Epoch.Source.originalState source.native)
        (Execution.programme source script) channel bearer good : ℝ) : EReal)
  | .stockDraw bearer good =>
      (((source.raw.stock bearer good - (Execution.endAt source script).raw.stock bearer good : ℚ) : ℝ) : EReal)
  | .outstandingClaim instrument debtor holder =>
      (((Execution.endAt source script).raw.claims instrument debtor holder : ℝ) : EReal)
  | .remainingProgress row =>
      (((Execution.rowAt source script row).progressBudget : ℝ) : EReal)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities
