import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Holding

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Trace)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

theorem paid_trace_realizes_forecastHolding (source : C) (past : Script) (word : Word)
    (paid : Trace (Execution.endAt source past) word
      (Execution.endAt (Execution.endAt source past) (Execution.primitiveScript word)))
    (key : Party × Good) :
    forecastHolding source past word key = holding source (past ++ Execution.primitiveScript word) key := by
  unfold forecastHolding holding
  apply congrArg List.sum
  apply List.map_congr_left
  intro row _
  unfold forecastUnpaid unpaid
  rw [paid_trace_adds_exactly_the_forecast_use source past word paid]

theorem original_floor_is_paid_iff_supported_forecast_zero (source : C) (past : Script) (word : Word)
    (paid : Trace (Execution.endAt source past) word
      (Execution.endAt (Execution.endAt source past) (Execution.primitiveScript word))) :
    (∀ key ∈ holdingAddresses source, forecastHolding source past word key = 0) ↔
      Demand.Covers source (past ++ Execution.primitiveScript word) := by
  rw [← original_floor_holding_vanishes_exactly_after_actual_payment]
  constructor
  · intro zero key
    rw [← paid_trace_realizes_forecastHolding source past word paid]
    by_cases named : key ∈ holdingAddresses source
    · exact zero key named
    · exact forecastHolding_zero_off_support source past word key named
  · intro zero key _
    rw [paid_trace_realizes_forecastHolding source past word paid]
    exact zero key

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor
