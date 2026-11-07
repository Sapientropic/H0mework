import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Coverage
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Trace)
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

theorem a_paid_primitive_trace_keeps_the_actual_clock {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (paid : Trace source word target) :
    target.raw.clock = source.raw.clock := by
  rw [paid.raw_is_the_complete_original_execution 0]
  exact (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
    (Physical.Public.interpreter source.native.input) source.raw 0 word).1

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
