import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Proposal" => Compile.RawInput Party Good Port Technology Instrument

variable (source : Cut Party Good Port Technology Instrument)
  (policy : Nat → Cut Party Good Port Technology Instrument → Option
    (Compile.RawInput Party Good Port Technology Instrument))
  (read : Cut Party Good Port Technology Instrument → ℚ)
  (proposals : Cut Party Good Port Technology Instrument →
    List (RawEvent Party Good Port Technology Instrument) × List (RawEvent Party Good Port Technology Instrument))

def generatedPressure (index : Nat) : Option ℚ :=
  let cut := Quantities.Execution.endAt source (Quantities.Execution.observedScript policy index source)
  let (war, peace) := proposals cut
  pressure cut read war peace

def generatedPressureMenu : Choice.Menu Nat where
  executable := {index | (generatedPressure source policy read proposals index).isSome }
  score := fun index => ((generatedPressure source policy read proposals index).getD 0 : ℝ)

/-- No terminal history is needed. A first crossing is an original prefix,
and the peak may be attained, approached, unbounded or without a comparison. -/
theorem first_crossing_on_a_generated_history
    (crosses : ∃ index value, generatedPressure source policy read proposals index = some value ∧ 0 < value) :
    ∃ first, Quantities.Recorded source (Quantities.Execution.observedScript policy first source) ∧
      (∃ value, generatedPressure source policy read proposals first = some value ∧ 0 < value) ∧
      ∀ earlier < first, ¬ ∃ value, generatedPressure source policy read proposals earlier = some value ∧ 0 < value := by
  classical
  exact ⟨Nat.find crosses, Quantities.record source _, Nat.find_spec crosses,
    fun _ earlier => Nat.find_min crosses earlier⟩

theorem the_generated_history_peak_resolves :
    (generatedPressureMenu source policy read proposals).Resolution :=
  (generatedPressureMenu source policy read proposals).resolve

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
