import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Positivity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- A fixed observer of complete actual resource incidence. It is neither
a market price oracle nor production/admission authority. -/
structure LinearReadout (Party Good : Type) where
  resourceWeight : Channel → Party → Good → ℚ
  resource_nonnegative : ∀ channel party good, 0 ≤ resourceWeight channel party good
  timeWeight : ℚ
  time_nonnegative : 0 ≤ timeWeight

variable (reading : LinearReadout Party Good)

def weightedFlow (channel : Channel) (flow : Flow Party Good) : ℚ :=
  (flow.map (fun entry => reading.resourceWeight channel entry.1.1 entry.1.2 * entry.2)).sum

def itemValue (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) : ℚ :=
  (channels.map (fun channel => weightedFlow reading channel (actualPart law item.before item.request channel))).sum

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (code : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Actual finite flow support supplies every bearer/good; no supplied
finite census truncates the comparison domain. -/
def value : ℚ :=
  ((Programme.items input before code).map (itemValue reading (Physical.Public.interpreter input))).sum +
    reading.timeWeight * Programme.clockCost input before code

theorem value_nonnegative : 0 ≤ value reading input before code := by
  apply add_nonneg _ (mul_nonneg reading.time_nonnegative (Programme.clockCost_nonnegative input before code))
  apply List.sum_nonneg
  intro amount member
  obtain ⟨item,listed,rfl⟩ := List.mem_map.mp member
  unfold itemValue
  apply List.sum_nonneg
  intro amount member
  obtain ⟨channel,listed,rfl⟩ := List.mem_map.mp member
  unfold weightedFlow
  apply List.sum_nonneg
  intro amount member
  obtain ⟨entry,listed,rfl⟩ := List.mem_map.mp member
  exact mul_nonneg (reading.resource_nonnegative channel entry.1.1 entry.1.2)
    (actualPart_is_the_original_nonnegative_flow (Physical.Public.interpreter input) item.before item.request channel entry listed)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
