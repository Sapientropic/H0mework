import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Reading

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (code : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem all_programmes_have_nonnegative_real_resource_costs
    (channel : Channel) (party : Party) (good : Good) : 0 ≤ resource input before code channel party good := by
  unfold resource
  induction Programme.items input before code with
  | nil => exact le_refl _
  | cons item rest prior =>
      exact add_nonneg (actualPart_nonnegative (Physical.Public.interpreter input) item.before item.request channel party good) prior

theorem every_original_transfer_leg_is_nonnegative
    (kind : Movement) (party : Party) (good : Good) : 0 ≤ cashOut input before code kind party good := by
  unfold cashOut
  induction Programme.items input before code with
  | nil => exact le_refl _
  | cons item rest prior =>
      apply add_nonneg _ prior
      unfold movingDebit
      dsimp only
      split
      · exact PublicFunction.Costs.actual_debit_nonnegative (Physical.Public.interpreter input) item party good
      · simp [flowAt,amount]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
