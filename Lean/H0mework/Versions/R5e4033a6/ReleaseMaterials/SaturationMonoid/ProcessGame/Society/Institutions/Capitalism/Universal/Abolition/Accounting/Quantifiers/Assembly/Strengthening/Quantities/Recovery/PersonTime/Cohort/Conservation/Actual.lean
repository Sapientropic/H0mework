import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation.Stock
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [Fintype Party] [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

omit [DecidableEq Port] in
private theorem programme_stock_cannot_increase (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (code : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (good : Good) (noOutput : ∀ tech person,
      amount Good ((Physical.Public.interpreter input).technique tech person).outputs good = 0) :
    stock (Optimality.Programme.run input before code).raw good ≤ stock before.raw good := by
  induction code generalizing before with
  | nil => exact le_rfl
  | cons proposal later ih =>
    let compiled := Physical.Public.compile input before proposal
    have consumed : stock compiled.next.raw good ≤ stock before.raw good := by
      unfold compiled
      cases Physical.Public.compile input before proposal with
      | accepted word selected checked =>
        cases proposal <;> exact stock_cannot_increase_in_an_original_word_without_output
          (Physical.Public.interpreter input) before.raw word 0 good noOutput
      | refused => exact le_rfl
      | metadata => exact le_rfl
    exact (ih compiled.next).trans consumed

/-- The bound applies to every actual successor word of the same root,
including transfers, claim payments and changes of technology. -/
theorem unproduced_original_stock_never_increases_in_any_continuation
    (origin : C) (good : Good)
    (noOutput : ∀ tech person,
      amount Good ((Physical.Public.interpreter origin.native.input).technique tech person).outputs good = 0)
    (repair : Script) :
    stock (Execution.endAt origin repair).raw good ≤ stock origin.raw good := by
  have physical := programme_stock_cannot_increase origin.native.input (Execution.programme origin repair)
    (Evolving.Epoch.Source.originalState origin.native) good noOutput
  rw [Execution.physical_is_the_folded_actual_end] at physical
  exact physical

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation
