import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.Support

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  {raw : Compile.RawInput Party Good Port Technology Instrument}

def stepCells (result : Physical.Public.ResultAt input before raw) : List (Party × Good) :=
  result.execution.items.flatMap fun item =>
    ((Physical.Public.interpreter input).actualDebit item.before item.request).map Prod.fst ++
      ((Physical.Public.interpreter input).actualCredit item.before item.request).map Prod.fst

def stepNet (result : Physical.Public.ResultAt input before raw) (person : Party) (good : Good) : ℚ :=
  (Physical.Public.interpreter input).totalCredit result.execution.items person good -
    (Physical.Public.interpreter input).totalDebit result.execution.items person good

theorem every_actual_step_includes_both_original_gross_flows
    (result : Physical.Public.ResultAt input before raw) (person : Party) (good : Good) :
    result.next.raw.stock person good = before.raw.stock person good + stepNet input before result person good := by
  cases result with
  | accepted word selected checked =>
    cases raw <;>
      exact Material.Continuation.Balance.exact_stock_after_original_effects
        (Physical.Public.interpreter input) before.raw word person good
  | refused word selected item listed failed =>
    simp only [Physical.Public.ResultAt.next, stepNet, Physical.Public.ResultAt.execution,
      RawLaw.totalCredit, RawLaw.totalDebit, List.map_nil, List.sum_nil, sub_self, add_zero]
  | metadata selected =>
    simp only [Physical.Public.ResultAt.next, stepNet, Physical.Public.ResultAt.execution,
      RawLaw.totalCredit, RawLaw.totalDebit, List.map_nil, List.sum_nil, sub_self, add_zero]

theorem no_actual_step_cost_is_outside_its_original_effect_support
    (result : Physical.Public.ResultAt input before raw) (person : Party) (good : Good)
    (absent : (person, good) ∉ stepCells input before result) :
    stepNet input before result person good = 0 := by
  cases result with
  | accepted word selected checked =>
    have support : (person, good) ∉ Material.Continuation.Balance.cells
        (Physical.Public.interpreter input) before.raw word := absent
    obtain ⟨debit, credit⟩ := Material.Continuation.Balance.no_effect_outside_original_support
      (Physical.Public.interpreter input) before.raw word person good support
    exact sub_eq_zero.mpr (credit.trans debit.symm)
  | refused word selected item listed failed =>
    simp only [stepNet, Physical.Public.ResultAt.execution, RawLaw.totalCredit, RawLaw.totalDebit,
      List.map_nil, List.sum_nil, sub_self]
  | metadata selected =>
    simp only [stepNet, Physical.Public.ResultAt.execution, RawLaw.totalCredit, RawLaw.totalDebit,
      List.map_nil, List.sum_nil, sub_self]

#print axioms every_actual_step_includes_both_original_gross_flows
#print axioms no_actual_step_cost_is_outside_its_original_effect_support

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend
