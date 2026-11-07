import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Raw.Invariant

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

variable (current : Actual.Current (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))

theorem each_compiled_result_preserves_the_obstruction
    (raw : Compile.RawInput Bool Bool Unit Nat Unit) (result : Physical.Public.ResultAt input current raw)
    (prior : Obstruction current.raw)
    (notProduction : ∀ item ∈ result.execution.items,item.request.operation ≠ .produce false) :
    Obstruction result.next.raw := by
  cases result with
  | accepted word selected checked =>
      have inherited := the_original_execution_cannot_remove_the_obstruction_without_production current.raw 0 word prior notProduction
      cases raw <;> exact inherited
  | refused => exact prior
  | metadata => exact prior

theorem no_actual_programme_removes_original_debt_without_production
    (code : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))
    (prior : Obstruction current.raw)
    (notProduction : ∀ item ∈ Programme.items input current code,item.request.operation ≠ .produce false) :
    Obstruction (Programme.run input current code).raw := by
  induction code generalizing current with
  | nil => exact prior
  | cons raw tail inherited =>
      have first := each_compiled_result_preserves_the_obstruction current raw (Physical.Public.compile input current raw) prior
        (fun item listed => notProduction item (List.mem_append_left _ listed))
      exact inherited (Physical.Public.compile input current raw).next first
        (fun item listed => notProduction item (List.mem_append_right _ listed))

theorem every_actual_programme_inventory_item_is_accepted
    (code : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))
    (item : ExecutionItem Bool Bool Unit Nat Unit) (listed : item ∈ Programme.items input current code) :
    law.Valid item.before item.request := by
  induction code generalizing current with
  | nil => cases listed
  | cons raw tail inherited =>
      rcases List.mem_append.mp listed with first | later
      · cases result : Physical.Public.compile input current raw with
        | accepted word selected checked =>
            rw [result] at first
            exact checked item first
        | refused word selected original member failed => rw [result] at first; cases first
        | metadata selected => rw [result] at first; cases first
      · exact inherited (Physical.Public.compile input current raw).next later

def RawCleared (code : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit)) : Prop :=
  ∀ debtor holder,(Programme.run input before code).raw.claims () debtor holder = 0

theorem every_complete_original_debt_clearing_contains_an_actual_productive_item
    (code : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))
    (cleared : RawCleared code) :
    ∃ item ∈ Programme.items input before code,item.request.operation = .produce false := by
  by_contra absent
  have notProduction : ∀ item ∈ Programme.items input before code,item.request.operation ≠ .produce false := by
    intro item member same
    exact absent ⟨item,member,same⟩
  have preserved := no_actual_programme_removes_original_debt_without_production before code
    the_original_cut_has_no_cash_and_retains_its_complete_debt notProduction
  unfold RawCleared at cleared
  have zero : claimTotal (Programme.run input before code).raw = 0 := by simp [claimTotal,cleared]
  have lower := preserved.2.2
  rw [zero] at lower
  norm_num at lower

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
