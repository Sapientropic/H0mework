import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend

open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication

/-- The smallest source task still pays the opening and has a strict saving. -/
theorem smallest_task_has_one_actual_unit_of_dividend :
    dividend 0 = 1 ∧ extraDebit 0 true false false = 1 ∧ extraDebit 0 false false false = 0 := by
  rw [(exact_strict_dividend_and_actual_payment 0).1, complete_extra_debits, complete_extra_debits]
  norm_num

/-- An explicit current-stock override takes priority over the public label. -/
theorem no_spare_stock_means_no_reinvestment (n : Nat) :
    dispatch n true ((state 1 0 0 true).retime 2 2) = [] ∧
      dispatch n true ((state 0 0 0 true).retime 2 2) = [] := by
  norm_num [dispatch, reinvest, maintenanceBudget, RawCurrent.retime, state]

/-- Raw legality alone does not enforce the comparison's retained reserve. -/
theorem one_more_legal_payment_would_break_the_retained_floor (n : Nat) (shared : Bool) :
    (law n).Valid (currentAt n shared 3) maintain ∧
      ((law n).step (currentAt n shared 3) maintain).stock false false = 0 := by
  have valid : (law n).Valid (currentAt n shared 3) maintain := by
    rw [reinvested_current, (law n).valid_retime (time_independent n)]
    norm_num [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
      RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
      NonnegativeBundle, flowAt, amount, locate, law, state, maintain]
  refine ⟨valid, ?_⟩
  rw [RawLaw.step, if_pos valid, reinvested_current]
  norm_num [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, maintain, state,
    RawCurrent.retime, flowAt, amount, locate]

theorem delivered_but_unused_copies_do_not_meet_the_original_task :
    ¬ ServiceAdequate (law 2) (currentAt 2 true 1) (task 2)
      [openAccess, produce, deliver 2, maintain] := by
  rw [first_current]
  decide +kernel

theorem missing_original_maintenance_does_not_meet_the_original_task :
    ¬ ServiceAdequate (law 2) (currentAt 2 true 1) (task 2)
      [openAccess, produce, deliver 2, consume 2] := by
  rw [first_current]
  decide +kernel

theorem a_second_count_of_the_same_saving_is_not_paid (n : Nat) :
    extraDebit n true false false - extraDebit n false false false ≠ dividend n + dividend n := by
  have facts := exact_strict_dividend_and_actual_payment n
  rw [facts.2.2.1]
  linarith [facts.2.1]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend
