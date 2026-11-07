import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program Innovation
open Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

noncomputable section

attribute [local irreducible] Execution.Selected.items Joint.Planning.selected Joint.Planning.actualNext Joint.Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

theorem the_open_source_keeps_the_exact_original_native_endpoint :
    (Evolution.Sparse.Current.support seed.claim (futureSource seed claim)).1 =
      Runtime.support seed claim (Runtime.visitAt seed claim (Execution.Selected.items seed claim).length).current :=
  Continuation.nextSparse_base_support seed claim _

variable {target : Evolution.Sparse.Current (oldN := Continuation.base seed claim) seed.claim}

theorem every_open_mechanism_history_keeps_the_whole_actual_native_background
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target) :
    (Evolution.Sparse.Current.support seed.claim target).1 =
      Runtime.support seed claim (Runtime.visitAt seed claim (Execution.Selected.items seed claim).length).current :=
  (every_open_history_preserves_the_complete_old_world seed.claim history).trans
    (the_open_source_keeps_the_exact_original_native_endpoint seed claim)

theorem no_open_mechanism_history_replaces_the_original_gross_snapshot
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target) :
    (Evolution.Sparse.Current.support seed.claim target).1.2 =
      some (Joint.Planning.actualNext seed claim (shared seed claim)) := by
  rw [every_open_mechanism_history_keeps_the_whole_actual_native_background seed claim history]
  change some (Runtime.sharedAt seed claim
    (Runtime.visitAt seed claim (Execution.Selected.items seed claim).length).current) = _
  exact congrArg some (Runtime.the_named_final_root_keeps_the_one_executed_material_result seed claim)

theorem every_open_history_retains_the_exact_original_financial_account
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target) :
    (Background.shape seed).AllRead seed.input seed.depth seed.count (Execution.Selected.after seed claim)
      (Evolution.Sparse.Current.support seed.claim target).1.1.1 := by
  rw [every_open_mechanism_history_keeps_the_whole_actual_native_background seed claim history]
  have original := Runtime.all_original_financial_rows_read_this_one_actual_root_account
    seed claim (Execution.Selected.items seed claim).length
  rw [Runtime.the_named_runtime_completes_the_original_financial_consumption_within_its_source_budget] at original
  exact original

theorem every_open_history_keeps_the_actual_paid_gross_responsibility
    (enough : Joint.Planning.Enough seed claim (shared seed claim))
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target) :
    ∃ snapshot : Joint.Current seed claim,
      (Evolution.Sparse.Current.support seed.claim target).1.2 = some snapshot ∧
        Joint.Current.grossPaid seed claim snapshot := by
  refine ⟨Joint.Planning.actualNext seed claim (shared seed claim),
    no_open_mechanism_history_replaces_the_original_gross_snapshot seed claim history,?_⟩
  unfold Joint.Planning.actualNext
  exact (Joint.Planning.sufficient_source_resources_force_the_actual_shared_payment
    seed claim (shared seed claim) enough).grossPaid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
