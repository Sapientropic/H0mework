import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Root
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Read
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse.Account

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

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

def futureSource := Continuation.nextSparse seed claim (Execution.Selected.items seed claim).length

theorem funded_native_completion_generates_the_actual_paid_open_source
    (enough : Joint.Planning.Enough seed claim (shared seed claim)) :
    Responsibility.Family.State.isPaid seed.claim (Evolution.Sparse.Current.state seed.claim (futureSource seed claim)) := by
  unfold futureSource
  apply (Continuation.nextSparse_paid_iff seed claim (Execution.Selected.items seed claim).length).2
  change Joint.Current.productivePaid seed claim
    (Runtime.sharedAt seed claim (Runtime.visitAt seed claim (Execution.Selected.items seed claim).length).current)
  rw [Runtime.the_named_final_root_keeps_the_one_executed_material_result]
  unfold Joint.Planning.actualNext
  exact (Joint.Planning.sufficient_source_resources_force_the_actual_shared_payment
    seed claim (shared seed claim) enough).productivePaid

variable {target : Evolution.Sparse.Current (oldN := Continuation.base seed claim) seed.claim}

theorem every_open_mechanism_history_from_the_actual_joint_endpoint_excludes_all_capital
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target) :
    Global.NoCapital target.actualLaw := by
  rw [(Evolution.Sparse.History.every_history_keeps_the_same_effective_law_and_roster seed.claim history).1]
  rw [← Evolution.Sparse.Current.readLaw_eq]
  exact Continuation.nextSparse_no_capital seed claim _

theorem every_coalition_has_its_full_account_through_every_actual_open_mechanism_history
    (enough : Joint.Planning.Enough seed claim (shared seed claim))
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target)
    (members : Party → Bool) (good : Good) :
    Global.NoCapital target.actualLaw ∧
      Responsibility.Family.State.isPaid seed.claim (Evolution.Sparse.Current.state seed.claim target) ∧
      Coalition.read members good (Coalition.Sparse.income seed.claim history) ≤ 0 ∧
      Coalition.read members good (Coalition.Sparse.income seed.claim history) +
        Coalition.read members good (Coalition.Sparse.consumed seed.claim history) = 0 := by
  have paid := funded_native_completion_generates_the_actual_paid_open_source seed claim enough
  exact ⟨every_open_mechanism_history_from_the_actual_joint_endpoint_excludes_all_capital seed claim history,
    Coalition.Sparse.every_history_keeps_the_actual_paid_row_paid seed.claim history paid,
    Coalition.Sparse.every_coalition_has_nonpositive_income_along_every_paid_row_history seed.claim history paid members good,
    Coalition.Sparse.every_coalition_keeps_its_actual_consumption_along_every_history seed.claim history paid members good⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
