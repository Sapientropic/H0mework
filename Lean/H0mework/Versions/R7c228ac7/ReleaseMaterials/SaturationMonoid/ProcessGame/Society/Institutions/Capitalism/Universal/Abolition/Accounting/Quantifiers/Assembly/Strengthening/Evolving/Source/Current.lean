import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open Source.Program Innovation Quantifiers.Joint Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Execution.Selected.items Planning.selected Planning.actualNext Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

variable (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

/-- The initial evolving current is the completed original runtime, equipped
with this actual query code and its inherited sealed authority. -/
def initial : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := seed.input
  depth := seed.depth
  count := seed.count
  prefixLimit := 0
  renewalLimit := 0
  oldPast := []
  start := Runtime.cursor seed claim
  frame := Runtime.Resumption.nativeFrame seed claim enough
  reader := reader
  visit := Runtime.Resumption.completedVisit seed claim
  actual := Runtime.Resumption.completedActual seed claim enough
  bodyPaid := (Runtime.Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.2
  authority := (Runtime.Resumption.completedAuthority seed claim enough).withProjectionCoface
    (Public.Inquiry.component (Runtime.Resumption.nativeFrame seed claim enough) reader)
  rows := initialRows seed claim enough

theorem initial_reads_the_completed_original_financial_account :
    (initial seed claim enough reader).actual.actual.account = Execution.Selected.after seed claim :=
  Runtime.Resumption.the_returned_native_current_is_the_same_completed_original_account seed claim enough

theorem initial_does_not_restart_the_paid_body :
    (initial seed claim enough reader).actual.actual.bodyPaid = true :=
  (initial seed claim enough reader).bodyPaid

theorem initial_account_heq : HEq (initial seed claim enough reader).actual.actual.account
    (Execution.Selected.after seed claim) :=
  heq_of_eq (initial_reads_the_completed_original_financial_account seed claim enough reader)

theorem initial_has_no_pending_native_work :
    ¬ Public.Inquiry.HasWork (initial seed claim enough reader).frame
      (initial seed claim enough reader).actual.actual := by
  change ¬ ((Runtime.Drain.completed seed claim).bodyPaid = false ∨
    (Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
      (Runtime.Drain.completed seed claim)).isSome = true)
  rw [(Runtime.Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.2,
    Runtime.Drain.the_finite_source_budget_leaves_no_original_head seed claim]
  simp

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source
