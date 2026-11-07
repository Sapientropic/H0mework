import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Completed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
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

theorem the_physical_source_after_is_the_same_paid_material_result :
    (Physical.Public.stateAt seed.input seed.depth seed.count 0 0 [] (Physical.next (Runtime.cursor seed claim)).past).raw =
      (paidState seed claim).raw := by
  rw [Physical.Public.consumed_input_generates_its_own_after]
  change (Physical.Public.compile seed.input
    (Physical.Public.stateAt seed.input seed.depth seed.count 0 0 [] (Execution.Prefix.sharedCursor seed).past)
    (.execute (Material.word seed claim))).next.raw = _
  unfold Execution.Prefix.sharedCursor
  rw [Physical.Prefix.past_readback]
  exact Execution.Selected.physical_and_financial_execution_have_the_same_material_next seed claim

theorem the_resumed_live_raw_is_the_same_actual_paid_raw :
    Ingress.Native.rawAt (nativeFrame seed claim enough) (completedActual seed claim enough) =
      (paidState seed claim).raw := by
  unfold Ingress.Native.rawAt Public.Inquiry.ActualAt.snapshot
  change (Physical.Public.stateAt seed.input seed.depth seed.count 0 0 []
    (if (Drain.completed seed claim).bodyPaid then Physical.next (Runtime.cursor seed claim) else Runtime.cursor seed claim).past).raw = _
  rw [(Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.2,if_pos rfl]
  exact the_physical_source_after_is_the_same_paid_material_result seed claim

theorem the_next_source_context_reads_this_same_actual_raw :
    Factory.Context.readRaw (completedContext seed claim enough) = (paidState seed claim).raw :=
  (Ingress.Native.the_live_raw_is_the_existing_native_occurrence _ _ _ _ _).trans
    (the_resumed_live_raw_is_the_same_actual_paid_raw seed claim enough)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
