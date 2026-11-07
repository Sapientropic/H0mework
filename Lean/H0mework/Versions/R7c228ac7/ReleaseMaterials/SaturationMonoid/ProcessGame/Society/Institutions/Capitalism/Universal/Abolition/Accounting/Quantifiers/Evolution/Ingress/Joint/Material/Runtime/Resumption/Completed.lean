import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Frame
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Endpoint
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Native.Source

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

def completedVisit := Runtime.temporalAt seed claim (Execution.Selected.items seed claim).length

def completedActual : Public.Inquiry.ActualAt (nativeFrame seed claim enough) (completedVisit seed claim).current :=
  ⟨Drain.completed seed claim,by
    change stageCursor seed (Runtime.visitAt seed claim (Execution.Selected.items seed claim).length).current = _
    rw [Runtime.the_final_actual_native_coordinate_is_the_source_completed_cursor seed claim]
    exact if_pos (Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.2⟩

def completedAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (nativeFrame seed claim enough).root
    (completedVisit seed claim) ((nativeFrame seed claim enough).entry (completedVisit seed claim).current) := by
  change SourceNativeLivingTemporalCausalEntryAuthorityAt (Runtime.Inquiry.root seed claim)
    (Runtime.temporalAt seed claim (Execution.Selected.items seed claim).length)
    (entry seed claim enough (Runtime.visitAt seed claim (Execution.Selected.items seed claim).length).current)
  exact authorityAt seed claim enough (Execution.Selected.items seed claim).length

def completedContext := Ingress.Native.context (nativeFrame seed claim enough) (completedVisit seed claim)
  (completedActual seed claim enough) ((nativeFrame seed claim enough).entry (completedVisit seed claim).current)
  (completedAuthority seed claim enough)

theorem the_returned_native_current_is_the_same_completed_original_account :
    (completedActual seed claim enough).actual.account = Execution.Selected.after seed claim :=
  (Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).1

theorem the_returned_native_current_has_no_replayed_original_pending_head :
    Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
      (completedActual seed claim enough).actual = none :=
  Drain.the_finite_source_budget_leaves_no_original_head seed claim

include enough in
theorem the_same_completed_root_still_owns_both_zero_budget_historical_rows :
    (Productive.law seed claim).budget (.current (paidState seed claim)) = 0 ∧
      (Gross.law seed claim).budget (paidState seed claim) = 0 :=
  the_fixed_historical_rows_have_no_remaining_budget seed claim enough

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
