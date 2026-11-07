import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Handler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))


/-- Uniform closure of the computed actual chain, including every old row.
No next current, old-row enumeration, branch success, or per-step invariant
is supplied by the caller. -/
structure ClosedAt (n : Nat) : Prop where
  actual_next : (currentAt source (n + 1)).inquiry.erase =
    (RootInquiryProcessNode.answered (currentAt source n).inquiry PUnit.unit).erase
  actual_living_law : (RootInquiryProcessNode.active (currentAt source n).inquiry).PreservesGeneratedLivingLawAt
    PUnit.unit (RootInquiryProcessNode.active (currentAt source (n + 1)).inquiry)
  original_claims_injective : Function.Injective (claimAt source n)
  whole_original_ledger : ∀ row, (rowAt source row n).claim = claimAt source n row.claim ∧
    (rowAt source row n).progressBudget ≤ row.progressBudget
  productive_history : rowAt source source.rows.productive n = (currentAt source n).rows.productive
  gross_history : rowAt source source.rows.gross n = (currentAt source n).rows.gross
  productive_paid : (currentAt source n).rows.productive.progressBudget = 0
  gross_paid : (currentAt source n).rows.gross.progressBudget = 0
  actual_handler_commutes : (currentAt source n).handlerFace.rootRead = (currentAt source n).handlerLaw
  no_capital_active_face : Global.NoCapital (currentAt source n).handlerFace.rootRead
  no_capital_handler : Global.NoCapital (currentAt source n).handlerLaw

theorem the_source_generates_its_whole_ledger_evolving_closure (n : Nat) : ClosedAt source n where
  actual_next := (every_step_is_the_actual_root_query source n).1
  actual_living_law := (every_step_is_the_actual_root_query source n).2
  original_claims_injective := every_actual_claim_map_is_injective source n
  whole_original_ledger := fun row => ⟨every_original_row_keeps_its_claim source row n,
    no_original_responsibility_can_be_refilled source row n⟩
  productive_history := the_productive_row_is_the_carried_original source n
  gross_history := the_gross_row_is_the_carried_original source n
  productive_paid := (currentAt source n).rows.productive_zero
  gross_paid := (currentAt source n).rows.gross_zero
  actual_handler_commutes := NativeCurrent.handlerFace_reads_the_actual_handler _
  no_capital_active_face := NativeCurrent.the_actual_root_interpreter_excludes_every_capital_relation _
  no_capital_handler := each_actual_handler_excludes_every_capital_relation source n

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History
