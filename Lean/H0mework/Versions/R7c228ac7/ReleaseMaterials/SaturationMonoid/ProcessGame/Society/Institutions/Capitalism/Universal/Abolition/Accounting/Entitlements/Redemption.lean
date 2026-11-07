import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements.Funding
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.NoRetake
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Gate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements

open Source.Program Innovation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim source past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

local notation "state" => Abolition.Accounting.Root.Reentry.Frame.state claim frame
local notation "executed" => Priority.Root.Gate.executableWord claim frame proposal

/-- Repair authority cannot be packaged into a new issued, assigned or settled
financial title. New real contributions retain their own native sources. -/
theorem the_original_repair_authority_cannot_be_capitalized_as_a_financial_operation :
    ∀ request ∈ executed, ¬ Priority.Policy.FinancialOperation request.operation := by
  rw [Priority.Root.Gate.executableWord_eq_original_evaluation]
  exact Priority.Policy.accepted_prefix_has_no_financial_operation claim state frame.actualLaw frame.members
    (Priority.Policy.evaluate claim state frame.actualLaw frame.members proposal).accepted

theorem a_cleared_original_row_cannot_renew_any_compulsory_take
    (paid : Responsibility.Family.State.isPaid claim state) :
    ∀ request ∈ executed, ¬ Priority.Policy.CompulsoryTake request.operation := by
  rw [Priority.Root.Gate.executableWord_eq_original_evaluation]
  exact Priority.Policy.accepted_paid_prefix_has_no_new_compulsory_request claim state frame.actualLaw frame.members paid
    (Priority.Policy.evaluate claim state frame.actualLaw frame.members proposal).accepted

theorem no_real_disbursement_can_be_minted_by_redeeming_the_old_repair_row
    (terms : PublicFunction.Financing.Terms Party Instrument) :
    ¬ Nonempty (PublicFunction.Financing.Disbursement frame.actualLaw (state).raw executed terms) := by
  rintro ⟨receipt⟩
  have original : receipt.issue.request ∈ executed := by
    have inside : receipt.issue.request ∈
        (frame.actualLaw.rawItems (state).raw executed).map ExecutionItem.request :=
      List.mem_map.mpr ⟨receipt.issue,receipt.issue_mem,rfl⟩
    dsimp only [RawLaw.rawItems] at inside
    rw [frame.actualLaw.inventory_requests_exact (state).raw 0 executed] at inside
    exact inside
  have absent := the_original_repair_authority_cannot_be_capitalized_as_a_financial_operation
    claim frame proposal receipt.issue.request original
  rw [receipt.issue_kind] at absent
  exact absent trivial

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements
