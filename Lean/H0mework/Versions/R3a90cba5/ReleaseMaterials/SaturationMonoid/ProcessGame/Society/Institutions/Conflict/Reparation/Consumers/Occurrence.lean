import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Discharge
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving

noncomputable section

abbrev warCut : C := Conflict.Consumers.Evolving.source

def address : Key Bool Bool := (false, true, false)

theorem gross_is_the_original_six : gross warCut conflict id address = 6 := by
  unfold gross
  rw [show occurred warCut conflict = compact.law.rawItems oldRaw conflict from by
    unfold occurred
    rw [sourceInput, sourceRead]]
  rw [sourceInput]
  decide +kernel

theorem original : ClaimAt warCut conflict id address := by
  have positive : 0 < gross warCut conflict id address := by rw [gross_is_the_original_six]; decide
  obtain ⟨row, _, same⟩ := every_positive_address_is_assessed warCut conflict id conflictPaid positive
  exact same ▸ row.property

def receipt (amount : ℚ) : R :=
  ⟨false, [], false, [], .transfer true false [(false, amount)]⟩

private theorem executed (word : W)
    (consents : ∀ request ∈ word, request.consents = [])
    (signed : ∀ item ∈ (Physical.Public.interpreter compact).rawItems oldRaw word,
      compact.law.Valid item.before item.request)
    (food : ∀ person : Bool, 1 ≤ Material.actualUse (Macro.Public.Scope.checkInput compact)
      oldRaw word person .necessity true) :
    Conflict.Root.Paid warCut word := by
  have start := conflictPaid.trace.a_nonempty_execution_starts_at_the_actual_ready_boundary
    (by simp [conflict, front])
  have authorized : Conflict.Root.Authorized warCut word := by
    unfold Conflict.Root.Authorized
    rw [sourceInput, sourceRead]
    exact signed
  have valid : ∀ item ∈ (Physical.Public.interpreter warCut.native.input).rawItems warCut.raw word,
      (Physical.Public.interpreter warCut.native.input).Valid item.before item.request :=
    fun item present => PublicFunction.valid_physical _ _ _ (authorized item present)
  obtain ⟨trace, finished, _⟩ := Quantities.Execution.pay_checked_primitives
    warCut word 0 start.1 start.2 consents valid
  refine ⟨authorized, trace, Quantities.settle warCut _ ⟨?_, finished⟩⟩
  apply (Quantities.Demand.primitive_covers_iff_original_floor trace).mpr
  intro cell listed
  obtain ⟨bearer, _, required⟩ := List.mem_flatMap.mp listed
  rw [sourceInput] at required ⊢
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] at required
  have one : amount Bool [(true, 1)] true = 1 := by decide +kernel
  rw [List.mem_singleton.mp required, sourceRead]
  simpa only [one] using food bearer

theorem partialPaid : Conflict.Root.Paid warCut (conflict ++ [receipt 2]) :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fullPaid : Conflict.Root.Paid warCut (conflict ++ [receipt 6]) :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem unilateral_delivery_keeps_six_due :
    remaining warCut conflict [returnAt 6] id address = 6 := by
  rw [unilateral_carry_keeps_the_entire_original_debt original _ (by decide +kernel),
    gross_is_the_original_six]

private theorem receipt_amount (amount : ℚ) :
    received warCut conflict [receipt amount] address =
      ((compact.law.rawItems oldRaw (conflict ++ [receipt amount])).drop conflict.length |>.map
        (fun item => receiptCredit compact.law item address)).sum := by
  unfold received continuationItems occurred
  rw [sourceInput, sourceRead]

theorem partial_delivery_leaves_four : remaining warCut conflict [receipt 2] id address = 4 := by
  rw [remaining, gross_is_the_original_six, receipt_amount]
  decide +kernel

theorem actual_victim_receipt_closes_six : remaining warCut conflict [receipt 6] id address = 0 := by
  rw [remaining, gross_is_the_original_six, receipt_amount]
  decide +kernel

theorem refused_receipt_has_the_original_root_failure :
    ∃ issue, inspect original [receipt 1000] = .refused original issue := by
  have refusal : ¬ Conflict.Root.Paid warCut (conflict ++ [receipt 1000]) := by
    intro paid
    have originalAuth := paid.authorized
    unfold Conflict.Root.Authorized at originalAuth
    rw [sourceInput, sourceRead] at originalAuth
    have unavailable : ¬ ∀ item ∈ (Physical.Public.interpreter compact).rawItems oldRaw
        (conflict ++ [receipt 1000]), compact.law.Valid item.before item.request := by decide +kernel
    exact unavailable originalAuth
  unfold inspect
  cases Conflict.Root.inspect warCut (conflict ++ [receipt 1000]) with
  | rejected issue => exact ⟨issue, rfl⟩
  | paid actual => exact (refusal actual).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers
