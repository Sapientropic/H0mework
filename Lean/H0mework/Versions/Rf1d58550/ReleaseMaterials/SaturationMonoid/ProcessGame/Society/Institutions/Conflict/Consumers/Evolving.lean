import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualSource

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

abbrev C := Conflict.Root.Cut Bool Bool Bool Unit Unit
abbrev R := Request Bool Bool Bool Unit Unit
abbrev W := RawEvent Bool Bool Bool Unit Unit
abbrev compact := Accounting.Quantifiers.Joint.Consumers.Compact.input

namespace Original
export Innovation.Contribution.Pricing.Consumers.Actual
  (source source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair quoteCut)
end Original

def issue : R := ⟨true, [], false, [], .issue () true false 6⟩
def source : C := afterNative Original.source issue
def oldRaw := (Physical.Public.interpreter compact).step Original.quoteCut issue

private theorem issueValid : (Physical.Public.interpreter Original.source.native.input).Valid Original.source.raw issue := by
  rw [Original.source_input_is_the_original_registered_input, Original.the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem sourceReady : Ready source :=
  (two_actual_root_steps_pay_and_consume_the_generated_primitive Original.source issue
    Original.source_ready Original.source_review rfl issueValid).1

private theorem sourceReview : ReviewAvailable source :=
  afterNative_keeps_the_available_review Original.source issue Original.source_ready Original.source_review rfl issueValid

theorem sourceInput : source.native.input = compact :=
  (afterNative_keeps_the_same_original_input Original.source issue).trans
    Original.source_input_is_the_original_registered_input

theorem sourceRead : source.raw = oldRaw := by
  unfold source
  rw [(two_actual_root_steps_pay_and_consume_the_generated_primitive Original.source issue
    Original.source_ready Original.source_review rfl issueValid).2,
    Original.source_input_is_the_original_registered_input,
    Original.the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  rfl

def settle : R := ⟨true, [], false, [], .settle () true false 6⟩
def destroy : R := ⟨true, [], false, [], .use true [(false, 2)] .external⟩
def levy : R := ⟨true, [], false, [true], .transfer false true [(false, 6)]⟩
def returnAt (amount : ℚ) : R := ⟨true, [], false, [], .transfer true false [(false, amount)]⟩
def life (bearer : Bool) : R := ⟨bearer, [], false, [], .use bearer [(true, 1)] .necessity⟩
def peace : W := [settle, life false, life true]
def front : W := [life false, life true, destroy]
def conflict : W := front ++ [levy, settle]
def restored (amount : ℚ) : W := conflict ++ [returnAt amount]

private theorem paidFromOriginalGuards (word : W)
    (consents : ∀ request ∈ word, request.consents = [])
    (signed : ∀ item ∈ (Physical.Public.interpreter compact).rawItems oldRaw word,
      compact.law.Valid item.before item.request)
    (food : ∀ person : Bool, 1 ≤ Material.actualUse (Macro.Public.Scope.checkInput compact) oldRaw word person .necessity true) :
    Conflict.Root.Paid source word := by
  have authorized : Conflict.Root.Authorized source word := by
    unfold Conflict.Root.Authorized
    rw [sourceInput, sourceRead]
    exact signed
  have valid : ∀ item ∈ (Physical.Public.interpreter source.native.input).rawItems source.raw word,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request :=
    fun item present => PublicFunction.valid_physical source.native.input.law item.before item.request (authorized item present)
  obtain ⟨actual, finished, _available⟩ := Quantities.Execution.pay_checked_primitives
    source word 0 sourceReady sourceReview consents valid
  refine ⟨authorized, actual, Quantities.settle source _ ⟨?_, finished⟩⟩
  apply (Quantities.Demand.primitive_covers_iff_original_floor actual).mpr
  intro cell listed
  obtain ⟨bearer, _present, required⟩ := List.mem_flatMap.mp listed
  rw [sourceInput] at required ⊢
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] at required
  have one : amount Bool [(true, 1)] true = 1 := by decide +kernel
  rw [List.mem_singleton.mp required, sourceRead]
  simpa only [one] using food bearer

theorem peacePaid : Conflict.Root.Paid source peace :=
  paidFromOriginalGuards peace (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem conflictPaid : Conflict.Root.Paid source conflict :=
  paidFromOriginalGuards conflict (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fullReturnPaid : Conflict.Root.Paid source (restored 6) :=
  paidFromOriginalGuards (restored 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bindingReturnPaid : Conflict.Root.Paid source (restored 4) :=
  paidFromOriginalGuards (restored 4) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def decisionStock (cut : C) : ℚ := cut.raw.stock true false

theorem old_war_peace_gap : decisionStock (Conflict.Root.terminal source conflict) -
    decisionStock (Conflict.Root.terminal source peace) = 4 := by
  unfold decisionStock
  rw [conflictPaid.raw_exact, peacePaid.raw_exact, sourceInput, sourceRead]
  decide +kernel

theorem restored_war_peace_gap : decisionStock (Conflict.Root.terminal source (restored 6)) -
    decisionStock (Conflict.Root.terminal source peace) = -2 := by
  unfold decisionStock
  rw [fullReturnPaid.raw_exact, peacePaid.raw_exact, sourceInput, sourceRead]
  decide +kernel

theorem binding_return_is_a_paid_tie : decisionStock (Conflict.Root.terminal source (restored 4)) -
    decisionStock (Conflict.Root.terminal source peace) = 0 := by
  unfold decisionStock
  rw [bindingReturnPaid.raw_exact, peacePaid.raw_exact, sourceInput, sourceRead]
  decide +kernel

#print axioms peacePaid
#print axioms conflictPaid
#print axioms fullReturnPaid
#print axioms binding_return_is_a_paid_tie

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
