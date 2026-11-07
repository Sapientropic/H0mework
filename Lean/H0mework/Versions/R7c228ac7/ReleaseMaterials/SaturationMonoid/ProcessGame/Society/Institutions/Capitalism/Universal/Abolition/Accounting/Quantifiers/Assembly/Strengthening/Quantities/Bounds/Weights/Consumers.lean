import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights.Order
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.CofinalClock
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers.Review
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Consumers.Life

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Optimality.Cost Execution
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (lifeWord life source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource firstPaidPeriod checked_living_period
  the_original_full_period_pays_life_and_finishes_its_native_work)

noncomputable section

def fee := Evolving.Epoch.Consumers.reviewFee.resign false
def quickWord := lifeWord ++ [fee]
def quick := primitiveScript quickWord
def feeAddress : Channel × Bool × Bool := (.use .external, false, false)

private theorem quick_is_actually_paid :
    Trace lifeSource quickWord (endAt lifeSource quick) ∧ Ready (endAt lifeSource quick) := by
  have signatures : ∀ request ∈ quickWord, request.consents = [] := by
    intro request listed
    simp only [quickWord, lifeWord, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl
  have approved : ∀ item ∈ (Physical.Public.interpreter lifeSource.native.input).rawItems lifeSource.raw quickWord,
      (Physical.Public.interpreter lifeSource.native.input).Valid item.before item.request := by
    rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    simp only [quickWord, lifeWord, List.cons_append, List.nil_append, RawLaw.rawItems, RawLaw.execute,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    decide +kernel
  obtain ⟨trace, ready, _⟩ := pay_checked_primitives lifeSource quickWord 0 source_ready source_review signatures approved
  exact ⟨trace, ready⟩

private theorem quick_settles : Settled lifeSource quick := by
  refine settle lifeSource _ ⟨(Demand.primitive_covers_iff_original_floor quick_is_actually_paid.1).mpr ?_,
    quick_is_actually_paid.2⟩
  intro cell listed
  obtain ⟨bearer, _, item⟩ := List.mem_flatMap.mp listed
  rw [source_input_is_the_original_registered_input] at item
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] ++ [] at item
  have same : cell = (bearer, .necessity, true, 1) := by simpa [amount] using item
  rw [same, source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  cases bearer <;> decide +kernel

private theorem quick_clock : elapsed lifeSource quick = 0 := by
  have raw := quick_is_actually_paid.1.raw_is_the_complete_original_execution 0
  have clock := (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
    (Physical.Public.interpreter lifeSource.native.input) lifeSource.raw 0 quickWord).1
  unfold elapsed
  rw [raw, clock, sub_self]

private theorem quick_fee : amount (Channel × Bool × Bool) (material lifeSource quick) feeAddress = 1 := by
  unfold material quick
  rw [primitive_inventory quick_is_actually_paid.1 0]
  change amount (Channel × Bool × Bool)
    (((Physical.Public.interpreter lifeSource.native.input).rawItems lifeSource.raw quickWord).map
      (fun item => {item with index := 0}) |>.flatMap (fun item => channels.flatMap fun channel =>
        (actualPart (Physical.Public.interpreter lifeSource.native.input) item.before item.request channel).map
          fun lot => ((channel, lot.1.1, lot.1.2), lot.2))) feeAddress = 1
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem slower_has_no_fee :
    amount (Channel × Bool × Bool) (material lifeSource firstPaidPeriod) feeAddress = 0 := by
  unfold material firstPaidPeriod
  rw [inventory_of_the_original_period_and_accounting lifeSource lifeWord source_ready source_review checked_living_period]
  change amount (Channel × Bool × Bool)
    (((Physical.Public.interpreter lifeSource.native.input).rawItems lifeSource.raw (normalise lifeWord)).flatMap
      (fun item => channels.flatMap fun channel =>
        (actualPart (Physical.Public.interpreter lifeSource.native.input) item.before item.request channel).map
          fun lot => ((channel, lot.1.1, lot.1.2), lot.2))) feeAddress = 0
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem two_original_whole_payments_reverse_under_the_actual_clock_and_material_weights :
    Settled lifeSource quick ∧ Settled lifeSource firstPaidPeriod ∧
      nativeValue lifeSource quick timeOnly < nativeValue lifeSource firstPaidPeriod timeOnly ∧
      nativeValue lifeSource firstPaidPeriod (materialOnly feeAddress) < nativeValue lifeSource quick (materialOnly feeAddress) := by
  refine ⟨quick_settles, the_original_full_period_pays_life_and_finishes_its_native_work.1, ?_, ?_⟩
  · rw [clock_is_its_own_weighted_readout, clock_is_its_own_weighted_readout, quick_clock,
      the_original_full_period_pays_life_and_finishes_its_native_work.2]
    decide
  · rw [each_material_address_is_its_own_weighted_readout, each_material_address_is_its_own_weighted_readout,
      slower_has_no_fee, quick_fee]
    decide

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights.Consumers
