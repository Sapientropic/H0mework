import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Settlement
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Trace
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeSettlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers.Review

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open PublicFunction Execution
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (lifeWord life source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

abbrev wholeFee := Evolving.Epoch.Consumers.reviewFee.resign false

def halfFee : Request Bool Bool Bool Unit Unit :=
  { wholeFee with operation := .use false [(false, 1 / 2)] .external }

def word := lifeWord ++ [halfFee, halfFee]

def script := primitiveScript word

theorem the_original_root_actually_pays_two_half_uses :
    Trace lifeSource word (endAt lifeSource script) ∧ Ready (endAt lifeSource script) := by
  have signatures : ∀ request ∈ word, request.consents = [] := by
    intro request listed
    simp only [word, lifeWord, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl <;> rfl
  have approved : ∀ item ∈ (Physical.Public.interpreter lifeSource.native.input).rawItems lifeSource.raw word,
      (Physical.Public.interpreter lifeSource.native.input).Valid item.before item.request := by
    rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    simp only [word, lifeWord, List.cons_append, List.nil_append, RawLaw.rawItems, RawLaw.execute,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    decide +kernel
  obtain ⟨trace, ready, _⟩ := pay_checked_primitives lifeSource word 0 source_ready source_review signatures approved
  exact ⟨trace, ready⟩

theorem the_two_half_uses_keep_the_original_whole_settlement : Settled lifeSource script := by
  refine settle lifeSource _ ⟨(Demand.primitive_covers_iff_original_floor the_original_root_actually_pays_two_half_uses.1).mpr ?_,
    the_original_root_actually_pays_two_half_uses.2⟩
  intro cell listed
  obtain ⟨bearer, _, item⟩ := List.mem_flatMap.mp listed
  rw [source_input_is_the_original_registered_input] at item
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] ++ [] at item
  have same : cell = (bearer, .necessity, true, 1) := by simpa [amount] using item
  rw [same, source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  cases bearer <;> decide +kernel

/-- The due amount uses the old whole fee request's bearer, quantity and
material unit. Its two paid parts are still the original primitive visits. -/
def taskAt (deadline : ℚ) : PublicTaskSpec Bool Bool where
  slots := [⟨false, [(false, 1)], .external⟩]
  earliest := min lifeSource.raw.clock deadline
  deadline := deadline
  demand := by decide

theorem original_task_uses_the_same_whole_fee_request (deadline : ℚ) :
    (taskAt deadline).slots.map (fun slot => Operation.use (Technology := Unit) (Instrument := Unit)
      slot.bearer slot.goods slot.purpose) = [wholeFee.operation] := rfl

def ids : Finset Unit := {()}

def tasks (deadline : ℚ) (_ : Unit) := taskAt deadline

abbrev liveClock := lifeSource.raw.clock

theorem four_original_material_ordinals : (inventory lifeSource script).length = 4 := by
  unfold script
  rw [primitive_inventory the_original_root_actually_pays_two_half_uses.1 0, List.length_map, RawLaw.inventory_length]
  rfl

abbrev OriginalOrdinal := Ordinal lifeSource script

def rawTimed :=
  (((Physical.Public.interpreter lifeSource.native.input).rawItems lifeSource.raw word).map
    fun item => ({item with index := 0}, liveClock))

theorem timed_receipt_at_its_original_ordinal (ordinal : OriginalOrdinal) :
    some (timedAt lifeSource script ordinal) = rawTimed[ordinal.val]? := by
  have exactWord : timedInventory lifeSource script = rawTimed :=
    timed_primitives_are_the_original_material_at_the_same_clock the_original_root_actually_pays_two_half_uses.1
  rw [← exactWord]
  unfold timedAt
  exact (List.getElem?_eq_getElem _).symm

theorem every_original_primitive_debit_commits_at_the_same_clock (ordinal : OriginalOrdinal) :
    (timedAt lifeSource script ordinal).2 = liveClock := by
  have last := a_paid_primitive_trace_keeps_the_actual_clock the_original_root_actually_pays_two_half_uses.1
  have bounds := an_ordinal_uses_its_actual_committing_clock lifeSource script ordinal
  exact le_antisymm (bounds.2.trans_eq last) bounds.1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers
