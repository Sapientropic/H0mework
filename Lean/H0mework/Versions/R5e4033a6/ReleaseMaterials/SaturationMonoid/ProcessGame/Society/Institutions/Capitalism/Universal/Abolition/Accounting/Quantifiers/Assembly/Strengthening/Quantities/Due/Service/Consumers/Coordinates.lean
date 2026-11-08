import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers.Source
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Execution PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open Innovation.Contribution.Pricing.Consumers.Actual
  (source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair)

noncomputable section

abbrev Lines (deadline : ℚ) := Need ids (tasks deadline)
abbrev Receipts (deadline : ℚ) := Supply lifeSource script ids (tasks deadline)

def firstSlot (deadline : ℚ) : Slot ids (tasks deadline) :=
  ⟨⟨(), by decide⟩, ⟨0, by change 0 < 1; decide⟩⟩

def firstNeed (deadline : ℚ) : Lines deadline :=
  ⟨firstSlot deadline, ⟨false, by change false ∈ ({false} : Finset Bool); simp⟩⟩

private theorem all_slots_are_original (deadline : ℚ) (slot : Slot ids (tasks deadline)) :
    slot = firstSlot deadline := by
  obtain ⟨id, index⟩ := slot
  have oneId : id = (firstSlot deadline).1 := Subtype.ext (Subsingleton.elim _ _)
  subst id
  have oneIndex : index = (firstSlot deadline).2 := by
    apply Fin.ext
    have inside : index.val < 1 := index.isLt
    change index.val = 0
    omega
  cases oneIndex
  rfl

theorem all_lines_are_original (deadline : ℚ) (line : Lines deadline) :
    line = firstNeed deadline := by
  obtain ⟨slot, good⟩ := line
  have one := all_slots_are_original deadline slot
  subst slot
  have actual : good.val = false := by
    have inside := good.property
    change good.val ∈ ({false} : Finset Bool) at inside
    exact Finset.mem_singleton.mp inside
  have exactGood : good = (firstNeed deadline).2 := Subtype.ext actual
  cases exactGood
  rfl

abbrev onlyLine (deadline : ℚ) : Unique (Lines deadline) :=
  ⟨⟨firstNeed deadline⟩, all_lines_are_original deadline⟩

theorem original_due_requirements_are_nonnegative (deadline : ℚ) : OriginalDemands ids (tasks deadline) := by
  intro slot
  rw [all_slots_are_original deadline slot]
  change NonnegativeBundle Bool [(false, 1)]
  decide

theorem each_original_line_needs_one (deadline : ℚ) (line : Lines deadline) :
    (network lifeSource script ids (tasks deadline) ∅).need line = 1 := by
  rw [all_lines_are_original deadline line]
  change max (0 : ℚ) (amount Bool [(false, 1)] false) = 1
  norm_num [amount]

private theorem goods_are_the_original_unit (deadline : ℚ) :
    goods ids (tasks deadline) = {false} := by
  ext good
  unfold goods
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨slot, _, inside⟩
    rw [all_slots_are_original deadline slot] at inside
    exact inside
  · intro present
    exact ⟨firstSlot deadline, Finset.mem_univ _, present⟩

theorem receipt_unit (deadline : ℚ) (receipt : Receipts deadline) : receipt.2.val = false := by
  have original := congrArg (fun units : Finset Bool => receipt.2.val ∈ units)
    (goods_are_the_original_unit deadline)
  exact Finset.mem_singleton.mp (original.mp receipt.2.property)

def receiptNumber (deadline : ℚ) : Receipts deadline ≃ Fin 4 where
  toFun := fun receipt => Fin.cast four_original_material_ordinals receipt.1
  invFun := fun ordinal =>
    (Fin.cast four_original_material_ordinals.symm ordinal,
      ⟨false, by rw [goods_are_the_original_unit]; exact Finset.mem_singleton_self _⟩)
  left_inv := by
    intro receipt
    apply Prod.ext
    · apply Fin.ext
      rfl
    · exact Subtype.ext (receipt_unit deadline receipt).symm
  right_inv := by
    intro ordinal
    apply Fin.ext
    rfl

private abbrev interpreter := Physical.Public.interpreter lifeSource.native.input
private abbrev Item := ExecutionItem Bool Bool Bool Unit Unit

private def observation (entry : Item × ℚ) : ℚ × Bool :=
  letI : Decidable (interpreter.Valid entry.1.before entry.1.request) :=
    RawLaw.instDecidableValid interpreter entry.1.before entry.1.request
  (paidAmount interpreter entry.1 false,
    decide (liveClock ≤ entry.1.before.clock ∧ entry.2 ≤ liveClock ∧
      interpreter.Valid entry.1.before entry.1.request ∧ useFor entry.1 (firstSlot liveClock).spec))

private theorem original_numeric_observation (ordinal : Fin 4) :
    rawTimed[ordinal.val]?.map observation =
      some (if 2 ≤ ordinal.val then ((1 / 2 : ℚ), true) else (0, false)) := by
  unfold rawTimed observation interpreter liveClock
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  fin_cases ordinal <;> decide +kernel

private theorem native_observation (ordinal : OriginalOrdinal) :
    observation (timedAt lifeSource script ordinal) =
      if 2 ≤ ordinal.val then ((1 / 2 : ℚ), true) else (0, false) := by
  apply Option.some.inj
  exact (congrArg (Option.map observation) (timed_receipt_at_its_original_ordinal ordinal)).trans
    (original_numeric_observation (Fin.cast four_original_material_ordinals ordinal))

theorem each_original_half_debit_supplies_exactly_half
    (deadline : ℚ) (receipt : Receipts deadline) (later : 2 ≤ receipt.1.val) :
    (network lifeSource script ids (tasks deadline) ∅).capacity receipt = 1 / 2 := by
  have actual := congrArg Prod.fst (native_observation receipt.1)
  rw [if_pos later] at actual
  unfold network
  simp only [Finset.notMem_empty, ↓reduceIte, receipt_unit deadline receipt]
  exact actual

theorem each_half_debit_is_signed_and_commits_in_the_original_window
    (line : Lines liveClock) (receipt : Receipts liveClock) (later : 2 ≤ receipt.1.val) :
    (network lifeSource script ids (tasks liveClock) ∅).allows line receipt = true := by
  have actual := congrArg Prod.snd (native_observation receipt.1)
  rw [if_pos later] at actual
  have accepted := of_decide_eq_true actual
  rw [all_lines_are_original liveClock line]
  apply (network_allows_iff _ _ _ _ _ _ _).mpr
  exact ⟨Finset.notMem_empty _, (receipt_unit liveClock receipt).symm,
    (min_le_left _ _).trans accepted.1, accepted.2.1, accepted.2.2.1, accepted.2.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers
