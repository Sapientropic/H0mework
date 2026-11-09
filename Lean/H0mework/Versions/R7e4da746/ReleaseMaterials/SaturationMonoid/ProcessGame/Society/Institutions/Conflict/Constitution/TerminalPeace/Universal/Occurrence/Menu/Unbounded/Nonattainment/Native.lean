import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Unbounded
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original

/-!
A bounded rational return uses the original debtor's signed material
transfer and both actual answer lanes. The original loss and cut are fixed.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Unbounded.Nonattainment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (compact returnAt sourceInput)
open Quantities.Execution
open Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem)
open ExposureGuard
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

abbrev loss := Original.occurrence
abbrev born := history loss
abbrev past : Original.Word := born ++ [none]
def answers : ReceiptAnswers Original.seed := fun _ _ _ _ => true
def payment (quantity : ℚ) : Reparation.Actual.Input Bool Bool Bool Unit Unit :=
  some (.primitive (returnAt quantity))
def word (quantity : ℚ) : Original.Word := [none, payment quantity]

theorem the_native_head_leaves_no_material : Boundary.Actual.items (endAt Original.seed born) none = [] :=
  Original.levy_native_has_no_second_item

private theorem physical_cut : endAt Original.seed past = Original.cut :=
  congrArg (endAt Original.seed) Original.exact_history.symm

private theorem compact_payment_is_legal (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6) :
    compact.law.Valid (Original.snapshot 111 113) (returnAt quantity) := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, rfl⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro port listed
    change port ∈ [false] at listed
    rw [List.mem_singleton.mp listed]
    exact Or.inl rfl
  · intro item listed
    change item ∈ [((true, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro item listed
    change item ∈ [((false, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro item listed
    change item ∈ [((true, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    change flowAt (locate true [(false, quantity)]) true false ≤ 113
    simpa [flowAt, amount, locate] using (small.le.trans (by norm_num : (6 : ℚ) ≤ 113))

private theorem legal_at_cut (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6) :
    Original.cut.native.input.law.Valid Original.cut.raw (returnAt quantity) := by
  rw [Original.same_source, Original.cut_raw]
  exact compact_payment_is_legal quantity positive small

theorem original_payment_items (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6) :
    Boundary.Actual.items (endAt Original.seed past) (payment quantity) =
      [⟨0, Original.cut.raw, returnAt quantity⟩] := by
  rw [physical_cut]
  exact (the_selected_primitive_is_paid_by_the_original_root (queued Original.cut (returnAt quantity))
    (returnAt quantity) Original.ready (the_available_review_forwards_the_actual_requested_primitive _ _ Original.review)
    rfl (PublicFunction.valid_physical _ _ _ (legal_at_cut quantity positive small))).2.2

theorem the_payer_signs_without_any_new_loss (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6) :
    Boundary.Actual.damages (endAt Original.seed past) (payment quantity) Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro loss _
  have literal := loss.source_item
  rw [original_payment_items quantity positive small] at literal
  have exactItem := List.mem_singleton.mp literal
  have keys := original_key loss
  have valid := loss.actual_foreign_debit.2.1
  rw [exactItem] at keys valid
  unfold keysAt at keys
  rw [RawLaw.actualDebit, if_pos valid] at keys
  change loss.key ∈ [(true, true, false)] at keys
  have foreign := loss.actual_foreign_debit.1.1
  rw [List.mem_singleton.mp keys] at foreign
  exact foreign rfl

theorem the_partial_payment_word_is_eligible (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6) :
    Eligible answers loss (word quantity) := by
  refine ⟨⟨no_material_is_admitted _ _ _ _ the_native_head_leaves_no_material,
    Boundary.Actual.no_material_write_has_no_damage _ _ _ the_native_head_leaves_no_material⟩,
    ⟨⟨?_, fun _ _ _ _ => rfl⟩, the_payer_signs_without_any_new_loss quantity positive small⟩, trivial⟩
  intro item listed
  change item ∈ Boundary.Actual.items (endAt Original.seed past) (payment quantity) at listed
  rw [original_payment_items quantity positive small] at listed
  rw [List.mem_singleton.mp listed, physical_cut]
  exact legal_at_cut quantity positive small

def position (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6) :
    Position Original.seed past (payment quantity) :=
  ⟨0, by
    rw [original_payment_items quantity positive small]
    exact Nat.zero_lt_one⟩

private theorem item_at_payment (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6)
    (site : Position Original.seed past (payment quantity)) :
    originalItem Original.seed past (payment quantity) site = ⟨0, Original.cut.raw, returnAt quantity⟩ := by
  let item := originalItem Original.seed past (payment quantity) site
  have actual : item ∈ Boundary.Actual.items (endAt Original.seed past) (payment quantity) := List.getElem_mem _
  rw [original_payment_items quantity positive small] at actual
  exact List.mem_singleton.mp actual

theorem the_actual_payer_credit_equals_the_requested_quantity
    (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6)
    (site : Position Original.seed past (payment quantity)) :
    payerCredit Original.seed.native.input.law (originalItem Original.seed past (payment quantity) site) loss.key = quantity := by
  rw [item_at_payment quantity positive small site, sourceInput, Original.cut_raw]
  have allowed := compact_payment_is_legal quantity positive small
  unfold returnAt at allowed
  change payerCredit compact.law ⟨0, Original.snapshot 111 113, returnAt quantity⟩ (false, true, false) = quantity
  simp [payerCredit, returnAt, allowed, RawLaw.actualCredit, RawLaw.credit, locate, flowAt, amount,
    max_eq_right positive.le]

#print axioms the_partial_payment_word_is_eligible
#print axioms the_actual_payer_credit_equals_the_requested_quantity

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Unbounded.Nonattainment
