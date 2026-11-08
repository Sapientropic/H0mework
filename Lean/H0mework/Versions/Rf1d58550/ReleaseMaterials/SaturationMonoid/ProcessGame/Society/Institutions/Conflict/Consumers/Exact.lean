import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Native
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold.Reattachment
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Primitive

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered

noncomputable section

private theorem nativeFold_append (cursor : Cursor) (account : Account) (front back : Word) :
    nativeFold cursor account (front ++ back) =
      nativeFold (nativeFold cursor account front).1 (nativeFold cursor account front).2 back := by
  induction front generalizing cursor account with
  | nil => rfl
  | cons command tail inherited =>
      exact inherited (Physical.next (submitted cursor command)) (consume cursor command account)

theorem raw_snoc (word : Word) (command : Command) :
    raw (word ++ [command]) = law.step (raw word) command := by
  unfold raw run
  rw [nativeFold_append]
  change (Physical.stateAt input depth count 0 0
    (Physical.next (submitted (nativeFold Physical.initial openingNative word).1 command)).past).raw = _
  rw [Physical.consumed_input_generates_its_own_after]
  exact Compile.primitive_after_is_the_original_guarded_step input depth count 0 0 _ _

theorem the_original_reimbursement_capacity (quantity : ℚ) :
    law.Valid (raw imposed) (restore quantity) ↔ 0 ≤ quantity ∧ quantity ≤ 8 := by
  have stockAt : (raw imposed).stock controller () = 8 := exact_native_material_controls.2.1
  have debit : law.debit (raw imposed) (restore quantity) = [((controller, ()), quantity)] := rfl
  have credit : law.credit (raw imposed) (restore quantity) = [((exposed, ()), quantity)] := rfl
  have ports : law.requiredPorts (raw imposed) (restore quantity) = [controller] := rfl
  have flow : flowAt (law.debit (raw imposed) (restore quantity)) controller () = quantity := by
    rw [debit]
    simp [flowAt, amount]
  constructor
  · intro accepted
    have nonnegative := accepted.2.2.2.1
    have covered := accepted.2.2.2.2.2
    rw [debit] at nonnegative
    refine ⟨nonnegative _ List.mem_cons_self, ?_⟩
    have paid := covered ((controller, ()), quantity) (by rw [debit]; exact List.mem_cons_self)
    simpa only [flow, stockAt] using paid
  · rintro ⟨nonnegative, capacity⟩
    refine ⟨⟨trivial, rfl⟩, ?_, trivial, ?_, ?_, ?_⟩
    · intro port present
      rw [ports] at present
      rw [List.mem_singleton.mp present]
      exact Or.inl (by simp [law, restore, request])
    · rw [debit]
      intro item present
      rw [List.mem_singleton.mp present]
      exact nonnegative
    · rw [credit]
      intro item present
      rw [List.mem_singleton.mp present]
      exact nonnegative
    · intro item present
      rw [debit] at present
      rw [List.mem_singleton.mp present]
      simpa only [flow, stockAt] using capacity

theorem every_affordable_actual_reimbursement_has_the_exact_pressure
    (quantity : ℚ) (nonnegative : 0 ≤ quantity) (capacity : quantity ≤ 8) :
    stock (raw (reattached quantity)) controller - stock (raw peace) controller = 4 - quantity ∧
      stock (raw (reattached quantity)) exposed = 4 + quantity ∧
      (raw (reattached quantity)).claims = (raw imposed).claims := by
  have accepted := (the_original_reimbursement_capacity quantity).mpr ⟨nonnegative, capacity⟩
  have owner := exact_native_material_controls.2.1
  have other := exact_native_material_controls.2.2.2.2.1
  have peace := exact_native_material_controls.1
  have separate : exposed ≠ controller := by decide
  unfold stock at owner other peace
  unfold reattached
  rw [raw_snoc, RawLaw.step, if_pos accepted]
  simp [RawLaw.paidStep, RawLaw.nextClaims, RawLaw.debit, RawLaw.credit, restore, request,
    stock, locate, flowAt, amount, separate, Ne.symm separate, owner, other, peace]
  ring

def actualRow : Threshold.Row Word :=
  ⟨imposed, stock (raw imposed) controller - stock (raw peace) controller,
    stock (raw peace) exposed - stock (raw imposed) exposed, by
      rw [exact_native_material_controls.2.2.2.1, exact_native_material_controls.2.2.2.2.1]
      decide +kernel⟩

theorem the_tight_rate_is_two_thirds_and_is_paid :
    Threshold.leastRate [actualRow] = 2 / 3 ∧
      stock (raw (reattached (Threshold.leastRate [actualRow] * actualRow.shift))) controller =
        stock (raw peace) controller := by
  constructor
  · decide +kernel
  · decide +kernel

theorem reattaching_the_actual_fraction_eliminates_pressure_exactly_at_the_tight_rate
    (rate : ℚ) (nonnegative : 0 ≤ rate) (within : rate ≤ 1) :
    stock (raw (reattached (rate * actualRow.shift))) controller - stock (raw peace) controller =
        actualRow.atRate rate ∧
      (stock (raw (reattached (rate * actualRow.shift))) controller ≤ stock (raw peace) controller ↔
        Threshold.leastRate [actualRow] ≤ rate) := by
  have margin : actualRow.margin = 4 := by decide +kernel
  have shift : actualRow.shift = 6 := by decide +kernel
  have affordable : rate * actualRow.shift ≤ 8 := by rw [shift]; linarith
  have paid := (every_affordable_actual_reimbursement_has_the_exact_pressure
    (rate * actualRow.shift) (mul_nonneg nonnegative actualRow.shift_nonnegative) affordable).1
  rw [Threshold.Row.atRate, margin]
  refine ⟨paid, ?_⟩
  rw [← sub_nonpos, paid, shift, the_tight_rate_is_two_thirds_and_is_paid.1]
  constructor <;> intro bound <;> linarith

theorem above_actual_capacity_returns_the_typed_original_refusal
    (quantity : ℚ) (beyond : 8 < quantity) :
    (∃ refusal, Physical.resultAt input depth count 0 0
      (submitted (run imposed).1 (restore quantity)) = .refused refusal) ∧
      raw (reattached quantity) = raw imposed := by
  have refused : ¬ law.Valid (raw imposed) (restore quantity) :=
    fun proof => (not_le_of_gt beyond) ((the_original_reimbursement_capacity quantity).mp proof).2
  constructor
  · exact Compile.invalid_input_is_a_typed_refusal input depth count 0 0 _ _ refused
  · rw [reattached, raw_snoc, law.rejected_preserves_current _ _ refused]

theorem the_native_compiler_refuses_a_levy_without_its_paid_trigger :
    (∃ refusal, Physical.resultAt input depth count 0 0
      (submitted Physical.initial levy) = .refused refusal) ∧
      raw [levy] = cut ∧ principals (run [levy]).2 = principals openingNative := by
  have denied := one_old_policy_opens_exposure_only_after_paid_destruction.1
  have empty : raw [] = cut := the_native_cut_reads_the_original_cut
  refine ⟨Compile.invalid_input_is_a_typed_refusal input depth count 0 0 _ _
    (by
      change ¬ law.Valid (Actual.initial input depth count).raw levy
      rwa [the_native_cut_reads_the_original_cut]), ?_, by decide +kernel⟩
  rw [show [levy] = [] ++ [levy] from rfl, raw_snoc, empty]
  exact law.rejected_preserves_current _ _ denied

theorem a_second_settlement_cannot_pay_the_old_row_twice :
    (∃ refusal, Physical.resultAt input depth count 0 0
      (submitted (run imposed).1 settle) = .refused refusal) ∧
      raw (imposed ++ [settle]) = raw imposed ∧
      principals (run (imposed ++ [settle])).2 = principals (run imposed).2 := by
  have denied : ¬ law.Valid (raw imposed) settle := by decide +kernel
  refine ⟨Compile.invalid_input_is_a_typed_refusal input depth count 0 0 _ _ denied, ?_, by decide +kernel⟩
  rw [raw_snoc, law.rejected_preserves_current _ _ denied]

#print axioms every_affordable_actual_reimbursement_has_the_exact_pressure
#print axioms the_tight_rate_is_two_thirds_and_is_paid
#print axioms reattaching_the_actual_fraction_eliminates_pressure_exactly_at_the_tight_rate
#print axioms above_actual_capacity_returns_the_typed_original_refusal
#print axioms the_native_compiler_refuses_a_levy_without_its_paid_trigger
#print axioms a_second_settlement_cannot_pay_the_old_row_twice

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers
