import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Discrete
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Revision

open Source.Program PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
open OutstandingSource.History.NativeService

noncomputable section

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory)

abbrev actualBound := epochBound ready

private theorem real_clock (inputs : List (List Action)) (ordinal : Nat) :
    clockAt (actualBound ready) inputs ordinal = (actualBound ready).source.seed.initial.clock + ordinal := by
  simpa only [mul_one] using
    constant_source_duration_gives_the_literal_clock (actualBound ready) inputs 1
      (by decide) (fun _ => rfl) ordinal

theorem the_original_revision_bootstrap_preserves_every_unpaid_service
    (slot : (actualBound ready).source.Slot) : (frameAt (actualBound ready).source [] 2).payments slot = none := by
  cases payment : (frameAt (actualBound ready).source [] 2).payments slot with
  | none => rfl
  | some paid =>
    obtain ⟨positive, earlier, actual⟩ :=
      OutstandingSource.History.recorded_payment_is_own_actual (actualBound ready).source [] 2 slot paid payment
    have ordinal : paid = 1 := by omega
    have timely : ready.task.earliest ≤ clockAt (actualBound ready) [] paid := actual.1
    rw [ordinal, real_clock] at timely
    change (actualBound ready).source.seed.initial.clock + 2 ≤
      (actualBound ready).source.seed.initial.clock + (1 : ℚ) at timely
    linarith

theorem no_original_revision_can_complete_before_the_first_service_word :
    ¬ PaidAt (actualBound ready) [] [] := by
  have nonempty : ready.task.slots ≠ [] := by
    obtain ⟨slot, inside, _⟩ := ready.task.demand
    intro empty
    rw [empty] at inside
    exact List.not_mem_nil inside
  have positive : 0 < ready.task.slots.length := by
    cases original : ready.task.slots with
    | nil => exact (nonempty original).elim
    | cons _ _ => simp
  let slot : (actualBound ready).source.Slot := ⟨0, positive⟩
  exact (Issue.service slot (((serviceThread (actualBound ready) [] [] slot).native_live_iff_unpaid
    (actualBound ready).source).mpr (the_original_revision_bootstrap_preserves_every_unpaid_service ready slot))).refutes

private theorem one_word_has_the_installed_clock (word : List Action) :
    readClock (actualBound ready) [] [word] = (((ready.task.deadline : ℚ) : ℝ) : EReal) := by
  change (((clockAt (actualBound ready) [word] 3 : ℚ) : ℝ) : EReal) = _
  rw [real_clock]
  rfl

/-- The actual source-generated review window is tight exactly when an
original one-word continuation pays every service and releases authority.
The comparison includes every submitted continuation of that original
revision, including attempts outside the automatic compiler's menu. -/
theorem the_installed_revision_cutoff_is_tight_iff_first_service_can_pay_and_release :
    IsLeast (times (actualBound ready) []) (((ready.task.deadline : ℚ) : ℝ) : EReal) ↔
      ∃ word : List Action, PaidAt (actualBound ready) [] [word] := by
  constructor
  · intro tight
    obtain ⟨suffix, paid, same⟩ := tight.1
    have clockEq : readClock (actualBound ready) [] suffix = readClock (actualBound ready) [] [[]] :=
      same.trans (one_word_has_the_installed_clock ready []).symm
    have length : suffix.length = 1 := by
      apply le_antisymm
      · exact (constant_owned_duration_orders_cutoffs_by_paid_word_count (actualBound ready) [] suffix [[]]
          1 (by decide) (fun _ => rfl)).mp clockEq.le
      · exact (constant_owned_duration_orders_cutoffs_by_paid_word_count (actualBound ready) [] [[]] suffix
          1 (by decide) (fun _ => rfl)).mp clockEq.ge
    cases suffix with
    | nil => exact (no_original_revision_can_complete_before_the_first_service_word ready paid).elim
    | cons word later =>
      simp only [List.length_cons] at length
      have empty : later = [] := List.length_eq_zero_iff.mp (by omega)
      subst later
      exact ⟨word, paid⟩
  · rintro ⟨word, paid⟩
    have clock := one_word_has_the_installed_clock ready word
    refine ⟨⟨[word], paid, clock⟩, ?_⟩
    rintro _ ⟨suffix, complete, rfl⟩
    have size : [word].length ≤ suffix.length := by
      cases suffix with
      | nil => exact (no_original_revision_can_complete_before_the_first_service_word ready complete).elim
      | cons _ _ => simp
    rw [← clock]
    exact (constant_owned_duration_orders_cutoffs_by_paid_word_count (actualBound ready) [] [word] suffix
      1 (by decide) (fun _ => rfl)).mpr size

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Revision
