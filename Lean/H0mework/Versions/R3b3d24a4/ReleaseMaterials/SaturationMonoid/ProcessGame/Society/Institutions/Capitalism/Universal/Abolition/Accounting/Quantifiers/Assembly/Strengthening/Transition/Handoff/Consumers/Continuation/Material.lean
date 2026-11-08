import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Accumulation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Actual Material.Continuation

noncomputable section

def gain (bearer good : Bool) : ℚ := if bearer = true ∧ good = false then 17 else 0

theorem gain_nonnegative (bearer good : Bool) : 0 ≤ gain bearer good := by
  cases bearer <;> cases good <;> decide +kernel

theorem the_public_law_is_time_independent : publicLaw.TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem the_public_law_is_reserve_insensitive : publicLaw.ReserveInsensitive :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem the_paid_word_earns_only_its_actual_material_gain :
    (publicLaw.execute opening 0 period).final = opening.addReserve gain := by
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

private theorem original_period_is_shared (members : List Bool) :
    SharedPeriod checkInput opening members period := by
  have paid := original_guard opening opening members (Or.inl rfl)
  exact ⟨paid.2.2.1, paid.2.2.2.1, fun _ _ _ _ _ => rfl, trivial⟩

private theorem original_material_is_valid : ∀ item ∈ publicLaw.rawItems opening period,
    publicLaw.Valid item.before item.request :=
  fun item present => ((original_guard opening opening [] (Or.inl rfl)).2.2.1 item present).1

/-- This is the material restriction of the installed word. The first
two periods are already present in the paid handoff. -/
def materialAt (n : Nat) : Raw :=
  (repeatPeriod checkInput opening period).currentAt (n + 2)

theorem material_starts_at_the_paid_handoff : materialAt 0 = secondRaw := rfl

theorem material_successor (n : Nat) : materialAt (n + 1) = publicLaw.next (materialAt n) period := rfl

theorem each_material_restriction_checks_the_original_period (origin : Raw) (members : List Bool) (n : Nat) :
    Abolition.Review.Guarded.Checks checkInput origin (materialAt n) members period := by
  have base := original_guard origin opening members (Or.inl rfl)
  exact ⟨base.1,
    productive_period_keeps_original_need_floor checkInput the_public_law_is_time_independent
      the_public_law_is_reserve_insensitive opening period gain gain_nonnegative origin members
      the_paid_word_earns_only_its_actual_material_gain original_material_is_valid base.2.1 (n + 2),
    productive_shared_period_generates_every_paid_period checkInput the_public_law_is_time_independent
      the_public_law_is_reserve_insensitive opening period gain gain_nonnegative members
      the_paid_word_earns_only_its_actual_material_gain (original_period_is_shared members) (n + 2)⟩

theorem each_material_restriction_has_exact_stock_and_claims (n : Nat) :
    (∀ bearer good, (materialAt n).stock bearer good =
      opening.stock bearer good + ((n + 2 : Nat) : ℚ) * gain bearer good) ∧
      (materialAt n).claims = opening.claims :=
  (productive_period_exact_resources checkInput the_public_law_is_time_independent
    the_public_law_is_reserve_insensitive opening period gain gain_nonnegative
    the_paid_word_earns_only_its_actual_material_gain original_material_is_valid (n + 2)).imp_right And.left

theorem material_has_its_actual_clock (n : Nat) : (materialAt n).clock = 6 + (n : ℚ) := by
  induction n with
  | zero =>
    rw [material_starts_at_the_paid_handoff]
    decide +kernel
  | succ n prior =>
    rw [material_successor]
    change (materialAt n).clock + max 0 (1 : ℚ) = _
    rw [prior, max_eq_right zero_le_one, Nat.cast_add, Nat.cast_one]
    ring

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
