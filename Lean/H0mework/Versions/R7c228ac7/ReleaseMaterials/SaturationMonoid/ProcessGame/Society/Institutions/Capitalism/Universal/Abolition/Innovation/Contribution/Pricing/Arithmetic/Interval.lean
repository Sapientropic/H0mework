import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.RiskMath

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic

def canonicalTransfer (lower upper : ℚ) : ℚ :=
  if 0 < lower then lower else if upper < 0 then upper else 0

theorem both_accounts_meet_their_baselines_iff
    (providerOutside providerIncome payerOutside payerIncome transfer : ℚ) :
    (providerOutside ≤ providerIncome + transfer ∧ payerOutside ≤ payerIncome - transfer) ↔
      providerOutside - providerIncome ≤ transfer ∧ transfer ≤ payerIncome - payerOutside := by
  constructor <;> rintro ⟨first, second⟩ <;> constructor <;> linarith

theorem a_jointly_safe_transfer_exists_iff (lower upper : ℚ) :
    (∃ transfer : ℚ, lower ≤ transfer ∧ transfer ≤ upper) ↔ lower ≤ upper := by
  constructor
  · rintro ⟨transfer, first, second⟩
    exact le_trans first second
  · intro compatible
    exact ⟨lower, le_refl _, compatible⟩

theorem canonical_transfer_is_in_the_interval (lower upper : ℚ) (compatible : lower ≤ upper) :
    lower ≤ canonicalTransfer lower upper ∧ canonicalTransfer lower upper ≤ upper := by
  unfold canonicalTransfer
  split
  · exact ⟨le_refl _, compatible⟩
  · split
    · exact ⟨compatible, le_refl _⟩
    · constructor <;> linarith

theorem canonical_transfer_has_minimal_absolute_payment (lower upper transfer : ℚ)
    (within : lower ≤ transfer ∧ transfer ≤ upper) :
    |canonicalTransfer lower upper| ≤ |transfer| := by
  unfold canonicalTransfer
  split
  · rename_i positive
    have nonnegative : 0 ≤ transfer := le_trans positive.le within.1
    rw [abs_of_pos positive, abs_of_nonneg nonnegative]
    exact within.1
  · split
    · rename_i negative
      have nonpositive : transfer ≤ 0 := le_trans within.2 negative.le
      rw [abs_of_neg negative, abs_of_nonpos nonpositive]
      linarith [within.2]
    · simp only [abs_zero]
      exact abs_nonneg _

theorem any_different_safe_transfer_has_strictly_larger_absolute_payment
    (lower upper transfer : ℚ) (within : lower ≤ transfer ∧ transfer ≤ upper)
    (different : transfer ≠ canonicalTransfer lower upper) :
    |canonicalTransfer lower upper| < |transfer| := by
  by_cases positive : 0 < lower
  · simp only [canonicalTransfer, if_pos positive] at different ⊢
    have nonnegative : 0 ≤ transfer := le_trans positive.le within.1
    rw [abs_of_pos positive, abs_of_nonneg nonnegative]
    exact lt_of_le_of_ne within.1 (Ne.symm different)
  · by_cases negative : upper < 0
    · simp only [canonicalTransfer, if_neg positive, if_pos negative] at different ⊢
      have nonpositive : transfer ≤ 0 := le_trans within.2 negative.le
      rw [abs_of_neg negative, abs_of_nonpos nonpositive]
      have strict : transfer < upper := lt_of_le_of_ne within.2 different
      linarith
    · simp only [canonicalTransfer, if_neg positive, if_neg negative] at different ⊢
      simpa only [abs_zero] using abs_pos.mpr different

theorem every_nonzero_canonical_payment_binds_an_original_baseline
    (providerOutside providerIncome payerOutside payerIncome : ℚ)
    (nonzero : canonicalTransfer (providerOutside - providerIncome) (payerIncome - payerOutside) ≠ 0) :
    providerIncome + canonicalTransfer (providerOutside - providerIncome) (payerIncome - payerOutside) =
        providerOutside ∨
      payerIncome - canonicalTransfer (providerOutside - providerIncome) (payerIncome - payerOutside) =
        payerOutside := by
  by_cases positive : 0 < providerOutside - providerIncome
  · simp only [canonicalTransfer, if_pos positive]
    left; ring
  · by_cases negative : payerIncome - payerOutside < 0
    · simp only [canonicalTransfer, if_neg positive, if_pos negative]
      right; ring
    · simp only [canonicalTransfer, if_neg positive, if_neg negative] at nonzero
      exact False.elim (nonzero rfl)

theorem an_added_loading_is_extra_payment_or_breaks_the_interval
    (lower upper loading : ℚ) (positive : 0 < loading) :
    ¬ (lower ≤ canonicalTransfer lower upper + loading ∧ canonicalTransfer lower upper + loading ≤ upper) ∨
      |canonicalTransfer lower upper| < |canonicalTransfer lower upper + loading| := by
  by_cases within : lower ≤ canonicalTransfer lower upper + loading ∧ canonicalTransfer lower upper + loading ≤ upper
  · exact Or.inr (any_different_safe_transfer_has_strictly_larger_absolute_payment
      lower upper _ within (by linarith))
  · exact Or.inl within

theorem every_transfer_has_an_exact_source_interval_disposition
    (lower upper transfer : ℚ) :
    (transfer = canonicalTransfer lower upper) ∨
      (lower ≤ transfer ∧ transfer ≤ upper ∧ |canonicalTransfer lower upper| < |transfer|) ∨
      transfer < lower ∨ upper < transfer := by
  by_cases same : transfer = canonicalTransfer lower upper
  · exact Or.inl same
  · right
    by_cases first : lower ≤ transfer
    · by_cases second : transfer ≤ upper
      · exact Or.inl ⟨first, second,
          any_different_safe_transfer_has_strictly_larger_absolute_payment lower upper transfer ⟨first, second⟩ same⟩
      · exact Or.inr (Or.inr (lt_of_not_ge second))
    · exact Or.inr (Or.inl (lt_of_not_ge first))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic
