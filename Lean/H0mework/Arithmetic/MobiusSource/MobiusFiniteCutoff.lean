import H0mework.Arithmetic.MobiusSource.CompactMobiusInverse

/-! # Finite centred divisor reconstruction fixed by the quarter gap -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Set
open scoped ArithmeticFunction BigOperators

noncomputable section

def burnolCenteredMobiusSummand (raw : ℝ → ℂ) (t : ℝ) (m : ℕ+) : ℂ :=
  (ArithmeticFunction.moebius (m : ℕ) : ℂ) * (((m : ℕ) : ℂ)⁻¹ *
    (raw (t / (m : ℕ)) - raw 0))

def burnolCenteredMobiusCutoff (t : ℝ) : ℕ := Nat.ceil (4 * |t|)

noncomputable def burnolCenteredMobiusCutoffFinset (t : ℝ) : Finset ℕ+ :=
  (show ({m : ℕ+ | (m : ℕ) < burnolCenteredMobiusCutoff t} : Set ℕ+).Finite by
    apply (Set.finite_lt_nat (burnolCenteredMobiusCutoff t)).preimage
    exact Set.injOn_of_injective PNat.coe_injective).toFinset

@[simp] theorem mem_burnolCenteredMobiusCutoffFinset (t : ℝ) (m : ℕ+) :
    m ∈ burnolCenteredMobiusCutoffFinset t ↔
      (m : ℕ) < burnolCenteredMobiusCutoff t := by
  simp [burnolCenteredMobiusCutoffFinset]

theorem burnolCenteredMobiusSummand_eq_zero_of_cutoff_le
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (t : ℝ) (m : ℕ+)
    (large : burnolCenteredMobiusCutoff t ≤ (m : ℕ)) :
    burnolCenteredMobiusSummand raw t m = 0 := by
  have mPositive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.property
  have scaledInside : |t / ((m : ℕ) : ℝ)| ≤ (1 / 4 : ℝ) := by
    rw [abs_div, abs_of_pos mPositive]
    apply (div_le_iff₀ mPositive).2
    have cutoffLe : 4 * |t| ≤ ((m : ℕ) : ℝ) :=
      (Nat.le_ceil (4 * |t|)).trans (by exact_mod_cast large)
    nlinarith
  rw [burnolCenteredMobiusSummand, quarterGap scaledInside, sub_self, mul_zero,
    mul_zero]

theorem burnolCenteredMobiusSummand_finiteSupport
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (t : ℝ) : Function.HasFiniteSupport (burnolCenteredMobiusSummand raw t) := by
  apply (burnolCenteredMobiusCutoffFinset t).finite_toSet.subset
  intro m termNe
  by_contra outside
  exact termNe (burnolCenteredMobiusSummand_eq_zero_of_cutoff_le raw quarterGap t m
    (Nat.le_of_not_gt (by simpa using outside)))

theorem burnolCenteredMobiusInverse_eq_cutoffSum
    (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (t : ℝ) :
    burnolCenteredMobiusInverse raw t =
      ∑ m ∈ burnolCenteredMobiusCutoffFinset t,
        burnolCenteredMobiusSummand raw t m := by
  change (∑' m : ℕ+, burnolCenteredMobiusSummand raw t m) = _
  rw [tsum_eq_sum (s := burnolCenteredMobiusCutoffFinset t)]
  intro m outside
  apply burnolCenteredMobiusSummand_eq_zero_of_cutoff_le raw quarterGap t m
  exact Nat.le_of_not_gt (by simpa using outside)

theorem burnolCompactCenteredMobiusInverse_eq_cutoffSum
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCenteredMobiusInverse (burnolCompactAdditiveCoSum source) t =
      ∑ m ∈ burnolCenteredMobiusCutoffFinset t,
        burnolCenteredMobiusSummand (burnolCompactAdditiveCoSum source) t m := by
  apply burnolCenteredMobiusInverse_eq_cutoffSum
  intro x inside
  rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source inside,
    burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source
      (t := 0) (by norm_num)]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
