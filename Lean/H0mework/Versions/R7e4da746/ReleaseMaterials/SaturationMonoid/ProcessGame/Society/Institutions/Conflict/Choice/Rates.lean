import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice

section Rates

variable (admitted : Set ℝ) (pressure : ℝ → ℝ)

/-- The source decides which rates execute. The optimized comparison at an admitted rate
decides whether any strictly positive pressure remains. -/
def safeRates : Set ℝ :=
  { rate | 0 ≤ rate ∧ rate ≤ 1 ∧ rate ∈ admitted ∧ pressure rate ≤ 0 }

theorem safeRates_bddBelow : BddBelow (safeRates admitted pressure) :=
  ⟨0, fun _ safe => safe.1⟩

theorem inf_safeRates_le {rate : ℝ} (safe : rate ∈ safeRates admitted pressure) :
    sInf (safeRates admitted pressure) ≤ rate :=
  csInf_le (safeRates_bddBelow admitted pressure) safe

theorem every_smaller_admitted_rate_leaves_pressure {rate : ℝ} (nonnegative : 0 ≤ rate)
    (smaller : rate < sInf (safeRates admitted pressure)) (authorized : rate ∈ admitted)
    (someSafe : (safeRates admitted pressure).Nonempty) : 0 < pressure rate := by
  obtain ⟨feasible, safe⟩ := someSafe
  have underOne : rate ≤ 1 := smaller.le.trans ((inf_safeRates_le admitted pressure safe).trans safe.2.1)
  apply lt_of_not_ge
  intro suppressed
  exact (not_lt_of_ge (inf_safeRates_le admitted pressure ⟨nonnegative, underOne, authorized, suppressed⟩)) smaller

theorem no_safe_rate_iff_rejection_or_pressure :
    ¬ (safeRates admitted pressure).Nonempty ↔
      ∀ rate : ℝ, 0 ≤ rate → rate ≤ 1 →
        rate ∉ admitted ∨ (rate ∈ admitted ∧ 0 < pressure rate) := by
  classical
  constructor
  · intro unavailable rate nonnegative underOne
    by_cases accepted : rate ∈ admitted
    · exact .inr ⟨accepted, lt_of_not_ge fun suppressed =>
        unavailable ⟨rate, nonnegative, underOne, accepted, suppressed⟩⟩
    · exact .inl accepted
  · rintro unavailable ⟨rate, nonnegative, underOne, accepted, suppressed⟩
    rcases unavailable rate nonnegative underOne with rejected | persists
    · exact rejected accepted
    · exact (not_lt_of_ge suppressed) persists.2

inductive LeastRate : Prop
  | attained (actual : sInf (safeRates admitted pressure) ∈ safeRates admitted pressure)
  | approached (someSafe : (safeRates admitted pressure).Nonempty)
      (noMinimum : sInf (safeRates admitted pressure) ∉ safeRates admitted pressure)
      (near : ∀ ε > 0, ∃ rate ∈ safeRates admitted pressure,
        sInf (safeRates admitted pressure) < rate ∧ rate < sInf (safeRates admitted pressure) + ε)
  | blocked (each : ∀ rate : ℝ, 0 ≤ rate → rate ≤ 1 →
      rate ∉ admitted ∨ (rate ∈ admitted ∧ 0 < pressure rate))

/-- Exact resolution for arbitrary source admissions, including gaps and a refused full rate. -/
theorem resolve_least_safe_rate : LeastRate admitted pressure := by
  classical
  by_cases someSafe : (safeRates admitted pressure).Nonempty
  · by_cases attained : sInf (safeRates admitted pressure) ∈ safeRates admitted pressure
    · exact .attained attained
    · refine .approached someSafe attained fun ε positive => ?_
      obtain ⟨rate, safe, near⟩ := exists_lt_of_csInf_lt someSafe (lt_add_of_pos_right _ positive)
      exact ⟨rate, safe,
        lt_of_le_of_ne (inf_safeRates_le admitted pressure safe) (fun equal => attained (equal ▸ safe)), near⟩
  · exact .blocked ((no_safe_rate_iff_rejection_or_pressure admitted pressure).mp someSafe)

end Rates

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice
