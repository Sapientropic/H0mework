import H0mework.NavierStokes.ReferenceErrorReferenceBarrier.Slope

/-! Continuous cubic Volterra barriers, with an integrable-energy adapter. -/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceBarrier

open Set Filter MeasureTheory

/-- A continuous integral subsolution cannot cross a constant supersolution of the cubic law.
The exact polynomial factorization makes positivity assumptions on f, κ, and B unnecessary. -/
theorem cubic_barrier {f A R : Real → Real} {a b κ B : Real}
    (fieldContinuous : ContinuousOn f (Icc a b))
    (rateContinuous : ContinuousOn A (Icc a b))
    (inputContinuous : ContinuousOn R (Icc a b))
    (increments : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      f t - f s ≤ ∫ u in s..t, κ * f u ^ 3 + A u * f u + R u)
    (initial : f a ≤ B)
    (barrier : ∀ t ∈ Icc a b, κ * B ^ 3 + A t * B + R t ≤ 0) :
    ∀ t ∈ Icc a b, f t ≤ B := by
  by_cases ordered : a ≤ b
  · let g : Real → Real := fun t => κ * f t ^ 3 + A t * f t + R t
    let coefficient : Real → Real := fun t => κ * (f t ^ 2 + f t * B + B ^ 2) + A t
    have gContinuous : ContinuousOn g (Icc a b) :=
      (((fieldContinuous.pow 3).const_mul κ).add (rateContinuous.mul fieldContinuous)).add inputContinuous
    have coefficientContinuous : ContinuousOn coefficient (Icc a b) :=
      ((((fieldContinuous.pow 2).add (fieldContinuous.mul continuousOn_const)).add continuousOn_const).const_mul κ).add
        rateContinuous
    obtain ⟨K, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn coefficientContinuous
    have slope := liminf_slope_of_increments ordered gContinuous increments
    have fenced (epsilon : Real) (positive : 0 < epsilon) (t : Real) (within : t ∈ Icc a b) :
        f t ≤ B + epsilon * Real.exp ((K + 1) * (t - a)) := by
      apply image_le_of_liminf_slope_right_lt_deriv_boundary
        (B := fun u => B + epsilon * Real.exp ((K + 1) * (u - a)))
        (B' := fun u => (K + 1) * epsilon * Real.exp ((K + 1) * (u - a))) fieldContinuous slope
      · simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
        linarith
      · intro u
        apply ((hasDerivAt_const u B).add
          (((((hasDerivAt_id u).sub_const a).const_mul (K + 1)).exp).const_mul epsilon)).congr_deriv
        dsimp
        ring
      · intro u member contact
        have gapPositive : 0 < epsilon * Real.exp ((K + 1) * (u - a)) :=
          mul_pos positive (Real.exp_pos _)
        have coefficientBound : coefficient u ≤ K := (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using bounded u (Ico_subset_Icc_self member))
        have factorization : g u = coefficient u * (f u - B) + (κ * B ^ 3 + A u * B + R u) := by
          dsimp [g, coefficient]
          ring
        have productBound := mul_le_mul_of_nonneg_right coefficientBound
          (show 0 ≤ f u - B by rw [contact]; linarith)
        rw [factorization]
        have inward := barrier u (Ico_subset_Icc_self member)
        rw [contact] at productBound ⊢
        nlinarith
      · exact within
    intro t within
    apply le_of_forall_pos_le_add
    intro epsilon positive
    have comparison := fenced (epsilon / Real.exp ((K + 1) * (t - a)))
      (div_pos positive (Real.exp_pos _)) t within
    simpa only [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos _))] using comparison
  · intro t within
    exact False.elim (ordered (within.1.trans within.2))

/-- Exact energy identities and an integrable a.e. power upper bound generate every interval increment. -/
theorem increments_of_energy {f power growth : Real → Real} {a b : Real} (ordered : a ≤ b)
    (powerIntegrable : IntervalIntegrable power volume a b)
    (growthContinuous : ContinuousOn growth (Icc a b))
    (energy : ∀ t ∈ Icc a b, (∫ u in a..t, power u) = f t - f a)
    (bound : power ≤ᵐ[volume.restrict (Icc a b)] growth) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → f t - f s ≤ ∫ u in s..t, growth u := by
  intro s sWithin t tWithin forward
  have asSubset : uIcc a s ⊆ uIcc a b := by
    rw [uIcc_of_le sWithin.1, uIcc_of_le ordered]
    exact Icc_subset_Icc le_rfl sWithin.2
  have stSubset : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le forward, uIcc_of_le ordered]
    exact Icc_subset_Icc sWithin.1 tWithin.2
  have localPower := powerIntegrable.mono_set stSubset
  have adjacent := intervalIntegral.integral_add_adjacent_intervals (powerIntegrable.mono_set asSubset) localPower
  rw [energy s sWithin, energy t tWithin] at adjacent
  have representation : f t - f s = ∫ u in s..t, power u := by linarith
  rw [representation]
  have localGrowth : IntervalIntegrable growth volume s t :=
    (growthContinuous.mono (by rw [uIcc_of_le forward]; exact Icc_subset_Icc sWithin.1 tWithin.2)).intervalIntegrable
  apply intervalIntegral.integral_mono_ae_restrict forward localPower localGrowth
  exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc sWithin.1 tWithin.2) bound

end SaturationMonoid.NavierStokes.ReferenceBarrier
