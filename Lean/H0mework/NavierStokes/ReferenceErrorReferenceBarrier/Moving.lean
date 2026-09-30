import H0mework.NavierStokes.ReferenceErrorReferenceBarrier.Cubic

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceBarrier

open Set MeasureTheory

/-- A differentiable moving barrier bounds the continuous cubic integral
subsolution. No derivative of the controlled field is assumed. -/
theorem cubic_moving_barrier {f A R barrier derivative : Real → Real} {a b κ : Real}
    (fieldContinuous : ContinuousOn f (Icc a b))
    (rateContinuous : ContinuousOn A (Icc a b))
    (inputContinuous : ContinuousOn R (Icc a b))
    (derivativeContinuous : ContinuousOn derivative (Icc a b))
    (barrierDerivative : ∀ t ∈ Icc a b, HasDerivAt barrier (derivative t) t)
    (increments : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      f t - f s ≤ ∫ u in s..t, κ * f u ^ 3 + A u * f u + R u)
    (initial : f a ≤ barrier a)
    (inward : ∀ t ∈ Icc a b, κ * barrier t ^ 3 + A t * barrier t + R t ≤ derivative t) :
    ∀ t ∈ Icc a b, f t ≤ barrier t := by
  have barrierContinuous : ContinuousOn barrier (Icc a b) :=
    fun t within => (barrierDerivative t within).continuousAt.continuousWithinAt
  let growth := fun t => κ * f t ^ 3 + A t * f t + R t
  let coefficient := fun t => κ * (f t ^ 2 + f t * barrier t + barrier t ^ 2) + A t
  have growthContinuous : ContinuousOn growth (Icc a b) :=
    (((fieldContinuous.pow 3).const_mul κ).add (rateContinuous.mul fieldContinuous)).add inputContinuous
  have coefficientContinuous : ContinuousOn coefficient (Icc a b) :=
    ((((fieldContinuous.pow 2).add (fieldContinuous.mul barrierContinuous)).add
      (barrierContinuous.pow 2)).const_mul κ).add rateContinuous
  have compared := cubic_barrier (κ := 0) (B := 0) (R := fun _ => 0)
    (f := fun t => f t - barrier t) (fieldContinuous.sub barrierContinuous)
    coefficientContinuous continuousOn_const (fun s sWithin t tWithin forward => by
      have subset : uIcc s t ⊆ Icc a b := by
        rw [uIcc_of_le forward]
        exact Icc_subset_Icc sWithin.1 tWithin.2
      have growthIntegrable : IntervalIntegrable growth volume s t :=
        (growthContinuous.mono subset).intervalIntegrable
      have derivativeIntegrable : IntervalIntegrable derivative volume s t :=
        (derivativeContinuous.mono subset).intervalIntegrable
      have remainderIntegrable : IntervalIntegrable (fun u => coefficient u * (f u - barrier u)) volume s t :=
        ((coefficientContinuous.mul (fieldContinuous.sub barrierContinuous)).mono subset).intervalIntegrable
      have barrierIntegral : (∫ u in s..t, derivative u) = barrier t - barrier s :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun u within => barrierDerivative u (subset within)) derivativeIntegrable
      simp only [zero_mul, zero_add, add_zero]
      calc
        (f t - barrier t) - (f s - barrier s) ≤
            (∫ u in s..t, growth u) - ∫ u in s..t, derivative u := by
          rw [barrierIntegral]
          linarith [increments s sWithin t tWithin forward]
        _ = ∫ u in s..t, growth u - derivative u :=
          (intervalIntegral.integral_sub growthIntegrable derivativeIntegrable).symm
        _ ≤ ∫ u in s..t, coefficient u * (f u - barrier u) := by
          apply intervalIntegral.integral_mono_on forward
            (growthIntegrable.sub derivativeIntegrable) remainderIntegrable
          intro u within
          have withinWhole : u ∈ Icc a b := ⟨sWithin.1.trans within.1, within.2.trans tWithin.2⟩
          have factorization : growth u - derivative u = coefficient u * (f u - barrier u) +
              (κ * barrier u ^ 3 + A u * barrier u + R u - derivative u) := by
            dsimp only [growth, coefficient]
            ring
          rw [factorization]
          linarith [inward u withinWhole])
    (by linarith) (by intro t _; simp)
  intro t within
  have bound := compared t within
  linarith

end SaturationMonoid.NavierStokes.ReferenceBarrier
