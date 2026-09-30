import H0mework.Arithmetic.Muntz.CoPoissonMuntzDirichletSource
import H0mework.Arithmetic.BurnolPhysical.EvenFourierSource

/-!
# Burnol additive co-sum and the reciprocal log chart

The existing `coPoissonLogOrbitEnergyMap` is a logarithmic half-density
realization of the modified integer-comb remainder.  It is not Burnol's
additive co-sum.

This file constructs the additive object first.  Starting from the concrete
even Schwartz annulus `burnolEvenAnnulusSchwartz`, its reciprocal source is

`g(t) = |t|⁻¹ φ(t⁻¹)`.

The source is even and vanishes on a neighbourhood of the origin.  Its
positive-integer additive co-sum is normalized by half of the full-line
integer-comb integral.  For nonzero positive `t`, the exact reciprocal
identity identifies the modified full-line remainder at scale `t⁻¹` with
`2t` times this additive co-sum.  Recharting `t = exp (-x)` then gives the
pointwise bridge to the existing log half-density, without asserting an
`L²`, Fourier, or physical-face landing.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped SchwartzMap ENNReal

noncomputable section

/-- The additive source paired with the concrete even Schwartz annulus by
reciprocal inversion.  The value at the origin is fixed independently, not
obtained from a spectral coordinate or a zero. -/
def burnolAdditiveAnnulusSource (t : ℝ) : ℂ :=
  if t = 0 then 0
  else ((|t| : ℝ) : ℂ)⁻¹ * burnolEvenAnnulusSchwartz t⁻¹

@[simp] theorem burnolAdditiveAnnulusSource_zero :
    burnolAdditiveAnnulusSource 0 = 0 := by
  simp [burnolAdditiveAnnulusSource]

theorem burnolAdditiveAnnulusSource_even (t : ℝ) :
    burnolAdditiveAnnulusSource (-t) =
      burnolAdditiveAnnulusSource t := by
  by_cases zero : t = 0
  · simp [zero]
  · simp only [burnolAdditiveAnnulusSource, neg_eq_zero, zero,
      ↓reduceIte, abs_neg, inv_neg]
    rw [burnolEvenAnnulusSchwartz_even]

/-- The reciprocal annulus has an actual open gap around the origin.  The
radius `1` is a convenient strict subradius of its exact inner radius `4/3`.
-/
theorem burnolAdditiveAnnulusSource_zero_of_abs_le_one
    {t : ℝ} (inside : |t| ≤ 1) :
    burnolAdditiveAnnulusSource t = 0 := by
  by_cases zero : t = 0
  · simp [zero]
  · have absPositive : 0 < |t| := abs_pos.mpr zero
    have inverseOne : (1 : ℝ) ≤ |t|⁻¹ :=
      (one_le_inv₀ absPositive).mpr inside
    have inverseOuter : (3 / 4 : ℝ) ≤ |t⁻¹| := by
      rw [abs_inv]
      linarith
    have inverseOuterNeg : (3 / 4 : ℝ) ≤ |-t⁻¹| := by
      simpa only [abs_neg] using inverseOuter
    have annulusZero : burnolEvenAnnulusSchwartz t⁻¹ = 0 := by
      simp only [burnolEvenAnnulusSchwartz, add_apply,
        burnolAnnulusSchwartzReflection_apply,
        burnolAnnulusSchwartz_apply]
      rw [burnolAnnulusBump_zero_of_three_quarters_le_abs inverseOuter,
        burnolAnnulusBump_zero_of_three_quarters_le_abs inverseOuterNeg]
      norm_num
    rw [burnolAdditiveAnnulusSource, if_neg zero, annulusZero, mul_zero]

/-- The correction in the full-line integer-comb normalization.  It is named
only as a normalization here: identifying it with a separately defined
right-Mellin integral of `burnolAdditiveAnnulusSource` requires its own
change-of-variables theorem. -/
def burnolAdditiveNormalization : ℂ :=
  (1 / 2 : ℂ) * ∫ x : ℝ, burnolEvenAnnulusSchwartz x

/-- Burnol's additive co-sum for the concrete reciprocal annulus, using the
strictly equivalent full-line integer-comb normalization. -/
def burnolAdditiveCoSum (t : ℝ) : ℂ :=
  (∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolAdditiveAnnulusSource (t / (n + 1 : ℕ))) -
    burnolAdditiveNormalization

theorem burnolAdditiveCoSum_even (t : ℝ) :
    burnolAdditiveCoSum (-t) = burnolAdditiveCoSum t := by
  unfold burnolAdditiveCoSum
  congr 1
  apply tsum_congr
  intro n
  rw [neg_div, burnolAdditiveAnnulusSource_even]

/-- The additive co-sum is literally constant on the position gap. -/
theorem burnolAdditiveCoSum_eq_neg_normalization_of_abs_le_one
    {t : ℝ} (inside : |t| ≤ 1) :
    burnolAdditiveCoSum t = -burnolAdditiveNormalization := by
  unfold burnolAdditiveCoSum
  have summandsZero : (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolAdditiveAnnulusSource (t / (n + 1 : ℕ))) = 0 := by
    funext n
    rw [burnolAdditiveAnnulusSource_zero_of_abs_le_one]
    · simp
    · have castAbs : |((n + 1 : ℕ) : ℝ)| = (n + 1 : ℕ) :=
        abs_of_nonneg (Nat.cast_nonneg (n + 1))
      rw [abs_div, castAbs]
      apply (div_le_one₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
      exact inside.trans (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  rw [summandsZero]
  have zeroTsum : tsum (0 : ℕ → ℂ) = 0 := tsum_zero
  rw [zeroTsum, zero_sub]

/-- Evaluation of one additive summand through the reciprocal Schwartz
source. -/
theorem burnolAdditiveAnnulusSource_div_nat
    {t : ℝ} (positive : 0 < t) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ)⁻¹ *
        burnolAdditiveAnnulusSource (t / (n + 1 : ℕ)) =
      (t : ℂ)⁻¹ * burnolEvenAnnulusSchwartz
        ((n + 1 : ℕ) * t⁻¹) := by
  have natPositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have quotientPositive : 0 < t / (n + 1 : ℕ) :=
    div_pos positive natPositive
  have quotientNe : t / (n + 1 : ℕ) ≠ 0 := quotientPositive.ne'
  rw [burnolAdditiveAnnulusSource, if_neg quotientNe,
    abs_of_pos quotientPositive]
  have argumentEq : (t / ((n + 1 : ℕ) : ℝ))⁻¹ =
      ((n + 1 : ℕ) : ℝ) * t⁻¹ := by
    field_simp [positive.ne', Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]
  rw [argumentEq]
  push_cast
  field_simp [positive.ne', Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

/-- The additive series is an actual summable series.  This is transported
from the already proved nonzero-integer Schwartz theta summability through
the reciprocal term equality, so no `tsum`-of-a-nonsummable-family convention
enters the co-sum. -/
theorem burnolAdditiveCoSum_summable_of_pos
    {t : ℝ} (positive : 0 < t) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolAdditiveAnnulusSource (t / (n + 1 : ℕ))) := by
  let positiveIndex : ℕ → {n : ℤ // n ≠ 0} := fun n =>
    ⟨(n.succ : ℤ), Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n)⟩
  have positiveIndex_injective : Function.Injective positiveIndex := by
    intro left right equality
    have valueEquality : (left.succ : ℤ) = (right.succ : ℤ) :=
      congrArg Subtype.val equality
    exact Nat.succ.inj (Int.ofNat_inj.mp valueEquality)
  have integerSummable :=
    coPoissonMuntzThetaNonzero_summable burnolEvenAnnulusSchwartz
      (inv_ne_zero positive.ne')
  have positiveSummable : Summable (fun n : ℕ =>
      burnolEvenAnnulusSchwartz
        (t⁻¹ * ((positiveIndex n).1 : ℝ))) :=
    integerSummable.comp_injective positiveIndex_injective
  have reorderedSummable : Summable (fun n : ℕ =>
      burnolEvenAnnulusSchwartz (((n + 1 : ℕ) : ℝ) * t⁻¹)) := by
    refine positiveSummable.congr ?_
    intro n
    congr 1
    simp only [positiveIndex, Nat.cast_succ, Int.cast_add, Int.cast_one,
      Int.cast_natCast]
    ring
  have scaledSummable := Summable.mul_left (t : ℂ)⁻¹ reorderedSummable
  exact scaledSummable.congr fun n =>
    (burnolAdditiveAnnulusSource_div_nat positive n).symm

/-- The same additive series is summable at every real position; evenness
reduces the negative half-line to the positive theorem and the origin is
identically zero termwise. -/
theorem burnolAdditiveCoSum_summable (t : ℝ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolAdditiveAnnulusSource (t / (n + 1 : ℕ))) := by
  rcases lt_trichotomy t 0 with negative | zero | positive
  · have source := burnolAdditiveCoSum_summable_of_pos (neg_pos.mpr negative)
    refine source.congr ?_
    intro n
    rw [neg_div, burnolAdditiveAnnulusSource_even]
  · subst t
    have summandsZero : (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
        burnolAdditiveAnnulusSource ((0 : ℝ) / (n + 1 : ℕ))) = 0 := by
      funext n
      simp
    rw [summandsZero]
    exact summable_zero
  · exact burnolAdditiveCoSum_summable_of_pos positive

/-- Positive and negative lattice points collapse to twice the positive
additive sum because the Schwartz-side annulus is even. -/
theorem burnolEvenAnnulusTheta_reciprocal_eq_additiveSum
    {t : ℝ} (positive : 0 < t) :
    coPoissonMuntzThetaNonzero burnolEvenAnnulusSchwartz t⁻¹ =
      ((2 * t : ℝ) : ℂ) *
        ∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ *
          burnolAdditiveAnnulusSource (t / (n + 1 : ℕ)) := by
  rw [coPoissonMuntzThetaNonzero_eq_positive_tsum
    burnolEvenAnnulusSchwartz (inv_ne_zero positive.ne')]
  rw [← (burnolAdditiveCoSum_summable_of_pos positive).tsum_mul_left]
  apply tsum_congr
  intro n
  rw [burnolAdditiveAnnulusSource_div_nat positive n]
  unfold coPoissonMuntzEvenSource
  rw [burnolEvenAnnulusSchwartz_even]
  push_cast
  field_simp [positive.ne']
  ring

/-- Exact full-line normalization law.  This is the first typed bridge which
distinguishes the additive co-sum from the existing modified-Poisson
half-density. -/
theorem coPoissonMuntzScaleRemainder_reciprocal_eq_additiveCoSum
    {t : ℝ} (positive : 0 < t) :
    coPoissonMuntzScaleRemainder burnolEvenAnnulusSchwartz t⁻¹ =
      ((2 * t : ℝ) : ℂ) * burnolAdditiveCoSum t := by
  rw [coPoissonMuntzScaleRemainder_eq burnolEvenAnnulusSchwartz
    (inv_pos.mpr positive)]
  rw [burnolEvenAnnulusTheta_reciprocal_eq_additiveSum positive]
  unfold burnolAdditiveCoSum burnolAdditiveNormalization
  rw [Complex.real_smul]
  push_cast
  field_simp [positive.ne']

/-- Generic pointwise link between the modified-Poisson scale remainder and
the already existing logarithmic half-density chart. -/
theorem coPoissonLogOrbitMap_log_eq_scaleRemainder
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (positive : 0 < scale) :
    coPoissonLogOrbitMap test (Real.log scale) =
      (scale : ℂ) ^ (1 / 2 : ℂ) *
        coPoissonMuntzScaleRemainder test scale := by
  rw [coPoissonLogOrbitMap_nonzero_formula, Real.exp_log positive]
  rw [coPoissonMuntzScaleRemainder_eq test positive]
  congr 2
  rw [Real.exp_neg, Real.exp_log positive]

/-- Reciprocal/log-chart identity: at `t > 0` the existing log half-density
is the reciprocal recharting of the additive co-sum, with its half-density
weight left explicit. -/
theorem coPoissonLogOrbitMap_reciprocal_eq_additiveCoSum
    {t : ℝ} (positive : 0 < t) :
    coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (Real.log t⁻¹) =
      (t⁻¹ : ℂ) ^ (1 / 2 : ℂ) *
        (((2 * t : ℝ) : ℂ) * burnolAdditiveCoSum t) := by
  rw [coPoissonLogOrbitMap_log_eq_scaleRemainder
      burnolEvenAnnulusSchwartz (inv_pos.mpr positive),
    coPoissonMuntzScaleRemainder_reciprocal_eq_additiveCoSum positive]
  norm_num

/-- Direct same-position consumer: inside the additive gap, local constancy
and the reciprocal log-half-density identity are simultaneously available.
No `L²`, Fourier-side constant law, or physical landing is a premise. -/
theorem burnolAdditivePositionAndReciprocalReadback
    {t : ℝ} (positive : 0 < t) (inside : |t| ≤ 1) :
    burnolAdditiveCoSum t = -burnolAdditiveNormalization ∧
      coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (Real.log t⁻¹) =
        (t⁻¹ : ℂ) ^ (1 / 2 : ℂ) *
          (((2 * t : ℝ) : ℂ) * burnolAdditiveCoSum t) :=
  ⟨burnolAdditiveCoSum_eq_neg_normalization_of_abs_le_one inside,
    coPoissonLogOrbitMap_reciprocal_eq_additiveCoSum positive⟩

end

end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
