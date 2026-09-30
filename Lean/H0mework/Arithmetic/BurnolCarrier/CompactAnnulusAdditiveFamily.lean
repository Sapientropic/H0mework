import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import H0mework.Arithmetic.BurnolCarrier.AdditiveFullEvenL2

/-!
# Additive co-Poisson family from compact annulus sources

This is the source-variable version of the previously fixed annulus
construction.  An even Schwartz test with actual inner and outer gaps is
sent first to its reciprocal additive co-sum and then, by the exact
exponential Jacobian, to full additive `L²`.  No logarithmic `L²` value is
relabelled as an additive-position value.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped ENNReal SchwartzMap

noncomputable section

/-- Actual compact annulus sources for the unscaled radius `1/4`. -/
def burnolCompactAnnulusSource : Submodule ℂ (SchwartzMap ℝ ℂ) where
  carrier := {test |
    (∀ x, test (-x) = test x) ∧
    (∀ x, |x| ≤ (1 / 4 : ℝ) → test x = 0) ∧
    (∀ x, (4 : ℝ) ≤ |x| → test x = 0)}
  zero_mem' := by simp
  add_mem' := by
    rintro left right ⟨leftEven, leftInner, leftOuter⟩
      ⟨rightEven, rightInner, rightOuter⟩
    exact ⟨fun x => by simp [leftEven x, rightEven x],
      fun x hx => by simp [leftInner x hx, rightInner x hx],
      fun x hx => by simp [leftOuter x hx, rightOuter x hx]⟩
  smul_mem' := by
    rintro coefficient test ⟨even, inner, outer⟩
    exact ⟨fun x => by simp [even x],
      fun x hx => by simp [inner x hx],
      fun x hx => by simp [outer x hx]⟩

theorem burnolCompactAnnulusSource_even
    (source : burnolCompactAnnulusSource) (x : ℝ) :
    source.1 (-x) = source.1 x :=
  source.2.1 x

/-- Reciprocal source in the additive coordinate. -/
def burnolCompactAdditiveSource
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  if t = 0 then 0 else ((|t| : ℝ) : ℂ)⁻¹ * source.1 t⁻¹

theorem burnolCompactAdditiveSource_even
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCompactAdditiveSource source (-t) =
      burnolCompactAdditiveSource source t := by
  by_cases zero : t = 0
  · simp [zero]
  · simp only [burnolCompactAdditiveSource, neg_eq_zero, zero,
      ↓reduceIte, abs_neg, inv_neg]
    rw [burnolCompactAnnulusSource_even]

theorem burnolCompactAdditiveSource_zero_of_abs_le_quarter
    (source : burnolCompactAnnulusSource) {t : ℝ}
    (inside : |t| ≤ (1 / 4 : ℝ)) :
    burnolCompactAdditiveSource source t = 0 := by
  by_cases zero : t = 0
  · simp [burnolCompactAdditiveSource, zero]
  · rw [burnolCompactAdditiveSource, if_neg zero,
      source.2.2.2 t⁻¹]
    · simp
    · rw [abs_inv]
      have positive : 0 < |t| := abs_pos.mpr zero
      rw [inv_eq_one_div]
      apply (le_div_iff₀ positive).mpr
      nlinarith

def burnolCompactAdditiveNormalization
    (source : burnolCompactAnnulusSource) : ℂ :=
  (1 / 2 : ℂ) * ∫ x : ℝ, source.1 x

def burnolCompactAdditiveCoSum
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  (∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolCompactAdditiveSource source (t / (n + 1 : ℕ))) -
    burnolCompactAdditiveNormalization source

theorem burnolCompactAdditiveCoSum_even
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCompactAdditiveCoSum source (-t) =
      burnolCompactAdditiveCoSum source t := by
  unfold burnolCompactAdditiveCoSum
  congr 1
  apply tsum_congr
  intro n
  rw [neg_div, burnolCompactAdditiveSource_even]

theorem burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
    (source : burnolCompactAnnulusSource) {t : ℝ}
    (inside : |t| ≤ (1 / 4 : ℝ)) :
    burnolCompactAdditiveCoSum source t =
      -burnolCompactAdditiveNormalization source := by
  unfold burnolCompactAdditiveCoSum
  have summandsZero : (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolCompactAdditiveSource source (t / (n + 1 : ℕ))) = 0 := by
    funext n
    rw [burnolCompactAdditiveSource_zero_of_abs_le_quarter]
    · simp
    · rw [abs_div]
      have denomAbs : |(((n + 1 : ℕ) : ℝ))| = (n + 1 : ℕ) :=
        abs_of_nonneg (Nat.cast_nonneg (n + 1))
      rw [denomAbs]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
      nlinarith [show (1 : ℝ) ≤ (n + 1 : ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)]
  rw [summandsZero]
  have zeroTsum : tsum (0 : ℕ → ℂ) = 0 := tsum_zero
  rw [zeroTsum, zero_sub]

theorem burnolCompactAdditiveSource_div_nat
    (source : burnolCompactAnnulusSource) {t : ℝ}
    (positive : 0 < t) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ)⁻¹ *
        burnolCompactAdditiveSource source (t / (n + 1 : ℕ)) =
      (t : ℂ)⁻¹ * source.1 (((n + 1 : ℕ) : ℝ) * t⁻¹) := by
  have natPositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have quotientPositive : 0 < t / (n + 1 : ℕ) := div_pos positive natPositive
  have quotientNe : t / (n + 1 : ℕ) ≠ 0 := quotientPositive.ne'
  rw [burnolCompactAdditiveSource, if_neg quotientNe,
    abs_of_pos quotientPositive]
  have argumentEq : (t / ((n + 1 : ℕ) : ℝ))⁻¹ =
      ((n + 1 : ℕ) : ℝ) * t⁻¹ := by
    field_simp [positive.ne', Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]
  rw [argumentEq]
  push_cast
  field_simp [positive.ne', Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

theorem burnolCompactAdditiveCoSum_summable_of_pos
    (source : burnolCompactAnnulusSource) {t : ℝ} (positive : 0 < t) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolCompactAdditiveSource source (t / (n + 1 : ℕ))) := by
  let positiveIndex : ℕ → {n : ℤ // n ≠ 0} := fun n =>
    ⟨(n.succ : ℤ), Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n)⟩
  have positiveIndex_injective : Function.Injective positiveIndex := by
    intro left right equality
    exact Nat.succ.inj (Int.ofNat_inj.mp (congrArg Subtype.val equality))
  have integerSummable :=
    coPoissonMuntzThetaNonzero_summable source.1
      (inv_ne_zero positive.ne')
  have positiveSummable : Summable (fun n : ℕ =>
      source.1 (t⁻¹ * ((positiveIndex n).1 : ℝ))) :=
    integerSummable.comp_injective positiveIndex_injective
  have reorderedSummable : Summable (fun n : ℕ =>
      source.1 (((n + 1 : ℕ) : ℝ) * t⁻¹)) := by
    refine positiveSummable.congr ?_
    intro n
    congr 1
    simp only [positiveIndex, Nat.cast_succ, Int.cast_add, Int.cast_one,
      Int.cast_natCast]
    ring
  exact (Summable.mul_left (t : ℂ)⁻¹ reorderedSummable).congr fun n =>
    (burnolCompactAdditiveSource_div_nat source positive n).symm

theorem burnolCompactAdditiveCoSum_summable
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolCompactAdditiveSource source (t / (n + 1 : ℕ))) := by
  rcases lt_trichotomy t 0 with negative | zero | positive
  · have base := burnolCompactAdditiveCoSum_summable_of_pos source
      (neg_pos.mpr negative)
    refine base.congr ?_
    intro n
    rw [neg_div, burnolCompactAdditiveSource_even]
  · subst t
    rw [show (fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹ *
        burnolCompactAdditiveSource source ((0 : ℝ) / (n + 1 : ℕ))) = 0 by
      funext n
      simp [burnolCompactAdditiveSource]]
    exact summable_zero
  · exact burnolCompactAdditiveCoSum_summable_of_pos source positive

theorem coPoissonMuntzScaleRemainder_reciprocal_eq_compactAdditiveCoSum
    (source : burnolCompactAnnulusSource) {t : ℝ} (positive : 0 < t) :
    coPoissonMuntzScaleRemainder source.1 t⁻¹ =
      (((2 * t : ℝ) : ℂ) * burnolCompactAdditiveCoSum source t) := by
  rw [coPoissonMuntzScaleRemainder_eq source.1 (inv_pos.mpr positive)]
  rw [coPoissonMuntzThetaNonzero_eq_positive_tsum source.1
    (inv_ne_zero positive.ne')]
  have sumEq :
      (∑' n : ℕ, coPoissonMuntzEvenSource source.1
        ((n + 1 : ℕ) * t⁻¹)) =
      ((2 * t : ℝ) : ℂ) *
        ∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ *
          burnolCompactAdditiveSource source (t / (n + 1 : ℕ)) := by
    rw [← (burnolCompactAdditiveCoSum_summable_of_pos source positive).tsum_mul_left]
    apply tsum_congr
    intro n
    rw [burnolCompactAdditiveSource_div_nat source positive]
    unfold coPoissonMuntzEvenSource
    rw [burnolCompactAnnulusSource_even]
    push_cast
    field_simp [positive.ne']
    ring
  rw [sumEq]
  unfold burnolCompactAdditiveCoSum burnolCompactAdditiveNormalization
  rw [Complex.real_smul]
  push_cast
  field_simp [positive.ne']

def burnolCompactAdditiveHalfDensity
    (source : burnolCompactAnnulusSource) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * burnolCompactAdditiveCoSum source (Real.exp x)

private theorem complexExp_cpow_half_family (x : ℝ) :
    (Real.exp x : ℂ) ^ (1 / 2 : ℂ) =
      (Real.exp (x / 2) : ℂ) := by
  calc
    _ = ((Real.exp x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos x).le (1 / 2 : ℝ) using 1
      all_goals norm_num
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
      congr 1
      ring

theorem burnolCompactAdditiveHalfDensity_eq_logOrbit
    (source : burnolCompactAnnulusSource) (x : ℝ) :
    burnolCompactAdditiveHalfDensity source x =
      (1 / 2 : ℂ) * coPoissonLogOrbitMap source.1 (-x) := by
  have bridge :=
    coPoissonMuntzScaleRemainder_reciprocal_eq_compactAdditiveCoSum
      source (t := Real.exp x) (Real.exp_pos x)
  have logBridge := coPoissonLogOrbitMap_log_eq_scaleRemainder
    source.1 (scale := (Real.exp x)⁻¹) (inv_pos.mpr (Real.exp_pos x))
  rw [Real.log_inv, Real.log_exp] at logBridge
  rw [bridge] at logBridge
  have inverseHalf :
      (Real.exp x : ℂ)⁻¹ ^ (1 / 2 : ℂ) =
        (Real.exp (-x / 2) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg,
      complexExp_cpow_half_family]
  rw [Complex.ofReal_inv, inverseHalf] at logBridge
  unfold burnolCompactAdditiveHalfDensity
  have expProduct :
      (Real.exp (-x / 2) : ℂ) * (Real.exp x : ℂ) =
        (Real.exp (x / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    (Real.exp (x / 2) : ℂ) * burnolCompactAdditiveCoSum source (Real.exp x) =
        (1 / 2 : ℂ) *
          ((Real.exp (-x / 2) : ℂ) *
            (((2 * Real.exp x : ℝ) : ℂ) *
              burnolCompactAdditiveCoSum source (Real.exp x))) := by
      rw [← expProduct]
      push_cast
      ring
    _ = (1 / 2 : ℂ) * coPoissonLogOrbitMap source.1 (-x) := by
      rw [logBridge]

theorem burnolCompactAdditiveHalfDensity_measurable
    (source : burnolCompactAnnulusSource) :
    Measurable (burnolCompactAdditiveHalfDensity source) := by
  rw [show burnolCompactAdditiveHalfDensity source = fun x : ℝ =>
      (1 / 2 : ℂ) * coPoissonLogOrbitMap source.1 (-x) by
    funext x
    exact burnolCompactAdditiveHalfDensity_eq_logOrbit source x]
  exact Measurable.mul measurable_const
    ((coPoissonLogOrbitMap_measurable source.1).comp measurable_neg)

theorem burnolCompactAdditiveHalfDensity_memLp
    (source : burnolCompactAnnulusSource) :
    MemLp (burnolCompactAdditiveHalfDensity source) 2 volume := by
  have reflected := (coPoissonLogOrbitMap_memLp source.1).comp_measurePreserving
    negMeasurePreserving
  change MemLp (fun x : ℝ => coPoissonLogOrbitMap source.1 (-x)) 2 volume at reflected
  exact (memLp_congr_ae <| ae_of_all volume fun x =>
    burnolCompactAdditiveHalfDensity_eq_logOrbit source x).mpr
      (reflected.const_smul (1 / 2 : ℂ))

/-- Positive additive reconstruction generated from the logarithmic
half-density; this is an actual change of variable, not a type alias. -/
def burnolCompactAdditiveReconstruction
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  (Real.exp (-Real.log t / 2) : ℂ) *
    burnolCompactAdditiveHalfDensity source (Real.log t)

theorem burnolCompactAdditiveReconstruction_eq
    (source : burnolCompactAnnulusSource) {t : ℝ} (positive : 0 < t) :
    burnolCompactAdditiveReconstruction source t =
      burnolCompactAdditiveCoSum source t := by
  unfold burnolCompactAdditiveReconstruction
    burnolCompactAdditiveHalfDensity
  rw [Real.exp_log positive]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have : -Real.log t / 2 + Real.log t / 2 = 0 := by ring
  rw [this, Real.exp_zero]
  norm_num

theorem burnolCompactAdditiveReconstruction_measurable
    (source : burnolCompactAnnulusSource) :
    Measurable (burnolCompactAdditiveReconstruction source) := by
  unfold burnolCompactAdditiveReconstruction
  exact (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (Measurable.div_const
          (Measurable.neg Real.measurable_log) 2))).mul
    ((burnolCompactAdditiveHalfDensity_measurable source).comp
      Real.measurable_log)

private theorem family_integrableOn_exp_weight_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      Integrable (fun x : ℝ => Real.exp x * g (Real.exp x)) := by
  have change :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun _ _ _ _ equality => Real.exp_injective equality) g
  simpa only [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    smul_eq_mul, integrableOn_univ] using change

private theorem burnolCompactAdditiveHalfDensity_sq_norm
    (source : burnolCompactAnnulusSource) (x : ℝ) :
    ‖burnolCompactAdditiveHalfDensity source x‖ ^ 2 =
      Real.exp x * ‖burnolCompactAdditiveCoSum source (Real.exp x)‖ ^ 2 := by
  rw [burnolCompactAdditiveHalfDensity, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos (x / 2)).le, mul_pow,
    ← Real.exp_nat_mul]
  congr 2
  ring

theorem burnolCompactAdditiveCoSum_memLp_positive
    (source : burnolCompactAnnulusSource) :
    MemLp (burnolCompactAdditiveCoSum source) 2
      (volume.restrict (Ioi 0)) := by
  have measurable : AEStronglyMeasurable (burnolCompactAdditiveCoSum source)
      (volume.restrict (Ioi 0)) := by
    refine (burnolCompactAdditiveReconstruction_measurable source).aestronglyMeasurable.restrict.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    exact burnolCompactAdditiveReconstruction_eq source positive
  apply (memLp_two_iff_integrable_sq_norm measurable).mpr
  have chartIntegrable : Integrable
      (fun x : ℝ => ‖burnolCompactAdditiveHalfDensity source x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (burnolCompactAdditiveHalfDensity_measurable source).aestronglyMeasurable).mp
        (burnolCompactAdditiveHalfDensity_memLp source)
  have weightedIntegrable : Integrable (fun x : ℝ =>
      Real.exp x * ‖burnolCompactAdditiveCoSum source (Real.exp x)‖ ^ 2) :=
    chartIntegrable.congr <| ae_of_all volume fun x =>
      burnolCompactAdditiveHalfDensity_sq_norm source x
  exact (family_integrableOn_exp_weight_iff
    (fun t : ℝ => ‖burnolCompactAdditiveCoSum source t‖ ^ 2)).mpr
      weightedIntegrable

def burnolCompactAdditiveEvenReconstruction
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  if t = 0 then burnolCompactAdditiveCoSum source 0
  else burnolCompactAdditiveReconstruction source |t|

theorem burnolCompactAdditiveEvenReconstruction_eq
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCompactAdditiveEvenReconstruction source t =
      burnolCompactAdditiveCoSum source t := by
  by_cases zero : t = 0
  · simp [burnolCompactAdditiveEvenReconstruction, zero]
  · rw [burnolCompactAdditiveEvenReconstruction, if_neg zero,
      burnolCompactAdditiveReconstruction_eq source (abs_pos.mpr zero)]
    rcases lt_or_ge t 0 with negative | nonnegative
    · rw [abs_of_neg negative, burnolCompactAdditiveCoSum_even]
    · rw [abs_of_nonneg nonnegative]

theorem burnolCompactAdditiveCoSum_measurable
    (source : burnolCompactAnnulusSource) :
    Measurable (burnolCompactAdditiveCoSum source) := by
  rw [← show burnolCompactAdditiveEvenReconstruction source =
      burnolCompactAdditiveCoSum source by
    funext t
    exact burnolCompactAdditiveEvenReconstruction_eq source t]
  unfold burnolCompactAdditiveEvenReconstruction
  exact Measurable.ite (by
      have setEq : {a : ℝ | a = 0} = ({0} : Set ℝ) := by
        ext a
        simp
      rw [setEq]
      exact measurableSet_singleton 0) measurable_const
    ((burnolCompactAdditiveReconstruction_measurable source).comp
      continuous_abs.measurable)

theorem burnolCompactAdditiveCoSum_memLp_full
    (source : burnolCompactAnnulusSource) :
    MemLp (burnolCompactAdditiveCoSum source) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (burnolCompactAdditiveCoSum_measurable source).aestronglyMeasurable).mpr
  have positiveIntegrable : IntegrableOn
      (fun t : ℝ => ‖burnolCompactAdditiveCoSum source t‖ ^ 2) (Ioi 0) :=
    (memLp_two_iff_integrable_sq_norm
      ((burnolCompactAdditiveCoSum_measurable source).aestronglyMeasurable.restrict)).mp
        (burnolCompactAdditiveCoSum_memLp_positive source)
  have negativeIntegrable : IntegrableOn
      (fun t : ℝ => ‖burnolCompactAdditiveCoSum source t‖ ^ 2) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let embedding : MeasurableEmbedding (fun t : ℝ => -t) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [embedding.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero,
      burnolCompactAdditiveCoSum_even source]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr positiveIntegrable
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact negativeIntegrable.union positiveIntegrable

/-- Actual additive-position `L²` landing of an arbitrary compact annulus
source. -/
def burnolCompactAdditiveL2
    (source : burnolCompactAnnulusSource) : BurnolL2 :=
  (burnolCompactAdditiveCoSum_memLp_full source).toLp
    (burnolCompactAdditiveCoSum source)

theorem burnolCompactAdditiveL2_coeFn
    (source : burnolCompactAnnulusSource) :
    (burnolCompactAdditiveL2 source : ℝ → ℂ) =ᵐ[volume]
      burnolCompactAdditiveCoSum source :=
  MemLp.coeFn_toLp (burnolCompactAdditiveCoSum_memLp_full source)

theorem burnolCompactAdditiveL2_mem_locallyConstantFace
    (source : burnolCompactAnnulusSource) :
    burnolCompactAdditiveL2 source ∈
      locallyConstantFace burnolUnscaledCommonGapRadius := by
  rw [mem_locallyConstantFace_iff_exists]
  refine ⟨-burnolCompactAdditiveNormalization source, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul
      (-burnolCompactAdditiveNormalization source)
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius)
      (burnolCompactAdditiveL2 source),
    ae_restrict_of_ae (burnolCompactAdditiveL2_coeFn source),
    ae_restrict_mem (measurableSet_symmetricInterval
      burnolUnscaledCommonGapRadius)] with t hsmul hconst hrestrict hvalue ht
  calc
    ((-burnolCompactAdditiveNormalization source) •
        intervalConstant burnolUnscaledCommonGapRadius :
          Lp ℂ 2 (volume.restrict
            (symmetricInterval burnolUnscaledCommonGapRadius))) t =
      -burnolCompactAdditiveNormalization source *
        intervalConstant burnolUnscaledCommonGapRadius t := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = -burnolCompactAdditiveNormalization source := by
      rw [hconst, mul_one]
    _ = burnolCompactAdditiveCoSum source t := by
      symm
      apply burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
      exact (abs_le).2 (by
        simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using ht)
    _ = burnolCompactAdditiveL2 source t := hvalue.symm
    _ = restrictToInterval burnolUnscaledCommonGapRadius
        (burnolCompactAdditiveL2 source) t := hrestrict.symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
