import H0mework.Arithmetic.BurnolCarrier.AdditiveFourierLanding
import H0mework.Versions.R2.Arithmetic.RiemannSpectral.FourierFixedSelfAdjoint

/-!
# Source-generated nonzero Fourier-fixed Burnol state

The actual additive co-sum state and its ordinary Fourier transform carry
source-computed constant coordinates on the common radius `1 / 4`.  The
position coefficient is the negative normalization, while the Fourier
coefficient is the negative positive-source mass.  Their signs rule out
anti-invariance, so the canonical symmetrization `(v + ℱv) / 2` is a
nonzero element of the Fourier-fixed physical carrier.

No spectral coordinate, zero, eigenvector, or landing law is supplied to
this construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped InnerProductSpace ENNReal

noncomputable section

private theorem reciprocalBumpSum_re (scale point : ℝ) :
    (((scale : ℂ)⁻¹ *
        ((burnolAnnulusBump point : ℂ) +
          (burnolAnnulusBump (-point) : ℂ))).re) =
      scale⁻¹ *
        (burnolAnnulusBump point + burnolAnnulusBump (-point)) := by
  rw [← ofReal_inv, ← ofReal_add, ← ofReal_mul, ofReal_re]

theorem burnolAdditiveNormalization_re_pos :
    0 < burnolAdditiveNormalization.re := by
  have annulusIntegral :
      (∫ x : ℝ, burnolAnnulusSchwartz x) =
        ((∫ x : ℝ, burnolAnnulusBump x : ℝ) : ℂ) := by
    simp_rw [burnolAnnulusSchwartz_apply]
    exact integral_complex_ofReal
  unfold burnolAdditiveNormalization
  rw [burnolEvenAnnulusSchwartz_integral_eq_two, annulusIntegral]
  norm_num
  exact burnolAnnulusBump_integral_pos

theorem burnolAdditiveAnnulusSource_re_nonneg (t : ℝ) :
    0 ≤ (burnolAdditiveAnnulusSource t).re := by
  by_cases zero : t = 0
  · simp [zero]
  · rw [burnolAdditiveAnnulusSource, if_neg zero,
      burnolEvenAnnulusSchwartz, add_apply,
      burnolAnnulusSchwartzReflection_apply,
      burnolAnnulusSchwartz_apply, burnolAnnulusSchwartz_apply]
    rw [reciprocalBumpSum_re]
    exact mul_nonneg (inv_nonneg.mpr (abs_nonneg t))
      (add_nonneg (burnolAnnulusBump.nonneg' _)
        (burnolAnnulusBump.nonneg' _))

theorem burnolAdditiveAnnulusSource_re_pos_on_core
    {t : ℝ} (lower : 9 / 5 < t) (upper : t < 11 / 5) :
    0 < (burnolAdditiveAnnulusSource t).re := by
  have positive : 0 < t := by linarith
  have inversePositive : 0 < t⁻¹ := inv_pos.mpr positive
  have inverseLower : (5 / 11 : ℝ) < t⁻¹ := by
    calc
      (5 / 11 : ℝ) < 1 / t := (lt_div_iff₀ positive).2 (by linarith)
      _ = t⁻¹ := one_div t
  have inverseUpper : t⁻¹ < (5 / 9 : ℝ) := by
    calc
      t⁻¹ = 1 / t := (one_div t).symm
      _ < (5 / 9 : ℝ) := (div_lt_iff₀ positive).2 (by linarith)
  have inBall : t⁻¹ ∈ Metric.ball (1 / 2 : ℝ) burnolAnnulusBump.rOut := by
    rw [Metric.mem_ball, Real.dist_eq]
    unfold burnolAnnulusBump
    dsimp only [ContDiffBump.rOut]
    rw [abs_lt]
    constructor <;> linarith
  have bumpPositive : 0 < burnolAnnulusBump t⁻¹ :=
    burnolAnnulusBump.pos_of_mem_ball inBall
  rw [burnolAdditiveAnnulusSource, if_neg positive.ne', abs_of_pos positive,
    burnolEvenAnnulusSchwartz, add_apply,
    burnolAnnulusSchwartzReflection_apply,
    burnolAnnulusSchwartz_apply, burnolAnnulusSchwartz_apply]
  rw [reciprocalBumpSum_re]
  have otherNonnegative : 0 ≤ burnolAnnulusBump (-t⁻¹) :=
    burnolAnnulusBump.nonneg' _
  exact mul_pos inversePositive (add_pos_of_pos_of_nonneg bumpPositive otherNonnegative)

theorem burnolAdditiveAnnulusSource_positiveIntegral_re_pos :
    0 < (∫ t : ℝ in Ioi 0, burnolAdditiveAnnulusSource t).re := by
  have reIntegral := integral_re
    (burnolAdditiveAnnulusSource_integrable.integrableOn (s := Ioi 0))
  change 0 < RCLike.re (∫ t : ℝ in Ioi 0, burnolAdditiveAnnulusSource t)
  rw [← reIntegral]
  apply (integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ burnolAdditiveAnnulusSource_re_nonneg)
    burnolAdditiveAnnulusSource_integrable.re.integrableOn).mpr
  have corePositive :
      (volume : Measure ℝ).restrict (Ioi 0)
        (Ioo (9 / 5 : ℝ) (11 / 5 : ℝ)) ≠ 0 := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    · rw [inter_eq_self_of_subset_left]
      · rw [Real.volume_Ioo]
        norm_num
      · intro t membership
        exact (by norm_num : (0 : ℝ) < 9 / 5).trans membership.1
  have subset : Ioo (9 / 5 : ℝ) (11 / 5 : ℝ) ⊆
      Function.support (fun t => (burnolAdditiveAnnulusSource t).re) := by
    intro t membership
    exact burnolAdditiveAnnulusSource_re_pos_on_core
      membership.1 membership.2 |>.ne'
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr corePositive)
    (measure_mono subset)

theorem burnolAdditiveFourierGapConstant_re_neg :
    burnolAdditiveFourierGapConstant.re < 0 := by
  unfold burnolAdditiveFourierGapConstant
  rw [neg_re]
  exact neg_lt_zero.mpr burnolAdditiveAnnulusSource_positiveIntegral_re_pos

theorem burnolAdditiveFourierGapConstant_ne_normalization :
    burnolAdditiveFourierGapConstant ≠ burnolAdditiveNormalization := by
  intro equality
  have := congrArg Complex.re equality
  linarith [burnolAdditiveFourierGapConstant_re_neg,
    burnolAdditiveNormalization_re_pos]

theorem burnolAdditiveFullEvenL2_restrict_eq_positionConstant :
    (-burnolAdditiveNormalization) •
        intervalConstant burnolUnscaledCommonGapRadius =
      restrictToInterval burnolUnscaledCommonGapRadius
        burnolAdditiveFullEvenL2 := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_smul (-burnolAdditiveNormalization)
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius)
      burnolAdditiveFullEvenL2,
    ae_restrict_of_ae burnolAdditiveFullEvenL2_coeFn,
    ae_restrict_mem
      (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)]
      with t hsmul hconstant hrestrict hfull inside
  have absBound : |t| ≤ 1 := by
    change t ∈ Icc (-burnolUnscaledCommonGapRadius)
      burnolUnscaledCommonGapRadius at inside
    exact (abs_le.mpr inside).trans burnolUnscaledCommonGapRadius_le_one
  calc
    ((-burnolAdditiveNormalization) •
        intervalConstant burnolUnscaledCommonGapRadius) t =
      (-burnolAdditiveNormalization) *
        intervalConstant burnolUnscaledCommonGapRadius t := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = -burnolAdditiveNormalization := by rw [hconstant, mul_one]
    _ = burnolAdditiveCoSum t :=
      (burnolAdditiveCoSum_eq_neg_normalization_of_abs_le_one absBound).symm
    _ = burnolAdditiveFullEvenL2 t := hfull.symm
    _ = restrictToInterval burnolUnscaledCommonGapRadius
        burnolAdditiveFullEvenL2 t := hrestrict.symm

theorem burnolAdditiveFourierL2_restrict_eq_gapConstant :
    burnolAdditiveFourierGapConstant •
        intervalConstant burnolUnscaledCommonGapRadius =
      restrictToInterval burnolUnscaledCommonGapRadius
        (fourierL2 burnolAdditiveFullEvenL2) := by
  have intervalAE :
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) =ᵐ[(volume : Measure ℝ)]
        Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    MeasureTheory.Ioo_ae_eq_Icc
  have closedIntervalAE : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) →
        (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t =
          burnolAdditiveFourierGapConstant := by
    filter_upwards [burnolAdditiveFourierL2_ae_eq_gapConstant_on_Ioo,
      intervalAE] with t openEquality sameInterval
    intro inClosed
    apply openEquality
    change Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) t
    rw [sameInterval]
    exact inClosed
  have constantRestricted : ∀ᵐ t ∂(volume : Measure ℝ).restrict
      (symmetricInterval burnolUnscaledCommonGapRadius),
      (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t =
        burnolAdditiveFourierGapConstant := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict
      (Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ)), _
    filter_upwards [ae_restrict_of_ae closedIntervalAE,
      ae_restrict_mem measurableSet_Icc] with t equality inClosed
    exact equality inClosed
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_smul burnolAdditiveFourierGapConstant
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius)
      (fourierL2 burnolAdditiveFullEvenL2),
    constantRestricted]
      with t hsmul hconstant hrestrict hfourier
  calc
    (burnolAdditiveFourierGapConstant •
        intervalConstant burnolUnscaledCommonGapRadius) t =
      burnolAdditiveFourierGapConstant *
        intervalConstant burnolUnscaledCommonGapRadius t := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = burnolAdditiveFourierGapConstant := by rw [hconstant, mul_one]
    _ = (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t := hfourier.symm
    _ = restrictToInterval burnolUnscaledCommonGapRadius
        (fourierL2 burnolAdditiveFullEvenL2) t := hrestrict.symm

def burnolAdditiveEvenPhysicalState :
    EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
  burnolAdditiveActualNonzeroPhysicalState.1

def burnolAdditiveFourierFixedSymmetrization :
    EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
  (1 / 2 : ℂ) •
    (burnolAdditiveEvenPhysicalState +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius
        burnolAdditiveEvenPhysicalState)

theorem burnolAdditiveFourierFixedSymmetrization_fixed :
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
        burnolAdditiveFourierFixedSymmetrization =
      burnolAdditiveFourierFixedSymmetrization := by
  have involution :
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            burnolAdditiveEvenPhysicalState) =
        burnolAdditiveEvenPhysicalState := by
    exact evenFaceFourier_involutive burnolUnscaledCommonGapRadius
      burnolAdditiveEvenPhysicalState
  unfold burnolAdditiveFourierFixedSymmetrization
  rw [map_smul, map_add, involution]
  abel_nf

theorem burnolAdditiveFourierFixedSymmetrization_ne_zero :
    burnolAdditiveFourierFixedSymmetrization ≠ 0 := by
  intro symmetrizationZero
  have sumZero :
      burnolAdditiveEvenPhysicalState +
          evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            burnolAdditiveEvenPhysicalState = 0 := by
    have scalarNe : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (smul_eq_zero.mp (by
      simpa [burnolAdditiveFourierFixedSymmetrization] using
        symmetrizationZero)).resolve_left scalarNe
  have physicalAnti :
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          burnolAdditiveEvenPhysicalState =
        -burnolAdditiveEvenPhysicalState :=
    eq_neg_of_add_eq_zero_right sumZero
  have ambientAnti :
      fourierL2 burnolAdditiveFullEvenL2 =
        -burnolAdditiveFullEvenL2 := by
    have coerced := congrArg Subtype.val physicalAnti
    exact coerced
  have restrictedAnti := congrArg
    (restrictToInterval burnolUnscaledCommonGapRadius) ambientAnti
  have scalarEquality :
      burnolAdditiveFourierGapConstant •
          intervalConstant burnolUnscaledCommonGapRadius =
        burnolAdditiveNormalization •
          intervalConstant burnolUnscaledCommonGapRadius := by
    calc
      burnolAdditiveFourierGapConstant •
          intervalConstant burnolUnscaledCommonGapRadius =
        restrictToInterval burnolUnscaledCommonGapRadius
          (fourierL2 burnolAdditiveFullEvenL2) :=
        burnolAdditiveFourierL2_restrict_eq_gapConstant
      _ = restrictToInterval burnolUnscaledCommonGapRadius
          (-burnolAdditiveFullEvenL2) := restrictedAnti
      _ = -restrictToInterval burnolUnscaledCommonGapRadius
          burnolAdditiveFullEvenL2 := by rw [map_neg]
      _ = -((-burnolAdditiveNormalization) •
          intervalConstant burnolUnscaledCommonGapRadius) := by
        rw [burnolAdditiveFullEvenL2_restrict_eq_positionConstant]
      _ = burnolAdditiveNormalization •
          intervalConstant burnolUnscaledCommonGapRadius := by module
  have coefficientEquality :
      burnolAdditiveFourierGapConstant = burnolAdditiveNormalization :=
    smul_left_injective ℂ
      (intervalConstant_ne_zero (by
        norm_num [burnolUnscaledCommonGapRadius])) scalarEquality
  exact burnolAdditiveFourierGapConstant_ne_normalization coefficientEquality

def burnolAdditiveFourierFixedPhysicalState :
    EvenBurnolFourierFixedCarrier burnolUnscaledCommonGapRadius :=
  ⟨burnolAdditiveFourierFixedSymmetrization,
    mem_evenBurnolFourierFixedFace_iff.mpr
      burnolAdditiveFourierFixedSymmetrization_fixed⟩

theorem burnolAdditiveFourierFixedPhysicalState_ne_zero :
    burnolAdditiveFourierFixedPhysicalState ≠ 0 := by
  intro stateZero
  apply burnolAdditiveFourierFixedSymmetrization_ne_zero
  exact congrArg Subtype.val stateZero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
