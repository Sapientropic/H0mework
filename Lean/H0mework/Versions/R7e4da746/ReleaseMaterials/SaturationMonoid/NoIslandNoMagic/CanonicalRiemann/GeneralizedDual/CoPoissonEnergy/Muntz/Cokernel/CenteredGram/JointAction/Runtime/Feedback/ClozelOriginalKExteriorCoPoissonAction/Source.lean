import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBFiniteAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorCoPoissonAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszFinitePairing
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalPaPhysicalGreen
open OriginalKFixedBoundarySourceFibre
open OriginalKCoefficientBFiniteAction
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace Topology
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "q" => (1 / 4 : ℝ)

def sourceColumn (c : BurnolCompletedMellinCoordinate) : Fin 2 → M := ![sourceB c, sourceSB c]
def sourceProfile (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![burnolRieszSingleFourierSourceRaw c, burnolRieszReturnRaw c]

/-- The sign is opposite to the old signed finite-column seed. -/
def positiveWeight (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : ℝ → ℂ :=
  fun t => -reciprocalWeight h (sourceProfile c i) t

private def returnWeightSlope (c : BurnolCompletedMellinCoordinate) (h t : ℝ) : ℂ :=
  (Real.exp (-h / 2) : ℂ) *
    ((-1 / (t : ℂ) ^ 2) * burnolRieszReturnRaw c (Real.exp (-h) / t) +
      (t : ℂ)⁻¹ * ((-Real.exp (-h) / t ^ 2) • burnolRieszReturnRawDerivative c (Real.exp (-h) / t)))

private theorem return_weight_derivative (c : BurnolCompletedMellinCoordinate) (h t : ℝ)
    (positive : 0 < t) :
    HasDerivAt (positiveWeight c h 1) (returnWeightSlope c h t) t := by
  have moved : HasDerivAt (fun u : ℝ => Real.exp (-h) / u) (-Real.exp (-h) / t ^ 2) t := by
    convert! (hasDerivAt_const t (Real.exp (-h))).div (hasDerivAt_id t) positive.ne' using 1
    simp
  have inverted : HasDerivAt (fun u : ℝ => (u : ℂ)⁻¹) (-1 / (t : ℂ) ^ 2) t :=
    (Complex.ofRealCLM.hasDerivAt).inv (Complex.ofReal_ne_zero.mpr positive.ne')
  convert! (inverted.mul ((burnolRieszReturnRaw_hasDerivAt c _).scomp t moved)).const_mul
      (Real.exp (-h / 2) : ℂ) using 1
  funext u
  simp only [positiveWeight, sourceProfile, Matrix.cons_val_one, Matrix.cons_val_zero,
    reciprocalWeight, neg_mul, neg_neg, Function.comp_def, Pi.mul_apply, mul_assoc]

theorem positiveWeight_hasDerivAt (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2)
    (t : ℝ) (positive : 0 < t) :
    HasDerivAt (positiveWeight c h i) (deriv (positiveWeight c h i) t) t := by
  fin_cases i
  · exact ((fourierWeight_hasDerivAt c h t positive).neg).differentiableAt.hasDerivAt
  · exact (return_weight_derivative c h t positive).differentiableAt.hasDerivAt

theorem positiveWeight_deriv_continuousOn (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    ContinuousOn (deriv (positiveWeight c h i)) (Ioi 0) := by
  fin_cases i
  · change ContinuousOn (deriv (-fourierWeight c h)) (Ioi 0)
    have same : deriv (-fourierWeight c h) = -deriv (fourierWeight c h) :=
      funext (fun _ => deriv.neg)
    rw [same]
    exact (fourierWeight_deriv_continuousOn c h).neg
  · have actual (t : ℝ) (positive : 0 < t) :
        deriv (positiveWeight c h 1) t = returnWeightSlope c h t :=
      (return_weight_derivative c h t positive).deriv
    have regular : ContinuousOn (returnWeightSlope c h) (Ioi 0) := by
      intro t positive
      have moved : ContinuousAt (fun u : ℝ => Real.exp (-h) / u) t :=
        continuousAt_const.div continuousAt_id positive.ne'
      have profile := (burnolRieszReturnRaw_continuous c).continuousAt.comp moved
      have slope := (burnolRieszReturnRawDerivative_continuous c).continuousAt.comp moved
      have castNonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
      exact (continuousAt_const.mul
        (((continuousAt_const.div (Complex.continuous_ofReal.continuousAt.pow 2)
          (pow_ne_zero _ castNonzero)).mul profile).add
          ((Complex.continuous_ofReal.continuousAt.inv₀ castNonzero).mul
            ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ positive.ne')).smul
              slope)))).continuousWithinAt
    exact regular.congr (fun t positive => actual t positive)

theorem positiveWeight_measurable (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    Measurable (positiveWeight c h i) := by
  have profile : Measurable (sourceProfile c i) := by
    fin_cases i
    · apply measurable_of_continuousOn_compl_singleton 0
      intro x outside
      exact (burnolRieszSingleFourierSourceRaw_continuousAt c
        (by simpa only [mem_compl_iff, mem_singleton_iff] using outside)).continuousWithinAt
    · exact (burnolRieszReturnRaw_continuous c).measurable
  unfold positiveWeight reciprocalWeight
  exact ((measurable_const.mul Complex.measurable_ofReal.inv).mul
    (profile.comp (measurable_const.div measurable_id))).neg

def exteriorSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  burnolWeightedReciprocalStepSource (bandLower h) 4 (positiveWeight c h i)
    (deriv (positiveWeight c h i))
def exteriorWave (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  burnolWeightedReciprocalStepWave (bandLower h) 4 (positiveWeight c h i)
    (deriv (positiveWeight c h i))
def exteriorPrefix (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) (N : ℕ) : BurnolL2 :=
  weightedPrefix (bandLower h) 4 (positiveWeight c h i) (deriv (positiveWeight c h i)) N

def nativeNormalization (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : ℂ :=
  ∫ t : ℝ in Ioc (bandLower h) 4, positiveWeight c h i t

def centeringMean (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : ℂ :=
  outwardMean h (sourceColumn c i)

private theorem weight_regular_band (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    ContinuousOn (deriv (positiveWeight c h i)) (Icc (bandLower h) 4) :=
  (positiveWeight_deriv_continuousOn c h i).mono (fun _ inside => (bandLower_pos h).trans_le inside.1)

private theorem weight_derivative_band (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    ∀ t ∈ Icc (bandLower h) 4,
      HasDerivAt (positiveWeight c h i) (deriv (positiveWeight c h i) t) t :=
  fun t inside => positiveWeight_hasDerivAt c h i t ((bandLower_pos h).trans_le inside.1)

private theorem column_raw (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (E (sourceColumn c i : Hq) : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval q).indicator (sourceProfile c i) := by
  fin_cases i
  · have original := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
      (burnolRieszSingleFourierSource_ae_raw c)
    filter_upwards [burnolQuarterZeroExtension_coe (sourceB c : Hq), original] with x extended raw
    change E (sourceB c : Hq) x = _
    rw [extended]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_mem inside, indicator_of_mem inside]
      exact raw inside
    · rw [indicator_of_notMem inside, indicator_of_notMem inside]
  · exact burnolZeroExtensionMeanZeroFourier_ae_raw (sourceB c)

private theorem profile_even (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) :
    sourceProfile c i (-x) = sourceProfile c i x := by
  fin_cases i
  · exact source_raw_even c x
  · exact return_raw_even c x

private theorem inverse_band (h : ℝ) : (bandLower h)⁻¹ = q * Real.exp h := by
  simp only [bandLower, Real.exp_neg, mul_inv_rev, inv_inv]
  norm_num
  ring

/-- The primitive's L2 source is the actual outward shell, before co-Poisson acts. -/
theorem actual_exterior_source (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    exteriorSource c h i = outwardExterior h (sourceColumn c i) := by
  let whole := E (sourceColumn c i : Hq)
  let dilated := burnolMultiplicativeDilation (-h) whole
  have movedRead := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero (-h))).ae (column_raw c i)
  have source := weighted_source_coeFn (bandLower h) 4 (positiveWeight c h i)
    (deriv (positiveWeight c h i)) (bandLower_pos h) (bandLower_le_four h nonnegative)
    (weight_derivative_band c h i) (weight_regular_band c h i) (measurable_deriv _)
  change exteriorSource c h i = dilated - originalPhysicalCutoff q dilated
  apply Lp.ext
  filter_upwards [source, Lp.coeFn_sub dilated (originalPhysicalCutoff q dilated),
    originalPhysicalCutoff_coeFn q dilated, burnolMultiplicativeDilation_coeFn (-h) whole,
    movedRead, volume.ae_ne (0 : ℝ)] with x sourceAt differenceAt cutoffAt dilationAt rawAt nonzero
  change exteriorSource c h i x = _ at sourceAt
  rw [sourceAt, differenceAt]
  change _ = dilated x - originalPhysicalCutoff q dilated x
  rw [cutoffAt]
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have active : (bandLower h ≤ |x|⁻¹ ∧ |x|⁻¹ < 4) ↔
      (q < |x| ∧ |x| ≤ q * Real.exp h) := by
    rw [le_inv_comm₀ (bandLower_pos h) absolute, inv_lt_comm₀ absolute (by norm_num : (0:ℝ)<4),
      inverse_band]
    norm_num only [inv_eq_one_div]
    exact and_comm
  have movedInside : Real.exp (-h) * x ∈ symmetricInterval q ↔ |x| ≤ q * Real.exp h := by
    change (-q ≤ Real.exp (-h) * x ∧ Real.exp (-h) * x ≤ q) ↔ _
    rw [← abs_le, abs_mul, abs_of_pos (Real.exp_pos (-h))]
    have identity : Real.exp (-h) * (q * Real.exp h) = q := by
      rw [Real.exp_neg]
      field_simp
    constructor
    · intro upper
      exact (mul_le_mul_iff_right₀ (Real.exp_pos (-h))).mp (upper.trans_eq identity.symm)
    · intro upper
      exact (mul_le_mul_of_nonneg_left upper (Real.exp_pos (-h)).le).trans_eq identity
  have evenRead : sourceProfile c i (Real.exp (-h) * x) =
      sourceProfile c i (Real.exp (-h) * |x|) := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, mul_neg, profile_even]
  have rawAt' : whole (Real.exp (-h) * x) =
      (symmetricInterval q).indicator (sourceProfile c i) (Real.exp (-h) * x) := rawAt
  by_cases inside : x ∈ symmetricInterval q
  · have small : |x| ≤ q := abs_le.mpr inside
    rw [indicator_of_mem inside, sub_self]
    simp only [burnolReciprocalStepSourceRaw, if_neg (fun member =>
      not_lt_of_ge small ((active.mp member).1)), mul_zero]
  · rw [indicator_of_notMem inside, sub_zero]
    change _ = burnolMultiplicativeDilation (-h) whole x
    rw [dilationAt]
    change _ = (Real.exp (-h / 2) : ℂ) * whole (Real.exp (-h) * x)
    rw [rawAt']
    by_cases upper : |x| ≤ q * Real.exp h
    · rw [indicator_of_mem (movedInside.mpr upper), evenRead]
      have lower : q < |x| := lt_of_not_ge (fun small => inside (abs_le.mp small))
      rw [burnolReciprocalStepSourceRaw, if_pos (active.mpr ⟨lower,upper⟩)]
      simp only [positiveWeight, reciprocalWeight, neg_mul, neg_neg, Complex.ofReal_inv,
        inv_inv, div_inv_eq_mul]
      field_simp [Complex.ofReal_ne_zero.mpr absolute.ne']
    · rw [indicator_of_notMem (fun member => upper (movedInside.mp member)), mul_zero,
        burnolReciprocalStepSourceRaw, if_neg (fun member => upper (active.mp member).2), mul_zero]

theorem exterior_wave_realizes (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (outwardExterior h (sourceColumn c i)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (exteriorWave c h i)) test := by
  rw [← actual_exterior_source c h nonnegative i]
  exact burnolWeightedReciprocalStepSource_realizes _ _ _ _ (bandLower_pos h)
    (bandLower_le_four h nonnegative) le_rfl (weight_regular_band c h i) test

theorem exterior_wave_inPa (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (i : Fin 2) :
    exteriorWave c h i ∈ burnolOriginalPaInL2 :=
  burnolWeightedReciprocalStepWave_inPa _ _ _ _ (bandLower_in_annulus h nonnegative bounded)
    (by norm_num) (weight_regular_band c h i)

theorem exterior_prefix_tendsto (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    Tendsto (exteriorPrefix c h i) atTop (𝓝 (exteriorWave c h i)) :=
  weightedPrefix_tendsto _ _ _ _ (bandLower_pos h) (weight_regular_band c h i)

theorem exterior_prefix_arithmetic (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (N : ℕ) :
    (exteriorPrefix c h i N : ℝ → ℂ) =ᵐ[volume]
      weightedPrefixRaw (bandLower h) 4 (positiveWeight c h i) N :=
  weighted_prefix_coeFn _ _ _ _ N (bandLower_pos h) (bandLower_le_four h nonnegative)
    (weight_derivative_band c h i) (weight_regular_band c h i) (measurable_deriv _)

/-- The native integer and continuous channels act on this same actual exterior. -/
theorem exterior_prefix_source (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (N : ℕ) :
    exteriorPrefix c h i N = FiniteForcing.source N (outwardExterior h (sourceColumn c i)) := by
  rw [← actual_exterior_source c h nonnegative i]
  exact weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (bandLower_pos h)
    (bandLower_le_four h nonnegative) (weight_derivative_band c h i)
    (weight_regular_band c h i) (measurable_deriv _) (positiveWeight_measurable c h i)

theorem exterior_wave_arithmetic_read (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (test : BurnolL2) :
    inner ℂ test (exteriorWave c h i) = ∫ x : ℝ, inner ℂ (test x)
      (Arithmetic.weightedCountingRaw (bandLower h) 4 (positiveWeight c h i) x) :=
  Arithmetic.weighted_wave_arithmetic_pairing _ _ _ _ (bandLower_pos h)
    (bandLower_le_four h nonnegative) (weight_derivative_band c h i)
    (weight_regular_band c h i) (measurable_deriv _) test

/-- Both actual centering means survive the complete physical-core source action. -/
theorem actual_core_source_action (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    sourceCore c h = finiteBoundaryAction c h (elementarySource c) - (1/2 : ℂ) •
      (exteriorSource c h 1 - fourierL2 (exteriorSource c h 0) +
        centeringMean c h 1 • ConstantDual.seed -
        centeringMean c h 0 • fourierL2 ConstantDual.seed) := by
  rw [actual_exterior_source c h nonnegative 0, actual_exterior_source c h nonnegative 1]
  simp only [sourceCore, sourceColumn, Matrix.cons_val_one, Matrix.cons_val_zero,
    centeringMean, fullWindowLoss, map_add, map_smul]
  module

end OriginalKExteriorCoPoissonAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
