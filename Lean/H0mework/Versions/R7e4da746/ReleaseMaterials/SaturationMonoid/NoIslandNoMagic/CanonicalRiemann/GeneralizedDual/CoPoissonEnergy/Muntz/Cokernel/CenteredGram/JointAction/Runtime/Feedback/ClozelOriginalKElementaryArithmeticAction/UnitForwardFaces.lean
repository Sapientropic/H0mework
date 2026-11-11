import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeWardCompactFee
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantMean

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.UnitForwardFaces
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKSourceResolventReconstruction
open OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction WholeBForcingSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "Q" => Constructor.zeroMean
local notation "ell" => CenteredCountingDual.logarithm
local notation "U" => unitResolventSource

local instance quarterComplete : CompleteSpace M := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem forward_raw : ∀ᵐ x : ℝ ∂volume, x ∈ symmetricInterval q →
    ConstantForward.value x = (Real.eulerMascheroniConstant : ℂ) + SmallScaleLog.logRaw x := by
  apply (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) ConstantForward.value,
    Lp.coeFn_add ((Real.eulerMascheroniConstant : ℂ) • intervalConstant q) SmallScaleLog.logL2,
    Lp.coeFn_smul (Real.eulerMascheroniConstant : ℂ) (intervalConstant q),
    intervalConstant_coeFn q, SmallScaleLog.log_coeFn] with x restricted added scalar constant logarithm
  have source := congrArg (fun value : Hq => value x) ConstantMean.forward_window
  change R ConstantForward.value x = _ at restricted
  simp only [Pi.smul_apply, smul_eq_mul] at scalar
  rw [restricted, added, Pi.add_apply, scalar, constant, logarithm] at source
  simpa only [smul_eq_mul, mul_one] using source

private theorem inward_forward_window (t : ℝ) (nn : 0 ≤ t) :
    R (burnolMultiplicativeDilation (-t) ConstantForward.value) =
      (Real.exp (-t/2) : ℂ) •
        (((Real.eulerMascheroniConstant : ℂ) - (t : ℂ)) • intervalConstant q + SmallScaleLog.logL2) := by
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-t)*x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.exp (-t)) (Real.exp_ne_zero (-t)))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation (-t) ConstantForward.value),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-t) ConstantForward.value),
    ae_restrict_of_ae (scale.ae forward_raw), ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
    Lp.coeFn_smul (Real.exp (-t/2) : ℂ)
      (((Real.eulerMascheroniConstant : ℂ) - (t : ℂ)) • intervalConstant q + SmallScaleLog.logL2),
    Lp.coeFn_add (((Real.eulerMascheroniConstant : ℂ) - (t : ℂ)) • intervalConstant q) SmallScaleLog.logL2,
    Lp.coeFn_smul ((Real.eulerMascheroniConstant : ℂ) - (t : ℂ)) (intervalConstant q),
    intervalConstant_coeFn q, SmallScaleLog.log_coeFn]
      with x restricted dilation moved inside nonzero outer added scalar constant logarithm
  have stays : Real.exp (-t)*x ∈ symmetricInterval q := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nn))
      (abs_nonneg x)).trans (by simpa only [one_mul] using abs_le.mpr inside)
  have logScale : SmallScaleLog.logRaw (Real.exp (-t)*x) = SmallScaleLog.logRaw x - (t : ℂ) := by
    unfold SmallScaleLog.logRaw
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_div_assoc,
      Real.log_mul (Real.exp_ne_zero _) (div_ne_zero (abs_ne_zero.mpr nonzero) (by norm_num)),
      Real.log_exp]
    push_cast
    ring
  change R (burnolMultiplicativeDilation (-t) ConstantForward.value) x = _ at restricted
  simp only [Pi.smul_apply, smul_eq_mul] at outer scalar
  rw [restricted, dilation, burnolL2RawNormalizedDilation, moved stays, logScale,
    outer, added, Pi.add_apply, scalar, constant, logarithm]
  simp only [mul_one]
  congr 1
  ring

private theorem inward_forward_centered (t : ℝ) (nn : 0 ≤ t) :
    Q (R (burnolMultiplicativeDilation (-t) ConstantForward.value)) =
      (Real.exp (-t/2) : ℂ) • ell := by
  rw [inward_forward_window t nn, map_smul, map_add, map_smul,
    Constructor.zeroMean_constant, smul_zero, zero_add]
  rfl

private theorem rbar_forward_centered (c : BurnolCompletedMellinCoordinate) :
    Q (R (sourceResolvent c ConstantForward.value)) = (-2 / star c.value) • ell := by
  let read : BurnolL2 →L[ℂ] M := Constructor.zeroMean.comp burnolQuarterRestriction
  have right : 1/4 < (star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have decay : (-(star c.value/2)).re < 0 := by
    simp only [Complex.neg_re, Complex.div_re, Complex.star_def, Complex.conj_re]
    norm_num
    linarith [c.rightHalf]
  have acted : Q (R (sourceResolvent c ConstantForward.value)) =
      -(∫ tau : ℝ in Ioi 0, Complex.exp (-(star c.value/2)*(tau : ℂ)) • ell) := by
    change read (burnolDirectRightResolvent (star c.value/2) ConstantForward.value) = _
    unfold burnolDirectRightResolvent
    rw [map_neg, ←read.integral_comp_comm
      (burnolDirectRightResolventIntegrand_integrableOn _ right ConstantForward.value)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro tau positive
    unfold burnolDirectRightResolventIntegrand
    change read (positiveMellinQuarterRightResolventWeight (star c.value/2) tau •
      burnolMultiplicativeDilation (-tau/2) ConstantForward.value) =
        Complex.exp (-(star c.value/2)*(tau : ℂ)) • ell
    rw [map_smul]
    change positiveMellinQuarterRightResolventWeight (star c.value/2) tau •
      Q (R (burnolMultiplicativeDilation (-tau/2) ConstantForward.value)) = _
    rw [show -tau/2 = -(tau/2) by ring,
      inward_forward_centered (tau/2) (by change 0 < tau at positive; linarith), smul_smul]
    congr 1
    unfold positiveMellinQuarterRightResolventWeight
    rw [Complex.ofReal_exp, ←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [acted, integral_smul_const, integral_exp_mul_complex_Ioi decay 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [←neg_smul]
  congr 1
  ring

/-- The original forward unit's complete inward R action generates its actual logarithmic face. -/
theorem forward_unit_position_source (c : BurnolCompletedMellinCoordinate) :
    Q (R (U c ConstantForward.value)) = GapEuler.gapMean q c • ell := by
  have nonzero : star c.value ≠ 0 := by
    intro equality
    have realPart := congrArg Complex.re equality
    simp only [Complex.star_def, Complex.conj_re, Complex.zero_re] at realPart
    linarith [c.rightHalf]
  have forward : Q (R ConstantForward.value) = ell := by
    rw [ConstantMean.forward_window, map_add, map_smul, Constructor.zeroMean_constant,
      smul_zero, zero_add]
    rfl
  rw [unitResolventSource, map_smul, map_sub, map_smul, map_smul, map_sub, map_smul,
    forward, rbar_forward_centered]
  have coefficient : (star c.value * GapEuler.gapMean q c) *
      (1 - ((1-star c.value)/2) * (-2/star c.value)) = GapEuler.gapMean q c := by
    field_simp [nonzero]
    ring
  calc
    _ = ((star c.value * GapEuler.gapMean q c) *
        (1 - ((1-star c.value)/2) * (-2/star c.value))) • ell := by module
    _ = _ := by rw [coefficient]

/-- Fourier and Tate use their separately paid reversal actions on the same full resolvent. -/
theorem forward_unit_fourier_source (c : BurnolCompletedMellinCoordinate) :
    fourierL2 (U c ConstantForward.value) =
      burnolTateReciprocalL2 (U c ConstantDual.value) := by
  have right : 1/4 < (star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  simp only [unitResolventSource, sourceResolvent, map_smul, map_sub,
    FiniteMobiusResolventFlux.fourier_R _ right, ConstantFourier.original_square,
    FiniteMobiusResolventFlux.tate_R _ right]

private theorem tate_compact_quarter (value : BurnolL2)
    (support : OriginalPaPhysicalGreen.originalPhysicalCutoff q value = value) :
    R (burnolTateReciprocalL2 value) = 0 := by
  have represented : (value : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (value : ℝ → ℂ) := by
    have read := OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn q value
    rwa [support] at read
  have reciprocal := burnolTateReciprocalRaw_ae_congr (Lp.memLp value)
    ((Lp.memLp value).ae_eq represented) represented
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolTateReciprocalL2 value),
    ae_restrict_of_ae (burnolTateReciprocalL2_coeFn value), ae_restrict_of_ae reciprocal,
    ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ)), Lp.coeFn_zero ℂ 2 μq]
      with x restricted actual source inside nonzero zeroAt
  have outside : x⁻¹ ∉ symmetricInterval q := by
    intro contrary
    have reciprocalBound := abs_le.mpr contrary
    rw [abs_inv, inv_le_comm₀ (abs_pos.mpr nonzero) (by norm_num)] at reciprocalBound
    norm_num at reciprocalBound
    linarith [abs_le.mpr inside]
  change R (burnolTateReciprocalL2 value) x = _ at restricted
  rw [restricted, actual, source, burnolTateReciprocalRaw, indicator_of_notMem outside, mul_zero]
  exact zeroAt.symm

/-- The actual zero-owned Z support, rather than the original K gap, pays this Fourier face. -/
theorem forward_unit_fourier_gap (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    R (fourierL2 (U c ConstantForward.value)) = 0 := by
  rw [forward_unit_fourier_source, ←elementary_reverse_unit_resolvent c zero]
  exact tate_compact_quarter _ (elementary_reverse_support c zero)

private theorem position_pair (value : BurnolL2) (test : M) :
    inner ℂ value (E (test : Hq)) = inner ℂ (Q (R value)) test := by
  have actual := ContinuousLinearMap.adjoint_inner_right R value (test : Hq)
  change inner ℂ value (E (test : Hq)) = _ at actual
  rw [actual]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right test _).symm

private theorem fourier_pair_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (test : Hq) : inner ℂ (U c ConstantForward.value) (fourierL2 (E test)) = 0 := by
  have actual := fourierL2.inner_map_map (U c ConstantForward.value) (fourierL2 (E test))
  rw [fourierL2_fourierL2] at actual
  have reflected : reflectL2 (E test) = E (reflectRestricted q test) := burnolRadiusZeroExtension_reflect q test
  rw [reflected] at actual
  have localRead := ContinuousLinearMap.adjoint_inner_right R (fourierL2 (U c ConstantForward.value))
    (reflectRestricted q test)
  change inner ℂ (fourierL2 (U c ConstantForward.value)) (E (reflectRestricted q test)) = _ at localRead
  rw [localRead, forward_unit_fourier_gap c zero, inner_zero_left] at actual
  exact actual.symm

/-- Both actual dependent faces are consumed in the original complete B correction. -/
theorem actual_compact_unit_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) : inner ℂ (U c ConstantForward.value) (compactCorrection c h) =
      star (GapEuler.gapMean q c) * inner ℂ ell (compactPosition c h) := by
  have scaled (a : ℂ) (x y : M) : inner ℂ (a • x) y = star a * inner ℂ x y :=
    inner_smul_left x y a
  rw [compactCorrection, inner_add_right, position_pair, forward_unit_position_source,
    scaled, fourier_pair_zero c zero, add_zero]

/-- The full original fee now reads only the generated log and original dual B source. -/
theorem actual_complete_compact_fee (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nn : 0 ≤ h) (bound : h ≤ Real.log 2) :
    inner ℂ (KCountingGram.value c) (compactCorrection c h) =
      (star (GapEuler.gapMean q c) - star (sourceFourierMean (sourceB c))) *
          inner ℂ ell (compactPosition c h) -
        inner ℂ (CountingDual.value c) (E (compactFourier c h : Hq)) := by
  rw [WholeWardCompactFee.actual_compact_correction_price c zero h nn bound,
    WholeWardCompactFee.compactFee, actual_compact_unit_price c zero h]
  ring

end OriginalKElementaryArithmeticAction.UnitForwardFaces
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
