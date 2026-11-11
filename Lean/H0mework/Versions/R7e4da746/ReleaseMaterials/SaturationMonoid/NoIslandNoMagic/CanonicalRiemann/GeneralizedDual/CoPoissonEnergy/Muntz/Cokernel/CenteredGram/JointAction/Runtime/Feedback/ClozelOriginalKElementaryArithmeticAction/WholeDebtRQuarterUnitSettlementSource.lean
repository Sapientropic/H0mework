import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRWeightedSourceActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRQuarterUnitSettlementSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalWholeDebtRCorrectionActionSource
open OriginalWholeDebtRMixedGreenSource OriginalWholeDebtRNativeForcingSource
open OriginalWholeDebtRGapStateActionSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
open private inputRaw input_read actedRaw prefixRaw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private actual_input_inner from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRNativeForcingSource
open private input_band_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRMixedGreenSource
open private extension_C_price power_first constant_first forcingB from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRGapStateActionSource
open private rate kappa from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRWeightedSourceActionSource
open private native_pair_read native_pair_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
local notation "q" => (1/4 : ℝ)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "Cq" => intervalConstant q
local notation "C" => BandFullStockEuler.correctionRaw
local notation "T" => burnolTruncatedFourier
local instance : IsFiniteMeasure (volume.restrict (symmetricInterval q)) where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def powerFee (c : BurnolCompletedMellinCoordinate) : ℂ :=
  nativeAlpha c+inner ℂ (T (SingularCounting.powerL2 c)) (sourceSecond c : Hq)

def constantFee (c : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (T Cq) (sourceSecond c : Hq)

private theorem input_quarter_read (c : BurnolCompletedMellinCoordinate) :
    (Rq (C c) : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] inputRaw c 0 := by
  have raw := input_read c 0
  change (C c : ℝ → ℂ)=ᵐ[volume] inputRaw c 0 at raw
  exact (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (C c)).trans (ae_restrict_of_ae raw)

private theorem input_raw_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    inputRaw c 0 (-x)=inputRaw c 0 x := by
  unfold inputRaw burnolEvenRaw
  simp only [neg_neg]
  ring

private theorem quarter_half (c : BurnolCompletedMellinCoordinate) (value : Hq) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw)
    (even : ∀ x,raw (-x)=raw x) :
    inner ℂ value (Rq (C c))=2*(∫ x : ℝ in 0..q,star (raw x)*inputRaw c 0 x) := by
  rw [native_pair_read _ _ _ _ read (input_quarter_read c),
    intervalIntegral.integral_of_le (by norm_num : -q≤q),←integral_Icc_eq_integral_Ioc]
  have paid := even_half_integral (fun x : ℝ => star (raw x)*inputRaw c 0 x)
    (native_pair_integrable value (Rq (C c)) _ _ read (input_quarter_read c))
    (fun x => by rw [even,input_raw_even])
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤q)]
  exact paid

private theorem native_power_pair (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (SingularCounting.powerL2 c) (Rq (C c))=powerFee c := by
  have extension := ContinuousLinearMap.adjoint_inner_left Rq (C c) (SingularCounting.powerL2 c)
  change inner ℂ (Eq (SingularCounting.powerL2 c)) (C c)=
    inner ℂ (SingularCounting.powerL2 c) (Rq (C c)) at extension
  rw [←extension,extension_C_price,power_first]
  rfl

private theorem power_raw_weight (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    star (SingularCounting.powerRaw c x)=(x : ℂ)^(c.value-1) := by
  unfold SingularCounting.powerRaw
  rw [abs_of_pos positive]
  have arg : (x : ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.star_def,Complex.conj_ofReal,map_sub,map_one,Complex.conj_conj] using
    (Complex.cpow_conj (x : ℂ) (star c.value-1) arg).symm

/-- This is the inward x^(c-1) source pairing, distinct from weightedInput's x^(-c). -/
theorem actual_power_source (c : BurnolCompletedMellinCoordinate) :
    powerFee c=2*(∫ x : ℝ in 0..q,(x : ℂ)^(c.value-1)*inputRaw c 0 x) := by
  rw [←native_power_pair,quarter_half c (SingularCounting.powerL2 c) (SingularCounting.powerRaw c)
    (SingularCounting.power_coeFn c) (fun x => by simp only [SingularCounting.powerRaw,abs_neg])]
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le (by norm_num : (0 : ℝ)≤q)]
  intro x hx
  change star (SingularCounting.powerRaw c x)*inputRaw c 0 x=_
  rw [power_raw_weight c x hx.1]

theorem actual_q_prefix (c : BurnolCompletedMellinCoordinate) :
    qCurrent c 0= -(q : ℂ)^(-c.value)*powerFee c := by
  rw [←actual_q_current c 0,actual_R_current c 0 q ⟨junctionPoint_bounds.2.le,le_rfl⟩]
  change prefixRaw c (inputRaw c 0) q=_
  unfold prefixRaw
  rw [abs_of_pos (by norm_num : (0 : ℝ)<q),actual_power_source]
  ring

private theorem input_integrable (c : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (inputRaw c 0) volume 0 q := by
  have raw : IntegrableOn (inputRaw c 0) (symmetricInterval q) :=
    ((Lp.memLp (Rq (C c))).integrable (by norm_num)).congr (input_quarter_read c)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤q)).mpr
    (raw.mono_set (by intro x hx;exact ⟨by linarith [hx.1],hx.2⟩))

private theorem actual_input_mean (c : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in 0..q,inputRaw c 0 x)=OriginalWholeDebtRWeightedSourceActionSource.constantInput c := by
  have full := input_integrable c
  have first := full.mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have second := full.mono_set (show uIcc p q⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc junctionPoint_bounds.1.le le_rfl)
  rw [←intervalIntegral.integral_add_adjacent_intervals first second]
  have inner : (∫ x : ℝ in 0..p,inputRaw c 0 x)=(p : ℂ)*meanCharge c 0 := by
    calc
      _=∫ _ : ℝ in 0..p,meanCharge c 0 := by
        apply intervalIntegral.integral_congr_uIoo
        rw [uIoo_of_le junctionPoint_bounds.1.le]
        exact fun x hx => actual_input_inner c 0 x (by rw [abs_of_pos hx.1];exact hx.2.le)
      _=_ := by rw [intervalIntegral.integral_const];simp only [sub_zero,Complex.real_smul]
  have outer : (∫ x : ℝ in p..q,inputRaw c 0 x)=∫ x : ℝ in p..q,bandInput c 0 x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le junctionPoint_bounds.2.le]
    have native := input_read c 0
    change (C c : ℝ → ℂ)=ᵐ[volume] inputRaw c 0 at native
    have rawRead : (C c : ℝ → ℂ)=ᵐ[volume.restrict (Ioc p q)] inputRaw c 0 :=
      ae_restrict_of_ae native
    have bandRead := input_band_read c 0
    filter_upwards [rawRead,bandRead] with x raw band
    change (C c) x=bandInput c 0 x at band
    exact raw.symm.trans band
  rw [inner,outer]
  rfl

theorem actual_constant_source (c : BurnolCompletedMellinCoordinate) :
    constantFee c=2*OriginalWholeDebtRWeightedSourceActionSource.constantInput c := by
  have extension := ContinuousLinearMap.adjoint_inner_left Rq (C c) Cq
  change inner ℂ (Eq Cq) (C c)=inner ℂ Cq (Rq (C c)) at extension
  have paid : inner ℂ Cq (Rq (C c))=constantFee c := by
    rw [←extension,extension_C_price,constant_first,zero_add]
    rfl
  rw [←paid,quarter_half c Cq (fun _ => (1 : ℂ)) (intervalConstant_coeFn q) (fun _ => rfl)]
  simp only [star_one,one_mul]
  rw [actual_input_mean]

private theorem rate_ne_zero (c : BurnolCompletedMellinCoordinate) : 2*c.value-1≠0 := by
  intro zero
  have re := congrArg Complex.re zero
  norm_num at re
  linarith [c.rightHalf]

private theorem one_sub_ne_zero (c : BurnolCompletedMellinCoordinate) : 1-c.value≠0 := by
  intro zero
  have re := congrArg Complex.re (sub_eq_zero.mp zero)
  simp only [Complex.one_re] at re
  linarith [c.belowOne]

private theorem quarter_star_power (exponent : ℂ) :
    star ((q : ℂ)^exponent)=(q : ℂ)^star exponent := by
  have arg : (q : ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ)≤q)]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.star_def,Complex.conj_ofReal] using
    (Complex.cpow_conj (q : ℂ) exponent arg).symm

/-- All q and power-unit fees settle through the actual prefix and both original C legs. -/
def sourcePrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  2*inner ℂ (forcingB c) (sourceSecond c)+
    2*OriginalWholeDebtRWeightedSourceActionSource.weightedInput c-
      4*star (GapEuler.gapMean q c)*OriginalWholeDebtRWeightedSourceActionSource.constantInput c

theorem actual_unit_settlement (c : BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRWeightedSourceActionSource.sourcePrice c=sourcePrice c := by
  unfold OriginalWholeDebtRWeightedSourceActionSource.sourcePrice
  have source : gapActionPrice c=star (outerRate c)*inner ℂ (forcingB c) (sourceSecond c)+
      star (gapConstant c)*constantFee c+star (gapPower c)*powerFee c := rfl
  rw [source,actual_q_prefix,actual_constant_source]
  unfold sourcePrice gapConstant gapPower outerRate rate kappa
  simp only [star_div₀,star_neg,star_ofNat,star_mul,star_sub,star_one,star_star,
    quarter_star_power,star_add]
  have qfirst : (q : ℂ)^(1-c.value)=(q : ℂ)*(q : ℂ)^(-c.value) := by
    rw [show 1-c.value=1+(-c.value) by ring,
      Complex.cpow_add _ _ (by norm_num : (q : ℂ)≠0),Complex.cpow_one]
  have qtwice : (q : ℂ)^(1-2*c.value)=(q : ℂ)*(q : ℂ)^(-c.value)*(q : ℂ)^(-c.value) := by
    rw [show 1-2*c.value=1+(-c.value)+(-c.value) by ring,
      Complex.cpow_add _ _ (by norm_num : (q : ℂ)≠0),
      Complex.cpow_add _ _ (by norm_num : (q : ℂ)≠0),Complex.cpow_one]
  have gap := congrArg star (GapEuler.gapMean_primitive q (by norm_num) c)
  simp only [star_mul,star_sub,star_one,star_star,quarter_star_power,star_div₀,star_ofNat,
    star_neg] at gap
  have unit : star (GapEuler.gapMean q c)=(1/2 : ℂ)*(q : ℂ)^(-c.value)/(1-c.value) := by
    apply (eq_div_iff (one_sub_ne_zero c)).mpr
    linear_combination gap
  simp only [show c.value*2=2*c.value by ring]
  rw [unit,qfirst,qtwice]
  field_simp [rate_ne_zero c,one_sub_ne_zero c]
  ring

theorem actual_finite_price_source (c : BurnolCompletedMellinCoordinate) :
    finitePrice c=sourcePrice c := by
  rw [OriginalWholeDebtRWeightedSourceActionSource.actual_finite_price_source,actual_unit_settlement]

theorem actual_fixed_residual_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    -burnolPaFixedShiftResidual c zero=
      (pairedMellinTranslationCharacter c.value junctionShift-
        pairedMellinTranslationCharacter (star c.value) junctionShift)*kernelSelfSource c+
      (1/2 : ℂ)*star (sourcePrice c) := by
  rw [OriginalWholeDebtRWeightedSourceActionSource.actual_fixed_residual_source,actual_unit_settlement]

end OriginalWholeDebtRQuarterUnitSettlementSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
