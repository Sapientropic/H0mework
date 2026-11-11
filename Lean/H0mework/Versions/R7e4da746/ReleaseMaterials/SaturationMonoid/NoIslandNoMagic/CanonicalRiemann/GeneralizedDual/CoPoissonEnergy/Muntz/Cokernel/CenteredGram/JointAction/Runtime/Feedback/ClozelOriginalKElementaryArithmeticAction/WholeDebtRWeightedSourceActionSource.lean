import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRGapStateActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRWeightedSourceActionSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalWholeDebtRCorrectionActionSource
open OriginalWholeDebtRMixedGreenSource OriginalWholeDebtRNativeForcingSource
open OriginalWholeDebtRGapStateActionSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
open private actual_R_inner native_quarter_read whole_forcing_integrable actual_inner_forcing from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRNativeForcingSource
open private inputRaw input_read actedRaw acted_read prefixRaw acted_continuous actual_quarters nativeQuarter acted_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private input_band_read source_profile_continuous from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRMixedGreenSource
open private forcingB source_correction_H from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRGapStateActionSource
open private original_source_read original_source_raw_even native_pair_read native_pair_integrable mixed_half_weight_flux from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private outwardRaw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
local notation "q" => (1/4 : ℝ)
local instance : IsFiniteMeasure (volume.restrict (symmetricInterval q)) where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "R" => burnolDirectRightResolventCLM
local notation "C" => BandFullStockEuler.correctionRaw
local notation "G" => gapState
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
private def rate (c : BurnolCompletedMellinCoordinate) : ℂ := 2*c.value-1
private def kappa (c : BurnolCompletedMellinCoordinate) : ℂ := GapEuler.gapMean q c

private theorem value_ne_zero (c : BurnolCompletedMellinCoordinate) : c.value≠0 := by
  intro zero
  have h := c.rightHalf
  rw [zero] at h
  norm_num at h

private theorem one_sub_ne_zero (c : BurnolCompletedMellinCoordinate) : 1-c.value≠0 := by
  intro zero
  have re := congrArg Complex.re (sub_eq_zero.mp zero)
  simp only [Complex.one_re] at re
  linarith [c.belowOne]

private theorem current_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    ContinuousOn (sourceCurrent c i) (Icc p q) := by
  intro x hx
  exact (actual_source_current_derivative c i x
    (by linarith [hx.1,junctionPoint_bounds.1])).continuousAt.continuousWithinAt

private theorem input_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (bandInput c 0) (Icc p q) := by
  intro x hx
  have positive := mul_pos (Real.exp_pos junctionShift) (junctionPoint_bounds.1.trans_le hx.1)
  have moved : ContinuousAt (fun y : ℝ => Real.exp junctionShift*y) x :=
    continuousAt_const.mul continuousAt_id
  exact (continuousAt_const.add (continuousAt_const.mul
    ((source_profile_continuous c 0 positive).comp moved))).continuousWithinAt

private theorem power_continuous (_c : BurnolCompletedMellinCoordinate) (e : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ)^e) (Icc p q) := by
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x e
    (Or.inr (junctionPoint_bounds.1.trans_le hx.1).ne')).continuousWithinAt

private theorem band_int (f : ℝ → ℂ) (regular : ContinuousOn f (Icc p q)) :
    IntervalIntegrable f volume p q :=
  ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le junctionPoint_bounds.2.le] using regular)

private theorem first_at_p (c : BurnolCompletedMellinCoordinate) :
    sourceCurrent c 0 p= -2*meanCharge c 0/c.value := by
  rw [actual_R_current c 0 p ⟨le_rfl,junctionPoint_bounds.2.le⟩,
    actual_R_inner c 0 p junctionPoint_bounds.1 le_rfl]
  rfl

/-- The derivative is generated by the actual first prefix, with the original input charge. -/
theorem actual_weighted_derivative (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : p/2<x) :
    HasDerivAt (fun y : ℝ => (y : ℂ)^(1-c.value)*sourceCurrent c 0 y)
      (-rate c*((x : ℂ)^(-c.value)*sourceCurrent c 0 x)-
        2*((x : ℂ)^(-c.value)*bandInput c 0 x)) x := by
  have positive : 0<x := by linarith [junctionPoint_bounds.1]
  have power := (Complex.hasStrictDerivAt_cpow_const (c := 1-c.value)
    (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
  convert! power.mul (actual_source_current_derivative c 0 x inside) using 1
  dsimp only [Matrix.cons_val_zero,rate]
  have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  rw [show 1-c.value-1= -c.value by ring]
  rw [Complex.cpow_sub _ _ xn,Complex.cpow_one,Complex.cpow_neg]
  field_simp [xn]
  ring

theorem actual_weighted_band (c : BurnolCompletedMellinCoordinate) :
    -rate c*(∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*sourceCurrent c 0 x)=
      (q : ℂ)^(1-c.value)*qCurrent c 0-
        (p : ℂ)^(1-c.value)*(-2*meanCharge c 0/c.value)+
          2*(∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*bandInput c 0 x) := by
  have mass : IntervalIntegrable (fun x : ℝ => (x : ℂ)^(-c.value)*sourceCurrent c 0 x) volume p q :=
    band_int _ ((power_continuous c (-c.value)).mul (current_continuous c 0))
  have input : IntervalIntegrable (fun x : ℝ => (x : ℂ)^(-c.value)*bandInput c 0 x) volume p q :=
    band_int _ ((power_continuous c (-c.value)).mul (input_continuous c))
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    junctionPoint_bounds.2.le ((power_continuous c (1-c.value)).mul (current_continuous c 0))
    (fun x hx => actual_weighted_derivative c x (by linarith [hx.1,junctionPoint_bounds.1]))
    ((mass.const_mul (-rate c)).sub (input.const_mul 2))
  rw [intervalIntegral.integral_sub (mass.const_mul _) (input.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at generated
  dsimp only [Pi.mul_apply] at generated
  rw [actual_q_current,first_at_p] at generated
  linear_combination generated

theorem actual_constant_band (c : BurnolCompletedMellinCoordinate) :
    (1-c.value)*(∫ x : ℝ in p..q,sourceCurrent c 0 x)=
      (q : ℂ)*qCurrent c 0-(p : ℂ)*(-2*meanCharge c 0/c.value)+
        2*(∫ x : ℝ in p..q,bandInput c 0 x) := by
  have mass := band_int _ (current_continuous c 0)
  have input := band_int _ (input_continuous c)
  have dc : ContinuousOn (fun x : ℝ => (x : ℂ)*sourceCurrent c 0 x) (Icc p q) :=
    Complex.continuous_ofReal.continuousOn.mul (current_continuous c 0)
  have derivative (x : ℝ) (hx : x∈Ioo p q) :
      HasDerivAt (fun y : ℝ => (y : ℂ)*sourceCurrent c 0 y)
        ((1-c.value)*sourceCurrent c 0 x-2*bandInput c 0 x) x := by
    have cast : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using!
        Complex.ofRealCLM.hasDerivAt (x := x)
    convert! cast.mul (actual_source_current_derivative c 0 x
      (by linarith [hx.1,junctionPoint_bounds.1])) using 1
    dsimp only [Matrix.cons_val_zero]
    field_simp [Complex.ofReal_ne_zero.mpr (junctionPoint_bounds.1.trans hx.1).ne']
    ring
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    junctionPoint_bounds.2.le dc derivative ((mass.const_mul _).sub (input.const_mul 2))
  rw [intervalIntegral.integral_sub (mass.const_mul _) (input.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at generated
  rw [actual_q_current,first_at_p] at generated
  linear_combination generated

def weightedInput (c : BurnolCompletedMellinCoordinate) : ℂ :=
  meanCharge c 0*(p : ℂ)^(1-c.value)/(1-c.value)+
    (∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*bandInput c 0 x)

def constantInput (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (p : ℂ)*meanCharge c 0+(∫ x : ℝ in p..q,bandInput c 0 x)

/-- Both actual source moments and the complete two-leg adjoint fee remain explicit. -/
def sourcePrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -rate c*gapActionPrice c+(q : ℂ)^(1-c.value)*qCurrent c 0+2*weightedInput c+
    (2*rate c*star (kappa c)/(1-c.value))*((q : ℂ)*qCurrent c 0+2*constantInput c)

private def crossRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (burnolRieszReturnRaw c x)*actedRaw c 0 x-
    star (burnolRieszSingleFourierSourceRaw c x)*actedRaw c 1 x

private theorem acted_raw_even (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) :
    actedRaw c i (-x)=actedRaw c i x := by
  fin_cases i
  · change prefixRaw c (inputRaw c 0) (-x)=prefixRaw c (inputRaw c 0) x
    simp only [prefixRaw,abs_neg]
  · change outwardRaw c (fourierL2 (C c)) (-x)=outwardRaw c (fourierL2 (C c)) x
    simp only [outwardRaw,abs_neg]

private theorem pair_int (c : BurnolCompletedMellinCoordinate) (i j : Fin 2) :
    IntervalIntegrable (fun x : ℝ => star (originalSourceRaw c i x)*actedRaw c j x) volume (-q) q :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q≤q)).mpr
    (native_pair_integrable (originalSource c i : Hq) (nativeQuarter c j) _ _
      (original_source_read c i) (native_quarter_read c j))

private theorem pair_half (c : BurnolCompletedMellinCoordinate) (i j : Fin 2) :
    inner ℂ (originalSource c i : Hq) (nativeQuarter c j)=
      2*(∫ x : ℝ in 0..q,star (originalSourceRaw c i x)*actedRaw c j x) := by
  rw [native_pair_read _ _ _ _ (original_source_read c i) (native_quarter_read c j),
    intervalIntegral.integral_of_le (by norm_num : -q≤q),←integral_Icc_eq_integral_Ioc]
  have generated := even_half_integral (fun x : ℝ => star (originalSourceRaw c i x)*actedRaw c j x)
    (native_pair_integrable (originalSource c i : Hq) (nativeQuarter c j) _ _
      (original_source_read c i) (native_quarter_read c j))
    (fun x => by rw [original_source_raw_even,acted_raw_even])
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤q)]
  exact generated

private theorem cross_integrable (c : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (crossRaw c) volume 0 q := by
  have first := (pair_int c 1 0).mono_set (show uIcc 0 q⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤q),uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have second := (pair_int c 0 1).mono_set (show uIcc 0 q⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤q),uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  exact first.sub second

private theorem correction_half (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (forcingB c) (nativeFoot c 1)= -2*(∫ x : ℝ in 0..q,crossRaw c x) := by
  rw [←source_correction_H]
  have twice : fourierL2 (fourierL2 (R c (C c)))=R c (C c) := by
    rw [fourierL2_fourierL2]
    exact acted_even c 0
  have paired := fourierL2.inner_map_map (Eq (burnolRieszSingleFourierSource c : Hq))
    (fourierL2 (R c (C c)))
  rw [twice] at paired
  have first := ContinuousLinearMap.adjoint_inner_left Rq
    (fourierL2 (R c (C c))) (burnolRieszSingleFourierSource c : Hq)
  have second := ContinuousLinearMap.adjoint_inner_left Rq
    (R c (C c)) (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c) : Hq)
  change inner ℂ (Eq (burnolRieszSingleFourierSource c : Hq)) (fourierL2 (R c (C c)))=
    inner ℂ (burnolRieszSingleFourierSource c : Hq) (Rq (fourierL2 (R c (C c)))) at first
  change inner ℂ (Eq (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c) : Hq))
    (R c (C c))=inner ℂ (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c) : Hq)
      (Rq (R c (C c))) at second
  unfold OriginalRieszSourceGreen.sourceCorrection
  rw [inner_sub_left,paired,first,second]
  change inner ℂ (originalSource c 0 : Hq) (Rq (fourierL2 (R c (C c))))-
    inner ℂ (originalSource c 1 : Hq) (Rq (R c (C c)))=_
  have q1 := actual_quarters c 1
  have q0 := actual_quarters c 0
  change Rq (fourierL2 (R c (C c)))=nativeQuarter c 1 at q1
  change Rq (R c (C c))=nativeQuarter c 0 at q0
  rw [q1,q0,pair_half,pair_half]
  have firstInt := (pair_int c 1 0).mono_set (show uIcc 0 q⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤q),uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have secondInt := (pair_int c 0 1).mono_set (show uIcc 0 q⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤q),uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  change 2*(∫ x : ℝ in 0..q,star (originalSourceRaw c 0 x)*actedRaw c 1 x)-
    2*(∫ x : ℝ in 0..q,star (originalSourceRaw c 1 x)*actedRaw c 0 x)=
      -2*(∫ x : ℝ in 0..q,star (originalSourceRaw c 1 x)*actedRaw c 0 x-
        star (originalSourceRaw c 0 x)*actedRaw c 1 x)
  rw [intervalIntegral.integral_sub firstInt secondInt]
  ring

private theorem star_power (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    star ((x : ℂ)^(-star c.value))=(x : ℂ)^(-c.value) := by
  have arg : (x : ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.star_def,Complex.conj_ofReal,map_neg,Complex.conj_conj] using
    (Complex.cpow_conj (x : ℂ) (-star c.value) arg).symm

private def bandPowerMass (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((1/2 : ℂ)*(x : ℂ)^(-c.value)-star (kappa c))*sourceCurrent c 0 x

private theorem band_power_int (c : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (bandPowerMass c) volume p q :=
  band_int _ (((continuousOn_const.mul (power_continuous c (-c.value))).sub continuousOn_const).mul
    (current_continuous c 0))

private theorem mass_reduction (c : BurnolCompletedMellinCoordinate) :
    sourceMass c=(1/2 : ℂ)*gapActionPrice c+(∫ x : ℝ in p..q,bandPowerMass c x)+
      (∫ x : ℝ in 0..p,crossRaw c x) := by
  have ci := cross_integrable c
  have cip := ci.mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have cib := ci.mono_set (show uIcc p q⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc junctionPoint_bounds.1.le le_rfl)
  have profile (i : Fin 2) : ContinuousOn (sourceProfile c i) (Icc p q) :=
    fun x hx => (source_profile_continuous c i (junctionPoint_bounds.1.trans_le hx.1)).continuousWithinAt
  have mi : IntervalIntegrable (mixedMass c) volume p q :=
    band_int _ (((profile 0).star.mul (current_continuous c 0)).add
      ((profile 1).star.mul (current_continuous c 1)))
  have paid : (∫ x : ℝ in p..q,mixedMass c x)+(∫ x : ℝ in p..q,crossRaw c x)=
      ∫ x : ℝ in p..q,bandPowerMass c x := by
    rw [←intervalIntegral.integral_add mi cib]
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le junctionPoint_bounds.2.le]
    intro x hx
    have pos := junctionPoint_bounds.1.trans hx.1
    unfold mixedMass crossRaw bandPowerMass sourceProfile positionSource
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [←actual_R_current c 0 x ⟨hx.1.le,hx.2.le⟩,
      ←actual_R_current c 1 x ⟨hx.1.le,hx.2.le⟩,star_sub,star_sub,star_mul,
      star_power c x pos]
    rw [show star (1/2 : ℂ)=(1/2 : ℂ) by norm_num]
    unfold kappa
    ring
  have split := intervalIntegral.integral_add_adjacent_intervals cip cib
  unfold sourceMass
  rw [correction_half]
  linear_combination paid-split

private theorem profile_int (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    IntervalIntegrable (fun x : ℝ => star (sourceProfile c i x)) volume 0 q := by
  have raw : IntegrableOn (sourceProfile c i) (Ioc 0 q) := by
    fin_cases i
    · exact PositionSource.integrable c
    · have source : IntegrableOn (burnolRieszSingleFourierSourceRaw c) (symmetricInterval q) :=
        ((Lp.memLp (burnolRieszSingleFourierSource c : Hq)).integrable (by norm_num)).congr
        (burnolRieszSingleFourierSource_ae_raw c)
      exact source.mono_set (by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤q)).mpr
    ((@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp raw)

private theorem mean_balance (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (∫ x : ℝ in 0..p,star (sourceProfile c i x))+
      (∫ x : ℝ in p..q,star (sourceProfile c i x))=0 := by
  have pi := profile_int c i
  have inner := pi.mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have outer := pi.mono_set (show uIcc p q⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc junctionPoint_bounds.1.le le_rfl)
  rw [intervalIntegral.integral_add_adjacent_intervals inner outer,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤q)]
  rw [RCLike.star_def,integral_conj]
  fin_cases i
  · change star (∫ x : ℝ in Ioc 0 q,positionSource c x)=0
    rw [PositionSource.positive_mass_zero,star_zero]
  · change star (∫ x : ℝ in Ioc 0 q,burnolRieszSingleFourierSourceRaw c x)=0
    rw [DualSourceRaw.source_half_integral_zero,star_zero]

private def innerMass (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (sourceProfile c 0 x)*innerCurrent c 0 x+star (sourceProfile c 1 x)*innerCurrent c 1 x

private def innerFlux (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ)*(star (sourceProfile c 0 x)*innerCurrent c 0 x-
    star (sourceProfile c 1 x)*innerCurrent c 1 x)

private theorem inner_mass_int (c : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (innerMass c) volume 0 p := by
  have first := (profile_int c 0).mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have second := (pair_int c 0 1).mono_set (show uIcc 0 p⊆uIcc (-q) q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc (by norm_num) junctionPoint_bounds.2.le)
  have secondRead : IntervalIntegrable
      (fun x : ℝ => star (sourceProfile c 1 x)*innerCurrent c 1 x) volume 0 p := by
    apply second.congr_uIoo
    rw [uIoo_of_le junctionPoint_bounds.1.le]
    intro x hx
    change star (burnolRieszSingleFourierSourceRaw c x)*actedRaw c 1 x=_
    rw [actual_R_inner c 1 x hx.1 hx.2.le]
    rfl
  exact (first.mul_const (-2*meanCharge c 0/c.value)).add secondRead

private theorem inner_current_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0<x) :
    HasDerivAt (innerCurrent c i)
      (![(-c.value*innerCurrent c 0 x-2*meanCharge c 0)/(x : ℂ),
        ((c.value-1)*innerCurrent c 1 x+2*meanCharge c 1)/(x : ℂ)] i) x := by
  fin_cases i
  · change HasDerivAt (fun _ : ℝ => -2*meanCharge c 0/c.value)
      ((-c.value*(-2*meanCharge c 0/c.value)-2*meanCharge c 0)/(x : ℂ)) x
    convert! hasDerivAt_const x (-2*meanCharge c 0/c.value) using 1
    field_simp [value_ne_zero c]
    ring
  · change HasDerivAt (fun y : ℝ => 2*meanCharge c 1/(1-c.value)+unitCoefficient c*(y : ℂ)^(c.value-1))
      (((c.value-1)*(2*meanCharge c 1/(1-c.value)+unitCoefficient c*(x : ℂ)^(c.value-1))+
        2*meanCharge c 1)/(x : ℂ)) x
    have power := (Complex.hasStrictDerivAt_cpow_const (c := c.value-1)
      (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
    convert! (hasDerivAt_const x (2*meanCharge c 1/(1-c.value))).add
      (power.const_mul (unitCoefficient c)) using 1
    have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
    rw [show c.value-1-1=c.value-2 by ring]
    simp only [Complex.cpow_sub _ _ xn,Complex.cpow_one,Complex.cpow_two]
    field_simp [one_sub_ne_zero c,xn]
    ring

private theorem inner_flux_derivative (c : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0<x) :
    HasDerivAt (innerFlux c)
      (innerForcing c x-rate c*innerMass c x-
        2*(meanCharge c 0*star (sourceProfile c 0 x)+meanCharge c 1*star (sourceProfile c 1 x))) x := by
  have cast : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using!
      Complex.ofRealCLM.hasDerivAt (x := x)
  have first := PositionSource.derivative c x positive
  have second := sourceRaw_hasDerivAt c x positive.ne'
  convert! cast.mul ((first.star.mul (inner_current_derivative c 0 x positive)).sub
    (second.star.mul (inner_current_derivative c 1 x positive))) using 1
  have fs := congrArg star (BandFiniteSourcePrice.position_source_euler c x positive)
  have gs := congrArg star (BandFiniteSourcePrice.fourier_source_euler c x positive.ne')
  simp only [star_add,star_mul,star_sub,star_star,star_div₀,star_ofNat,star_one,star_neg,
    show star (x : ℂ)=(x : ℂ) from Complex.conj_ofReal x,
    actual_forcing_columns,Matrix.cons_val_zero,Matrix.cons_val_one] at fs gs
  dsimp only [innerFlux,innerForcing,innerMass,rate,sourceProfile,Matrix.cons_val_zero,
    Matrix.cons_val_one,Pi.sub_apply,Pi.mul_apply]
  simp only [star_sub,star_one]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  linear_combination -(innerCurrent c 0 x)*fs+(innerCurrent c 1 x)*gs

private theorem unit_B_origin (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x : ℝ => (x : ℂ)^c.value*star (burnolRieszSingleFourierSourceRaw c x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have positive : 0<(c.value-(1/2 : ℂ)).re := by norm_num [Complex.sub_re];linarith [c.rightHalf]
  have nonzero : c.value-(1/2 : ℂ)≠0 := ne_of_apply_ne Complex.re positive.ne'
  have residual := (Complex.continuousAt_ofReal_cpow_const 0 (c.value-(1/2 : ℂ)) (Or.inl positive)).tendsto.norm
  simp only [Complex.ofReal_zero,Complex.zero_cpow nonzero,norm_zero] at residual
  have product : Tendsto (fun x : ℝ => ‖(x : ℂ)^(c.value-(1/2 : ℂ))‖*
      ‖(Real.sqrt |x| : ℂ)*burnolRieszSingleFourierSourceRaw c x‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using
      (residual.mul (source_halfWeight_origin c).norm).mono_left nhdsWithin_le_nhds
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply product.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0<x at hx
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hx]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx c.value,
    Complex.norm_cpow_eq_rpow_re_of_pos hx (c.value-(1/2 : ℂ))]
  norm_num only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
  rw [Real.sqrt_eq_rpow,←mul_assoc,←Real.rpow_add hx]
  rw [show c.value.re-1/2+(1/2 : ℝ)=c.value.re by ring]

private theorem inner_flux_origin (c : BurnolCompletedMellinCoordinate) :
    Tendsto (innerFlux c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have position : Tendsto (fun x : ℝ => (x : ℂ)*star (positionSource c x))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have paid := (PositionOrigin.weighted_origin_zero c).star
    simp only [star_zero,star_mul] at paid
    exact paid.congr' (Eventually.of_forall (fun x => by
      rw [show star (x : ℂ)=(x : ℂ) from Complex.conj_ofReal x]
      ring))
  have bounded := mixed_half_weight_flux (burnolRieszSingleFourierSourceRaw c) (source_halfWeight_origin c)
  have first : Tendsto (fun x : ℝ => (x : ℂ)*star (positionSource c x)*(-2*meanCharge c 0/c.value))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using (position.mul_const (-2*meanCharge c 0/c.value)).mono_left
      nhdsWithin_le_nhds
  have second : Tendsto (fun x : ℝ => (x : ℂ)*star (burnolRieszSingleFourierSourceRaw c x)*
      (2*meanCharge c 1/(1-c.value))+(x : ℂ)^c.value*star (burnolRieszSingleFourierSourceRaw c x)*unitCoefficient c)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul,zero_add] using
      (((bounded.mul_const (2*meanCharge c 1/(1-c.value))).mono_left
        nhdsWithin_le_nhds).add ((unit_B_origin c).mul_const (unitCoefficient c)))
  have generated := first.sub second
  simp only [sub_zero] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0<x at hx
  dsimp only [innerFlux,innerCurrent,sourceProfile,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),Complex.cpow_one]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

private theorem inner_green (c : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in 0..p,innerForcing c x)-rate c*(∫ x : ℝ in 0..p,innerMass c x)-
      2*(meanCharge c 0*(∫ x : ℝ in 0..p,star (sourceProfile c 0 x))+
        meanCharge c 1*(∫ x : ℝ in 0..p,star (sourceProfile c 1 x)))=nativePFlux c := by
  have first := (profile_int c 0).mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have second := (profile_int c 1).mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have forcing : IntervalIntegrable (innerForcing c) volume 0 p := by
    have paid := (whole_forcing_integrable c).mono_set (show uIcc 0 p⊆uIcc (-q) q by
      rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : -q≤q)]
      exact Icc_subset_Icc (by norm_num) junctionPoint_bounds.2.le)
    apply paid.congr_uIoo
    rw [uIoo_of_le junctionPoint_bounds.1.le]
    exact fun x hx => actual_inner_forcing c x hx.1 hx.2.le
  have upper : Tendsto (innerFlux c) (𝓝[<] p) (𝓝 (innerFlux c p)) :=
    (inner_flux_derivative c p junctionPoint_bounds.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto junctionPoint_bounds.1
    (fun x hx => inner_flux_derivative c x hx.1)
    ((forcing.sub ((inner_mass_int c).const_mul _)).sub
      (((first.const_mul _).add (second.const_mul _)).const_mul 2))
    (inner_flux_origin c) upper
  rw [intervalIntegral.integral_sub (forcing.sub ((inner_mass_int c).const_mul _))
      (((first.const_mul _).add (second.const_mul _)).const_mul _),
    intervalIntegral.integral_sub forcing ((inner_mass_int c).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (first.const_mul _) (second.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,sub_zero] at generated
  exact generated

private theorem inner_power_balance (c : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in 0..p,innerMass c x)+(∫ x : ℝ in 0..p,crossRaw c x)=
      (-2*meanCharge c 0/c.value)*((1/2 : ℂ)*(p : ℂ)^(1-c.value)/(1-c.value)-
        star (kappa c)*(p : ℂ)) := by
  have power : IntervalIntegrable (fun x : ℝ => (x : ℂ)^(-c.value)) volume 0 p := by
    apply intervalIntegral.intervalIntegrable_cpow'
    simp only [neg_re]
    linarith [c.belowOne]
  have constant : IntervalIntegrable (fun _ : ℝ => star (kappa c)) volume 0 p :=
    intervalIntegrable_const
  have ci := (cross_integrable c).mono_set (show uIcc 0 p⊆uIcc 0 q by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  calc
    _=∫ x : ℝ in 0..p,(-2*meanCharge c 0/c.value)*((1/2 : ℂ)*(x : ℂ)^(-c.value)-star (kappa c)) := by
      rw [←intervalIntegral.integral_add (inner_mass_int c) ci]
      apply intervalIntegral.integral_congr_uIoo
      rw [uIoo_of_le junctionPoint_bounds.1.le]
      intro x hx
      unfold innerMass crossRaw sourceProfile positionSource
      dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      rw [actual_R_inner c 0 x hx.1 hx.2.le,actual_R_inner c 1 x hx.1 hx.2.le,
        star_sub,star_sub,star_mul,star_power c x hx.1]
      rw [show star (1/2 : ℂ)=(1/2 : ℂ) by norm_num]
      dsimp only [innerCurrent,kappa,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    _=_ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (power.const_mul _) constant,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const,integral_cpow (Or.inl (by simp only [neg_re];linarith [c.belowOne]))]
      simp only [show -c.value+1=1-c.value by ring,Complex.ofReal_zero,
        Complex.zero_cpow (one_sub_ne_zero c),sub_zero,Complex.real_smul]
      ring

private theorem band_power_read (c : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in p..q,bandPowerMass c x)=
      (1/2 : ℂ)*(∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*sourceCurrent c 0 x)-
        star (kappa c)*(∫ x : ℝ in p..q,sourceCurrent c 0 x) := by
  have mass : IntervalIntegrable (fun x : ℝ => (x : ℂ)^(-c.value)*sourceCurrent c 0 x) volume p q :=
    band_int _ ((power_continuous c (-c.value)).mul (current_continuous c 0))
  have plain := band_int _ (current_continuous c 0)
  have same : bandPowerMass c=fun x : ℝ => (1/2 : ℂ)*((x : ℂ)^(-c.value)*sourceCurrent c 0 x)-
      star (kappa c)*sourceCurrent c 0 x := by
    funext x
    unfold bandPowerMass
    ring
  rw [same,intervalIntegral.integral_sub (mass.const_mul _) (plain.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

private theorem finite_price_mass_settlement (c : BurnolCompletedMellinCoordinate) :
    finitePrice c= -rate c*gapActionPrice c-
      rate c*(∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*sourceCurrent c 0 x)+
      2*rate c*star (kappa c)*(∫ x : ℝ in p..q,sourceCurrent c 0 x)-
      rate c*(-2*meanCharge c 0/c.value)*(p : ℂ)^(1-c.value)/(1-c.value)+
      2*rate c*star (kappa c)*(p : ℂ)*(-2*meanCharge c 0/c.value) := by
  rw [OriginalWholeDebtRGapStateActionSource.actual_finite_price_source]
  change 2*(nativePFlux c-(∫ x : ℝ in 0..p,innerForcing c x)-rate c*sourceMass c)-
    4*(meanCharge c 0*(∫ x : ℝ in p..q,star (sourceProfile c 0 x))+
      meanCharge c 1*(∫ x : ℝ in p..q,star (sourceProfile c 1 x)))=_
  rw [mass_reduction,band_power_read]
  have generated := inner_green c
  have power := inner_power_balance c
  have first := mean_balance c 0
  have second := mean_balance c 1
  linear_combination -2*generated-2*rate c*power-4*meanCharge c 0*first-4*meanCharge c 1*second

theorem actual_finite_price_source (c : BurnolCompletedMellinCoordinate) :
    finitePrice c=sourcePrice c := by
  rw [finite_price_mass_settlement]
  unfold sourcePrice weightedInput constantInput
  have weighted := actual_weighted_band c
  have constant := actual_constant_band c
  have resolved : (∫ x : ℝ in p..q,sourceCurrent c 0 x)=
      ((q : ℂ)*qCurrent c 0-(p : ℂ)*(-2*meanCharge c 0/c.value)+
        2*(∫ x : ℝ in p..q,bandInput c 0 x))/(1-c.value) :=
    (eq_div_iff (one_sub_ne_zero c)).mpr (by linear_combination constant)
  rw [resolved]
  have weighted' : rate c*(∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*sourceCurrent c 0 x)=
      -((q : ℂ)^(1-c.value)*qCurrent c 0-(p : ℂ)^(1-c.value)*(-2*meanCharge c 0/c.value)+
        2*(∫ x : ℝ in p..q,(x : ℂ)^(-c.value)*bandInput c 0 x)) := by
    linear_combination -weighted
  rw [weighted']
  field_simp [value_ne_zero c,one_sub_ne_zero c]
  unfold rate
  ring

theorem actual_fixed_residual_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    -burnolPaFixedShiftResidual c zero=
      (pairedMellinTranslationCharacter c.value junctionShift-
        pairedMellinTranslationCharacter (star c.value) junctionShift)*kernelSelfSource c+
      (1/2 : ℂ)*star (sourcePrice c) := by
  rw [OriginalWholeDebtRNativeForcingSource.actual_fixed_residual,actual_finite_price_source]

end OriginalWholeDebtRWeightedSourceActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
