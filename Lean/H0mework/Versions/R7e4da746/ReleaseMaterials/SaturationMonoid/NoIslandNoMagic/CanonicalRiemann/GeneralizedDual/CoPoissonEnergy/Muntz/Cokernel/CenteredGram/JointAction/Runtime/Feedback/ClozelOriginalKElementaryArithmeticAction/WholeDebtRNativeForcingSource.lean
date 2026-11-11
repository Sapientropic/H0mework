import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRMixedGreenSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRNativeForcingSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalWholeDebtRCorrectionActionSource
open OriginalWholeDebtRMixedGreenSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
open private nativeQuarter actual_quarters actual_face_feet acted_even flip inputRaw bareInputRaw input_read actedRaw prefixRaw acted_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private outwardRaw face from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
open private return_raw_even native_pair_integrable native_pair_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private tailSeed from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRMixedGreenSource
open private first_B_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private evenPart_of_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
local notation "q" => (1/4 : ℝ)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "C" => BandFullStockEuler.correctionRaw
local notation "R" => burnolDirectRightResolventCLM
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Rq" => burnolQuarterRestriction
local notation "mu" => burnolQuarterMeanCoefficient
local notation "phi" => BandFiniteSourcePrice.sourceColumn
local notation "A" => Kernel.A
local notation "beta" => Kernel.beta
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def nativeDrive (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : M :=
  nativeFoot c i+S (nativeFoot c (flip i))

private theorem actual_input_inner (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (small : |x|≤p) : inputRaw c i x=meanCharge c i := by
  have inside : x∈symmetricInterval q := abs_le.mp (small.trans junctionPoint_bounds.2.le)
  have reverse : -x∈symmetricInterval q := by
    exact ⟨by linarith [inside.2],by linarith [inside.1]⟩
  have sx : |(-x)|≤p := by simpa only [abs_neg] using small
  have mz (j : Fin 2) : burnolMeanZeroFourierRaw (sourcePartner c j) |x|=
      burnolMeanZeroFourierRaw (sourcePartner c j) x := by
    by_cases positive : 0≤x
    · rw [abs_of_nonneg positive]
    · rw [abs_of_neg (lt_of_not_ge positive)]
      exact return_raw_even c j x
  have fr (j : Fin 2) : burnolRadiusTruncatedFourierRaw q (sourcePartner c j : Hq) (-x)=
      burnolRadiusTruncatedFourierRaw q (sourcePartner c j : Hq) x := by
    have paid := return_raw_even c j x
    change burnolRadiusTruncatedFourierRaw q (sourcePartner c j : Hq) (-x)-_=
      burnolRadiusTruncatedFourierRaw q (sourcePartner c j : Hq) x-_ at paid
    linear_combination paid
  fin_cases i
  · change burnolEvenRaw (fun t => (symmetricInterval q).indicator (sourceRaw c 0) t+
        burnolRadiusTruncatedFourierRaw q (sourceSecond c : Hq) t) x=meanCharge c 0
    dsimp only [burnolEvenRaw]
    rw [indicator_of_mem inside,indicator_of_mem reverse]
    unfold sourceRaw
    rw [if_pos small,if_pos sx]
    simp only [abs_neg,sourceInnerRaw,mz]
    simp only [meanCharge,sourcePartner,Matrix.cons_val_zero]
    unfold burnolMeanZeroFourierRaw
    rw [show burnolRadiusTruncatedFourierRaw q (sourceSecond c : Hq) (-x)=
      burnolRadiusTruncatedFourierRaw q (sourceSecond c : Hq) x from fr 0]
    ring
  · change burnolEvenRaw (fun t => burnolRadiusTruncatedFourierRaw q (sourceFirst c : Hq) t+
        (symmetricInterval q).indicator (sourceRaw c 1) t) x=meanCharge c 1
    dsimp only [burnolEvenRaw]
    rw [indicator_of_mem inside,indicator_of_mem reverse]
    unfold sourceRaw
    rw [if_pos small,if_pos sx]
    simp only [abs_neg,sourceInnerRaw,mz]
    simp only [meanCharge,sourcePartner,Matrix.cons_val_one,Matrix.cons_val_zero]
    unfold burnolMeanZeroFourierRaw
    rw [show burnolRadiusTruncatedFourierRaw q (sourceFirst c : Hq) (-x)=
      burnolRadiusTruncatedFourierRaw q (sourceFirst c : Hq) x from fr 1]
    ring

/-- The actual outward unit is retained before the regular quarter source is constructed. -/
def unitCoefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*(tailSeed c+meanCharge c 1*(p : ℂ)^(1-c.value)/(1-c.value))

private theorem value_ne_zero (c : BurnolCompletedMellinCoordinate) : c.value≠0 := by
  intro zero
  have := c.rightHalf
  rw [zero] at this
  norm_num at this

private theorem one_sub_ne_zero (c : BurnolCompletedMellinCoordinate) : 1-c.value≠0 := by
  intro zero
  have re := congrArg Complex.re (sub_eq_zero.mp zero)
  simp only [Complex.one_re] at re
  linarith [c.belowOne]

private theorem actual_R_inner (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0<x) (small : x≤p) :
    actedRaw c i x= ![-2*meanCharge c 0/c.value,
      2*meanCharge c 1/(1-c.value)+unitCoefficient c*(x : ℂ)^(c.value-1)] i := by
  have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have pn : (x : ℂ)^c.value≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl xn)
  fin_cases i
  · have same : (∫ t : ℝ in 0..x,(t : ℂ)^(c.value-1)*inputRaw c 0 t)=
        meanCharge c 0*((x : ℂ)^c.value/c.value) := by
      calc
        _=∫ t : ℝ in 0..x,meanCharge c 0*(t : ℂ)^(c.value-1) := by
          apply intervalIntegral.integral_congr_uIoo
          rw [uIoo_of_le positive.le]
          intro t ht
          dsimp only
          rw [actual_input_inner c 0 t (by rw [abs_of_pos ht.1];exact ht.2.le.trans small)]
          ring
        _=meanCharge c 0*(∫ t : ℝ in 0..x,(t : ℂ)^(c.value-1)) :=
          intervalIntegral.integral_const_mul _ _
        _=_ := by
          rw [integral_cpow (Or.inl (by simpa using (show -1<(c.value-1).re by simp only [sub_re,one_re];linarith [c.rightHalf])))]
          simp only [show c.value-1+1=c.value by ring,Complex.ofReal_zero,
            Complex.zero_cpow (value_ne_zero c),sub_zero]
    change prefixRaw c (inputRaw c 0) x= -2*meanCharge c 0/c.value
    unfold prefixRaw
    rw [abs_of_pos positive,same,Complex.cpow_neg]
    field_simp [pn,value_ne_zero c]
  · have paid := burnolRadiusMellinWeight_integrableOn_tail x positive c.value c.rightHalf (fourierL2 (C c))
    have split := intervalIntegral.integral_Ioi_sub_Ioi paid small
    have same : (∫ t : ℝ in x..p,(t : ℂ)^(-c.value)*(fourierL2 (C c)) t)=
        meanCharge c 1*((p : ℂ)^(1-c.value)-(x : ℂ)^(1-c.value))/(1-c.value) := by
      calc
        _=∫ t : ℝ in x..p,meanCharge c 1*(t : ℂ)^(-c.value) := by
          apply intervalIntegral.integral_congr_ae_restrict
          have raw := ae_restrict_of_ae (s := uIoc x p) (input_read c 1)
          filter_upwards [raw,ae_restrict_mem measurableSet_uIoc] with t read ht
          rw [uIoc_of_le small] at ht
          change (fourierL2 (C c)) t=inputRaw c 1 t at read
          rw [read,actual_input_inner c 1 t (by rw [abs_of_pos (positive.trans ht.1)];exact ht.2)]
          ring
        _=meanCharge c 1*(∫ t : ℝ in x..p,(t : ℂ)^(-c.value)) :=
          intervalIntegral.integral_const_mul _ _
        _=_ := by
          rw [integral_cpow (Or.inl (by simp only [neg_re];linarith [c.belowOne]))]
          rw [show -c.value+1=1-c.value by ring]
          ring
    rw [same] at split
    change outwardRaw c (fourierL2 (C c)) x=
      2*meanCharge c 1/(1-c.value)+unitCoefficient c*(x : ℂ)^(c.value-1)
    unfold outwardRaw
    rw [abs_of_pos positive,sub_eq_iff_eq_add.mp split]
    unfold unitCoefficient tailSeed
    simp only [Complex.cpow_sub _ _ xn,Complex.cpow_one,Complex.cpow_neg]
    field_simp [one_sub_ne_zero c,xn,pn]
    ring


private theorem native_quarter_drive (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Constructor.zeroMean (nativeQuarter c i)=nativeDrive c i := by
  have feet := actual_native_feet c
  have even := evenPart_of_even (R c (C c)) (acted_even c 0)
  fin_cases i
  · change Constructor.zeroMean (nativeQuarter c 0)=nativeFoot c 0+S (nativeFoot c 1)
    rw [←actual_quarters c 0]
    have source := burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs (R c (C c)))
    change burnolAmbientMeanZeroFirstCorrection (R c (C c))+
      S (burnolAmbientMeanZeroSecondCorrection (R c (C c)))=
        Constructor.zeroMean (burnolQuarterRestriction (burnolAmbientEvenPart (R c (C c)))) at source
    rw [even] at source
    rw [feet.1,feet.2] at source
    exact source.symm
  · change Constructor.zeroMean (nativeQuarter c 1)=nativeFoot c 1+S (nativeFoot c 0)
    rw [←actual_quarters c 1]
    have source := burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs (R c (C c)))
    change S (burnolAmbientMeanZeroFirstCorrection (R c (C c)))+
      burnolAmbientMeanZeroSecondCorrection (R c (C c))=
        Constructor.zeroMean (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenPart (R c (C c))))) at source
    rw [even] at source
    rw [feet.1,feet.2] at source
    exact source.symm.trans (add_comm _ _)

private theorem native_even (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    reflectRestricted q (nativeFoot c i : Hq)=nativeFoot c i := by
  have paid := first_B_even (face i (R c (C c)))
  change sourceMeanZeroReflection (burnolAmbientMeanZeroFirstCorrection (face i (R c (C c))))=
    burnolAmbientMeanZeroFirstCorrection (face i (R c (C c))) at paid
  rw [(actual_face_feet c i).1] at paid
  exact congrArg (fun v : M => (v : Hq)) paid

private theorem native_quarter_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (nativeQuarter c i : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] actedRaw c i := by
  rw [←actual_quarters c i]
  exact (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) _).trans
    (ae_restrict_of_ae (acted_read c i))

private theorem edge_mean : Translator.ForcingMeanZero.edgeMean=ResponseProfile.etaMean := rfl
private theorem eta_normalization : Response.eta=TwoPieceFourierAction.eta q := rfl

/-- Both fixed forcing columns are generated by the original B response and its original constant. -/
theorem actual_forcing_columns (i : Fin 2) (x : ℝ) :
    phi i x= ![ResponseProfile.vRaw x-1,-ResponseProfile.uRaw x] i := by
  fin_cases i
  · change burnolRadiusTruncatedFourierRaw q (Response.u : Hq) x-
      (1+mu (burnolTruncatedFourier (Response.u : Hq)))=ResponseProfile.vRaw x-1
    unfold ResponseProfile.vRaw burnolMeanZeroFourierRaw
    ring
  · change -burnolRadiusTruncatedFourierRaw q (Response.v : Hq) x-Edge.raw q x-
      (-Translator.ForcingMeanZero.edgeMean-mu (burnolTruncatedFourier (Response.v : Hq)))=
        -ResponseProfile.uRaw x
    unfold ResponseProfile.uRaw ResponseProfile.etaRaw burnolMeanZeroFourierRaw
    rw [edge_mean]
    ring

private def forcingQuarter : Fin 2 → Hq :=
  ![(Response.v : Hq)-intervalConstant q,-(Response.u : Hq)]

private theorem forcing_quarter_read (i : Fin 2) :
    (forcingQuarter i : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] phi i := by
  fin_cases i
  · filter_upwards [Lp.coeFn_sub (Response.v : Hq) (intervalConstant q),
      ResponseProfile.v_read,intervalConstant_coeFn q] with x difference value one
    change ((Response.v : Hq)-intervalConstant q) x=phi 0 x
    rw [difference,Pi.sub_apply,value,one,actual_forcing_columns]
    rfl
  · filter_upwards [Lp.coeFn_neg (Response.u : Hq),ResponseProfile.u_read] with x negative value
    change (-(Response.u : Hq)) x=phi 1 x
    rw [negative,Pi.neg_apply,value,actual_forcing_columns]
    rfl

private theorem quarter_pairing (c : BurnolCompletedMellinCoordinate) (left : M) (i : Fin 2) :
    inner ℂ (left : Hq) (nativeQuarter c i)=inner ℂ left (nativeDrive c i) := by
  rw [←native_quarter_drive]
  change inner ℂ (left : Hq) (nativeQuarter c i)=
    inner ℂ (left : Hq) (burnolQuarterMeanZeroProjection (nativeQuarter c i))
  rw [burnolMeanZeroProjection_eq_sub_constant,inner_sub_right,inner_smul_right]
  have zero : inner ℂ (left : Hq) (intervalConstant q)=0 := by
    apply inner_eq_zero_symm.mp
    exact (Submodule.mem_orthogonal _ _).mp left.property _ (Submodule.mem_span_singleton_self _)
  rw [zero,mul_zero,sub_zero]

private theorem quarter_mean_pairing (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    inner ℂ (intervalConstant q) (nativeQuarter c i)=(1/2 : ℂ)*mu (nativeQuarter c i) := by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ)<q)]
  norm_num
  ring

private theorem native_response_pair (c : BurnolCompletedMellinCoordinate) :
    inner ℂ Response.v (nativeDrive c 0)-inner ℂ Response.u (nativeDrive c 1)=
      -inner ℂ Response.eta (nativeFoot c 1) ∧
    -inner ℂ Response.u (nativeDrive c 0)+inner ℂ Response.v (nativeDrive c 1)=
      -inner ℂ Response.eta (nativeFoot c 0) := by
  have forward := meanZero_fourier_pairing_of_reflection Response.u (nativeFoot c 0) (native_even c 0)
  have backward := meanZero_fourier_pairing_of_reflection Response.v (nativeFoot c 1) (native_even c 1)
  have otherForward := meanZero_fourier_pairing_of_reflection Response.u (nativeFoot c 1) (native_even c 1)
  have otherBackward := meanZero_fourier_pairing_of_reflection Response.v (nativeFoot c 0) (native_even c 0)
  change inner ℂ Response.v (nativeFoot c 0)=inner ℂ Response.u (S (nativeFoot c 0)) at forward
  change inner ℂ Response.v (nativeFoot c 1)=inner ℂ Response.u (S (nativeFoot c 1)) at otherForward
  have eta1 := congrArg (fun value : M => inner ℂ value (nativeFoot c 1)) Response.source_pair_equation
  have eta0 := congrArg (fun value : M => inner ℂ value (nativeFoot c 0)) Response.source_pair_equation
  simp only [inner_sub_left] at eta1 eta0
  change inner ℂ Response.u (nativeFoot c 1)-inner ℂ (S Response.v) (nativeFoot c 1)=
    inner ℂ Response.eta (nativeFoot c 1) at eta1
  change inner ℂ Response.u (nativeFoot c 0)-inner ℂ (S Response.v) (nativeFoot c 0)=
    inner ℂ Response.eta (nativeFoot c 0) at eta0
  constructor
  · change inner ℂ Response.v (nativeFoot c 0+S (nativeFoot c 1))-
      inner ℂ Response.u (nativeFoot c 1+S (nativeFoot c 0))=_
    simp only [inner_add_right]
    linear_combination -eta1+forward-backward
  · change -inner ℂ Response.u (nativeFoot c 0+S (nativeFoot c 1))+
      inner ℂ Response.v (nativeFoot c 1+S (nativeFoot c 0))=_
    simp only [inner_add_right]
    linear_combination -eta0+otherForward-otherBackward

def responseCharge (c : BurnolCompletedMellinCoordinate) : ℂ :=
  star (A c)*inner ℂ Response.eta (nativeFoot c 1)+
    star (beta c)*inner ℂ Response.eta (nativeFoot c 0)

def nativeMeanCharge (c : BurnolCompletedMellinCoordinate) : ℂ :=
  star (A c)*mu (nativeQuarter c 0)+star (beta c)*mu (nativeQuarter c 1)

private def wholeForcing (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (A c)*(star (phi 0 x)*actedRaw c 0 x+star (phi 1 x)*actedRaw c 1 x)+
    star (beta c)*(star (phi 1 x)*actedRaw c 0 x+star (phi 0 x)*actedRaw c 1 x)

private theorem whole_forcing_integrable (c : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (wholeForcing c) volume (-q) q := by
  have pair (i j : Fin 2) := native_pair_integrable (forcingQuarter i) (nativeQuarter c j)
    _ _ (forcing_quarter_read i) (native_quarter_read c j)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q≤q)).mpr
    (((pair 0 0).add (pair 1 1)).const_mul (star (A c)) |>.add
      (((pair 1 0).add (pair 0 1)).const_mul (star (beta c))))

/-- All four actual response/H actions collapse by the original B inverse; all means remain. -/
theorem actual_whole_forcing (c : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in (-q)..q,wholeForcing c x)= -responseCharge c-(1/2 : ℂ)*nativeMeanCharge c := by
  have pair (i j : Fin 2) := native_pair_read (forcingQuarter i) (nativeQuarter c j)
    _ _ (forcing_quarter_read i) (native_quarter_read c j)
  have integrable (i j : Fin 2) :
      IntervalIntegrable (fun x : ℝ => star (phi i x)*actedRaw c j x) volume (-q) q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q≤q)).mpr
      (native_pair_integrable _ _ _ _ (forcing_quarter_read i) (native_quarter_read c j))
  have assembled : (∫ x : ℝ in (-q)..q,wholeForcing c x)=
      star (A c)*(inner ℂ (forcingQuarter 0) (nativeQuarter c 0)+
        inner ℂ (forcingQuarter 1) (nativeQuarter c 1))+
      star (beta c)*(inner ℂ (forcingQuarter 1) (nativeQuarter c 0)+
        inner ℂ (forcingQuarter 0) (nativeQuarter c 1)) := by
    unfold wholeForcing
    rw [intervalIntegral.integral_add (((integrable 0 0).add (integrable 1 1)).const_mul _)
      (((integrable 1 0).add (integrable 0 1)).const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (integrable 0 0) (integrable 1 1),
      intervalIntegral.integral_add (integrable 1 0) (integrable 0 1),
      ←pair 0 0,←pair 1 1,←pair 1 0,←pair 0 1]
  rw [assembled]
  change star (A c)*(inner ℂ ((Response.v : Hq)-intervalConstant q) (nativeQuarter c 0)+
    inner ℂ (-(Response.u : Hq)) (nativeQuarter c 1))+
    star (beta c)*(inner ℂ (-(Response.u : Hq)) (nativeQuarter c 0)+
      inner ℂ ((Response.v : Hq)-intervalConstant q) (nativeQuarter c 1))=_
  rw [inner_sub_left,inner_sub_left,inner_neg_left,inner_neg_left,
    quarter_pairing,quarter_pairing,quarter_pairing,quarter_pairing,
    quarter_mean_pairing,quarter_mean_pairing]
  unfold responseCharge nativeMeanCharge
  linear_combination star (A c)*(native_response_pair c).1+star (beta c)*(native_response_pair c).2

def innerCurrent (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  ![-2*meanCharge c 0/c.value,
    2*meanCharge c 1/(1-c.value)+unitCoefficient c*(x : ℂ)^(c.value-1)] i

def innerForcing (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (A c)*(star (ResponseProfile.vRaw x-1)*innerCurrent c 0 x-
    star (ResponseProfile.uRaw x)*innerCurrent c 1 x)+
  star (beta c)*(-star (ResponseProfile.uRaw x)*innerCurrent c 0 x+
    star (ResponseProfile.vRaw x-1)*innerCurrent c 1 x)

def nativePFlux (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (p : ℂ)*(star (sourceProfile c 0 p)*innerCurrent c 0 p-
    star (sourceProfile c 1 p)*innerCurrent c 1 p)

private theorem whole_forcing_even (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x∈Icc 0 q) : wholeForcing c (-x)=wholeForcing c x := by
  have field (i : Fin 2) : actedRaw c i (-x)=actedRaw c i x := by
    fin_cases i
    · change prefixRaw c (inputRaw c 0) (-x)=prefixRaw c (inputRaw c 0) x
      simp only [prefixRaw,abs_neg]
    · change outwardRaw c (fourierL2 (C c)) (-x)=outwardRaw c (fourierL2 (C c)) x
      simp only [outwardRaw,abs_neg]
  have v := ResponseProfile.even_on true x (show x∈symmetricInterval q from ⟨by linarith [inside.1],inside.2⟩)
  have u := ResponseProfile.even_on false x (show x∈symmetricInterval q from ⟨by linarith [inside.1],inside.2⟩)
  change ResponseProfile.vRaw (-x)=ResponseProfile.vRaw x at v
  change ResponseProfile.uRaw (-x)=ResponseProfile.uRaw x at u
  simp only [wholeForcing,actual_forcing_columns,Matrix.cons_val_zero,Matrix.cons_val_one,
    v,u,field]

private theorem actual_band_forcing (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x∈Icc p q) : wholeForcing c x=mixedForcing c x := by
  unfold wholeForcing mixedForcing
  rw [actual_R_current c 0 x inside,actual_R_current c 1 x inside]

private theorem actual_inner_forcing (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0<x) (inside : x≤p) : wholeForcing c x=innerForcing c x := by
  simp only [wholeForcing,innerForcing,actual_forcing_columns,Matrix.cons_val_zero,
    Matrix.cons_val_one,actual_R_inner c 0 x positive inside,actual_R_inner c 1 x positive inside,
    innerCurrent,star_neg,neg_mul]
  ring

theorem actual_finite_forcing (c : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in p..q,mixedForcing c x)=
      -(1/2 : ℂ)*responseCharge c-(1/4 : ℂ)*nativeMeanCharge c-
        (∫ x : ℝ in 0..p,innerForcing c x) := by
  have whole := whole_forcing_integrable c
  have positive := whole.mono_set (show uIcc 0 q⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤q),uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have negative := whole.mono_set (show uIcc (-q) 0⊆uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : -q≤(0 : ℝ)),uIcc_of_le (by norm_num : -q≤q)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have reflected := intervalIntegral.integral_comp_neg (f := wholeForcing c) (a := (0 : ℝ)) (b := q)
  simp only [neg_zero] at reflected
  have same : (∫ x : ℝ in 0..q,wholeForcing c (-x))=(∫ x : ℝ in 0..q,wholeForcing c x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact whole_forcing_even c x (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤q)] using hx)
  have double := intervalIntegral.integral_add_adjacent_intervals negative positive
  rw [←reflected,same,actual_whole_forcing] at double
  have first := positive.mono_set (by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le)
  have next := positive.mono_set (by
    rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc junctionPoint_bounds.1.le le_rfl)
  have split := intervalIntegral.integral_add_adjacent_intervals first next
  have inner : (∫ x : ℝ in 0..p,wholeForcing c x)=(∫ x : ℝ in 0..p,innerForcing c x) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le junctionPoint_bounds.1.le]
    intro x hx
    exact actual_inner_forcing c x hx.1 hx.2.le
  have band : (∫ x : ℝ in p..q,wholeForcing c x)=(∫ x : ℝ in p..q,mixedForcing c x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact actual_band_forcing c x (by simpa only [uIcc_of_le junctionPoint_bounds.2.le] using hx)
  rw [inner,band] at split
  linear_combination split+(1/2 : ℂ)*double

private theorem actual_p_flux (c : BurnolCompletedMellinCoordinate) : mixedCurrent c p=nativePFlux c := by
  unfold mixedCurrent nativePFlux
  rw [actual_R_current c 0 p ⟨le_rfl,junctionPoint_bounds.2.le⟩,
    actual_R_current c 1 p ⟨le_rfl,junctionPoint_bounds.2.le⟩,
    actual_R_inner c 0 p junctionPoint_bounds.1 le_rfl,
    actual_R_inner c 1 p junctionPoint_bounds.1 le_rfl]
  rfl

/-- The same q source clears all native mean and response fees against its two actual endpoints. -/
theorem actual_q_source (c : BurnolCompletedMellinCoordinate) :
    -2*qFlux c-responseCharge c-(1/2 : ℂ)*nativeMeanCharge c=
      nativeAlpha c*(star (A c)*A (barC c)-star (beta c)*beta (barC c)) := by
  have read (i : Fin 2) : qCurrent c i=nativeEndpoint c i+mu (nativeQuarter c i)+
      burnolEvenRaw (burnolMeanZeroFourierRaw (nativeFoot c (flip i))) q := by
    have acted : qCurrent c i=actedRaw c i q :=
      (actual_q_current c i).symm.trans (actual_R_current c i q ⟨junctionPoint_bounds.2.le,le_rfl⟩)
    have even : actedRaw c i (-q)=actedRaw c i q := by
      fin_cases i
      · change prefixRaw c (inputRaw c 0) (-q)=prefixRaw c (inputRaw c 0) q
        simp only [prefixRaw,abs_neg]
      · change outwardRaw c (fourierL2 (C c)) (-q)=outwardRaw c (fourierL2 (C c)) q
        simp only [outwardRaw,abs_neg]
    have endpoint : nativeEndpoint c i=actedRaw c i q-mu (nativeQuarter c i)-
        burnolEvenRaw (burnolMeanZeroFourierRaw (nativeFoot c (flip i))) q := by
      dsimp only [nativeEndpoint,nativeRaw,burnolEvenRaw]
      rw [even]
      ring
    rw [acted]
    linear_combination -endpoint
  unfold qFlux responseCharge nativeMeanCharge
  rw [read 0,read 1,OriginalCommonInverseForcing.InverseEuler.eta_endpoint_read,
    OriginalCommonInverseForcing.InverseEuler.eta_endpoint_read,
    actual_native_endpoints c 0,actual_native_endpoints c 1]
  change -2*((q : ℂ)*(-star (A c)*(2*nativeAlpha c*A (barC c)+mu (nativeQuarter c 0)+
      burnolEvenRaw (burnolMeanZeroFourierRaw (nativeFoot c 1)) q)-
    star (beta c)*(-2*nativeAlpha c*beta (barC c)+mu (nativeQuarter c 1)+
      burnolEvenRaw (burnolMeanZeroFourierRaw (nativeFoot c 0)) q)))-
    (star (A c)*((q : ℂ)*(burnolMeanZeroFourierRaw (nativeFoot c 1) q+
      burnolMeanZeroFourierRaw (nativeFoot c 1) (-q)))+
    star (beta c)*((q : ℂ)*(burnolMeanZeroFourierRaw (nativeFoot c 0) q+
      burnolMeanZeroFourierRaw (nativeFoot c 0) (-q))))-
    (1/2 : ℂ)*(star (A c)*mu (nativeQuarter c 0)+star (beta c)*mu (nativeQuarter c 1))=_
  unfold burnolEvenRaw
  norm_num
  ring

/-- Every remaining term is an actual native response, full mean, unit or original R mass. -/
def finitePrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  2*(nativePFlux c-(∫ x : ℝ in 0..p,innerForcing c x)-
    (2*c.value-1)*(∫ x : ℝ in p..q,mixedMass c x))+
    nativeAlpha c*(star (A c)*A (barC c)-star (beta c)*beta (barC c))-
    4*(meanCharge c 0*(∫ x : ℝ in p..q,star (sourceProfile c 0 x))+
      meanCharge c 1*(∫ x : ℝ in p..q,star (sourceProfile c 1 x)))

/-- The new response action removes the original full finite forcing integral in the actual old Green price. -/
theorem actual_finite_price (c : BurnolCompletedMellinCoordinate) :
    BandFiniteSourcePrice.finiteSourcePrice c junctionShift=finitePrice c := by
  rw [actual_finite_price_mixed_green,actual_finite_forcing,actual_p_flux]
  unfold finitePrice
  linear_combination actual_q_source c

theorem actual_fixed_residual (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    -burnolPaFixedShiftResidual c zero=
      (pairedMellinTranslationCharacter c.value junctionShift-
        pairedMellinTranslationCharacter (star c.value) junctionShift)*kernelSelfSource c+
          (1/2 : ℂ)*star (finitePrice c) := by
  have source := BandFiniteSourcePrice.original_fixed_residual_finite_price c zero
  change -burnolPaFixedShiftResidual c zero=_ at source
  rw [←actual_finite_price]
  exact source

end OriginalWholeDebtRNativeForcingSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

