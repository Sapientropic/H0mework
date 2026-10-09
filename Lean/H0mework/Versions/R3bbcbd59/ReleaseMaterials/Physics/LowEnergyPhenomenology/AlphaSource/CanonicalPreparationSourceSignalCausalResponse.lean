import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSignalOperatorPrice

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentSignalOperator
open CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumCurrentSignalRealization
open PreparationVacuumGaugeSourceInjection PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart PreparationVacuumPropagationPencil PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumPhysicalHalfAxis
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime SourcePropagationMotherEulerKernel
open SourcePropagationNativeActionHessian SourcePropagationMotherResidualDirections
open Filter Set MeasureTheory
open scoped Topology BigOperators ContDiff Interval Matrix

def sourceQuadratureOperator : SignalAmplitude→L[ℝ] SignalAmplitude:=
  (-Complex.I) • ContinuousLinearMap.id ℝ SignalAmplitude

def sourceQuadratureCurrent (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) :
    SignalAmplitude→L[ℝ] (Fin 289→ℂ):=
  sourceCurrentOperator q p t+Complex.I • (sourceCurrentOperator q p t).comp sourceQuadratureOperator

theorem sourceQuadratureCurrent_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourceQuadratureCurrent q p t a=sourceSignalCurrent q p a t :=by
  rw [sourceQuadratureCurrent,add_apply,smul_apply,ContinuousLinearMap.comp_apply,sourceCurrentOperator_actual,
    sourceQuadratureOperator,smul_apply,ContinuousLinearMap.id_apply]
  funext i
  rw [sourceCurrentOperator_actual]
  rfl

theorem sourceQuadratureCurrent_continuous (q : PhysicalResponsePoint) (p : Fin 4→ℂ) :
    Continuous (sourceQuadratureCurrent q p) :=
  (sourceCurrentOperator_continuous q p).add
    (((sourceCurrentOperator_continuous q p).clm_comp continuous_const).const_smul Complex.I)

private theorem phase_price {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G] (c : ℂ) (unit : ‖c‖=1) (A : E→L[ℝ] G) : ‖c • A‖ ≤ ‖A‖ :=by
  apply (c • A).opNorm_le_bound (norm_nonneg A)
  intro x
  rw [smul_apply,norm_smul,unit,one_mul]
  exact A.le_opNorm x

private theorem quadrature_price : ‖sourceQuadratureOperator‖ ≤ 1 :=
  (phase_price (-Complex.I) (by simp) (ContinuousLinearMap.id ℝ SignalAmplitude)).trans ContinuousLinearMap.norm_id_le

theorem sourceQuadratureCurrent_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ)
    (positive : 0<eta) (future : 0 ≤ t) :
    ‖sourceQuadratureCurrent q p t‖ ≤
      2*(sourceCurrentLinearCoefficient q eta*t+sourceCurrentConstantCoefficient q eta)*
        Real.exp ((4*eta+sourceClockGrowth p)*t) :=by
  have rotation : ‖(sourceCurrentOperator q p t).comp sourceQuadratureOperator‖ ≤ ‖sourceCurrentOperator q p t‖:=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left quadrature_price (sourceCurrentOperator q p t).opNorm_nonneg).trans_eq (mul_one _))
  have imaginary:=phase_price Complex.I (by simp) ((sourceCurrentOperator q p t).comp sourceQuadratureOperator)
  have current:=sourceCurrentOperator_price q p eta t positive future
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans ((add_le_add current (imaginary.trans (rotation.trans current))).trans_eq (by ring))

def sourceReadGap (p : Fin 4→ℂ) (lambda : ℂ) : ℝ:=lambda.re-sourceClockGrowth p

def sourceCausalEta (p : Fin 4→ℂ) (lambda : ℂ) : ℝ:=sourceReadGap p lambda/16

def sourceCausalCoefficient (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) : ℝ:=
  2*((4/sourceReadGap p lambda)*sourceCurrentLinearCoefficient q (sourceCausalEta p lambda)+
    sourceCurrentConstantCoefficient q (sourceCausalEta p lambda))

def sourceWeightedQuadrature (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) (t : ℝ) :
    SignalAmplitude→L[ℝ] (Fin 289→ℂ):=
  laplaceWeight lambda t • sourceQuadratureCurrent q p t

private theorem scalar_growth_price (gap t : ℝ) (positive : 0<gap) :
    t ≤ (4/gap)*Real.exp ((gap/4)*t) :=by
  have source : (gap/4)*t ≤ Real.exp ((gap/4)*t):=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans (Real.add_one_le_exp _)
  calc
    t ≤ Real.exp ((gap/4)*t)/(gap/4):=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm t (gap/4)] using source)
    _=(4/gap)*Real.exp ((gap/4)*t):=by field_simp

private theorem scalar_operator_price {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G] (c : ℂ) (A : E→L[ℝ] G) : ‖c • A‖ ≤ ‖c‖*‖A‖ :=by
  apply (c • A).opNorm_le_bound (mul_nonneg (norm_nonneg c) A.opNorm_nonneg)
  intro x
  rw [smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg c)

private theorem decay_normalization (C sigma growth t : ℝ) :
    Real.exp (-sigma*t)*(2*(C*Real.exp ((sigma-growth)/4*t))*
      Real.exp ((4*((sigma-growth)/16)+growth)*t))=
        2*C*Real.exp (-((sigma-growth)/2)*t) :=by
  calc
    _=2*C*(Real.exp (-sigma*t)*Real.exp ((sigma-growth)/4*t)*
      Real.exp ((4*((sigma-growth)/16)+growth)*t)):=by ring
    _=_:=by
      rw [←Real.exp_add,←Real.exp_add]
      congr 2
      ring

theorem sourceWeightedQuadrature_price (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) (t : ℝ) (future : 0 ≤ t) :
    ‖sourceWeightedQuadrature q p lambda t‖ ≤ sourceCausalCoefficient q p lambda*
      Real.exp (-(sourceReadGap p lambda/2)*t) :=by
  have gap : 0<sourceReadGap p lambda:=sub_pos.mpr off
  have eta : 0<sourceCausalEta p lambda:=by unfold sourceCausalEta;positivity
  have coefficients:=sourceCurrentCoefficient_nonnegative q (sourceCausalEta p lambda) eta
  have source:=sourceQuadratureCurrent_price q p (sourceCausalEta p lambda) t eta future
  have rotated : ‖sourceWeightedQuadrature q p lambda t‖ ≤ ‖laplaceWeight lambda t‖*‖sourceQuadratureCurrent q p t‖ :=by
    unfold sourceWeightedQuadrature
    exact scalar_operator_price _ _
  have multiply:=rotated.trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))
  rw [laplace_norm] at multiply
  have grow:=scalar_growth_price (sourceReadGap p lambda) t gap
  have exponential : 1 ≤ Real.exp ((sourceReadGap p lambda/4)*t):=
    Real.one_le_exp (by positivity)
  have polynomial : sourceCurrentLinearCoefficient q (sourceCausalEta p lambda)*t+
      sourceCurrentConstantCoefficient q (sourceCausalEta p lambda) ≤
    ((4/sourceReadGap p lambda)*sourceCurrentLinearCoefficient q (sourceCausalEta p lambda)+
      sourceCurrentConstantCoefficient q (sourceCausalEta p lambda))*Real.exp ((sourceReadGap p lambda/4)*t) :=by
    have first:=mul_le_mul_of_nonneg_left grow coefficients.1
    have second:=le_mul_of_one_le_right coefficients.2 exponential
    refine (add_le_add first second).trans_eq ?_
    ring
  have polynomialScaled:=mul_le_mul_of_nonneg_left polynomial (show (0 : ℝ) ≤ 2 by norm_num)
  have fullScaled:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right polynomialScaled (Real.exp_pos ((4*sourceCausalEta p lambda+sourceClockGrowth p)*t)).le)
      (Real.exp_pos (-lambda.re*t)).le
  refine multiply.trans (fullScaled.trans_eq ?_)
  exact decay_normalization _ lambda.re (sourceClockGrowth p) t

theorem sourceWeightedQuadrature_continuous (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) :
    Continuous (sourceWeightedQuadrature q p lambda) :=by
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  exact weight.smul (sourceQuadratureCurrent_continuous q p)

theorem sourceWeightedQuadrature_integrable (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) : IntegrableOn (sourceWeightedQuadrature q p lambda) (Ioi (0 : ℝ)) :=by
  have gap : 0<sourceReadGap p lambda:=sub_pos.mpr off
  have majorant : IntegrableOn (fun t=>sourceCausalCoefficient q p lambda*Real.exp (-(sourceReadGap p lambda/2)*t))
      (Ioi (0 : ℝ)):=
    (integrableOn_exp_mul_Ioi (a:=-(sourceReadGap p lambda/2)) (by linarith) 0).const_mul _
  apply majorant.mono' (sourceWeightedQuadrature_continuous q p lambda).aestronglyMeasurable.restrict
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  exact sourceWeightedQuadrature_price q p lambda off t ht.le

def sourceCausalWindow (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) :
    SignalAmplitude→L[ℝ] (Fin 289→ℂ):=
  ∫t in (0 : ℝ)..T,sourceWeightedQuadrature q p lambda t

def sourceCausalHalfOperator (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) :
    SignalAmplitude→L[ℝ] (Fin 289→ℂ):=
  ∫t in Ioi (0 : ℝ),sourceWeightedQuadrature q p lambda t

theorem sourceCausalWindow_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) :
    sourceCausalWindow q p lambda T a=
      fun i=>∫t in (0 : ℝ)..T,laplaceWeight lambda t*sourceSignalCurrent q p a t i :=by
  rw [sourceCausalWindow,ContinuousLinearMap.intervalIntegral_apply
    ((sourceWeightedQuadrature_continuous q p lambda).intervalIntegrable 0 T)]
  funext i
  have integrable : IntervalIntegrable (fun t=>sourceWeightedQuadrature q p lambda t a) volume 0 T:=
    ((sourceWeightedQuadrature_continuous q p lambda).clm_apply (continuous_const : Continuous (fun _ : ℝ=>a))).intervalIntegrable 0 T
  have coordinate:=(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ] ℂ).intervalIntegral_comp_comm integrable
  simp only [ContinuousLinearMap.proj_apply] at coordinate
  rw [←coordinate]
  · apply intervalIntegral.integral_congr
    intro t _
    change laplaceWeight lambda t*(sourceQuadratureCurrent q p t a i)=_
    exact congrArg (fun z : ℂ=>laplaceWeight lambda t*z) (congrFun (sourceQuadratureCurrent_actual q p t a) i)

theorem sourceCausalWindow_noether (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ)
    (a : SignalAmplitude) :
    sourceCausalWindow q p lambda T a=
      noetherForcing q (nativeTimeSignal (sourceRealSignal p a)) lambda T+
        Complex.I • noetherForcing q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) lambda T :=by
  rw [sourceCausalWindow_actual]
  funext i
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  have first : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      (noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p a)) t i).value) volume 0 T:=
    (weight.mul ((noetherHistorySourceJet_continuous q _ (sourceTimeSignal_continuous p a) i).1)).intervalIntegrable 0 T
  have second : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      (noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t i).value) volume 0 T:=
    (weight.mul ((noetherHistorySourceJet_continuous q _ (sourceTimeSignal_continuous p (sourceQuadrature a)) i).1)).intervalIntegrable 0 T
  simp only [sourceSignalCurrent,mul_add,mul_left_comm (laplaceWeight lambda _),noetherForcing,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [intervalIntegral.integral_add first (second.const_mul Complex.I),intervalIntegral.integral_const_mul]

theorem sourceCausalWindow_operatorNorm (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) :
    Tendsto (fun T=>sourceCausalWindow q p lambda T) atTop (𝓝 (sourceCausalHalfOperator q p lambda)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (sourceWeightedQuadrature_integrable q p lambda off) tendsto_id

def sourceCausalTailPrice (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : ℝ:=
  (2/sourceReadGap p lambda)*sourceCausalCoefficient q p lambda*Real.exp (-(sourceReadGap p lambda/2)*T)

theorem sourceCausalHalfOperator_tail (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) (T : ℝ) (future : 0 ≤ T) :
    ‖sourceCausalHalfOperator q p lambda-sourceCausalWindow q p lambda T‖ ≤ sourceCausalTailPrice q p lambda T :=by
  have gap : 0<sourceReadGap p lambda:=sub_pos.mpr off
  have whole:=sourceWeightedQuadrature_integrable q p lambda off
  have tail:=whole.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi whole tail
  have difference : sourceCausalHalfOperator q p lambda-sourceCausalWindow q p lambda T=
      ∫t in Ioi T,sourceWeightedQuadrature q p lambda t :=by
    apply sub_eq_iff_eq_add.mpr
    simpa only [sourceCausalHalfOperator,sourceCausalWindow,add_comm] using equation.symm
  have majorant : IntegrableOn (fun t=>sourceCausalCoefficient q p lambda*Real.exp (-(sourceReadGap p lambda/2)*t)) (Ioi T):=
    (integrableOn_exp_mul_Ioi (a:=-(sourceReadGap p lambda/2)) (by linarith) T).const_mul _
  have bounded : ∀ᵐt ∂volume.restrict (Ioi T),‖sourceWeightedQuadrature q p lambda t‖ ≤
      sourceCausalCoefficient q p lambda*Real.exp (-(sourceReadGap p lambda/2)*t) :=by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact sourceWeightedQuadrature_price q p lambda off t (future.trans ht.le)
  rw [difference]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant bounded).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith)]
  unfold sourceCausalTailPrice
  field_simp

private def spectralMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : (Fin n→ℂ)→L[ℝ] (Fin m→ℂ):=
  ContinuousLinearMap.pi (fun i=>∑j : Fin n,A i j • (ContinuousLinearMap.proj j : (Fin n→ℂ)→L[ℝ] ℂ))

private theorem spectralMatrix_actual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n→ℂ) :
    spectralMatrix A v=A*ᵥv :=by
  funext i
  simp only [spectralMatrix,ContinuousLinearMap.pi_apply,sum_apply,smul_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul,Matrix.mulVec,dotProduct]

def sourceCausalFieldOperator (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) : SignalAmplitude→L[ℝ] (Fin 289→ℂ):=
  (spectralMatrix (sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩)).comp
    (sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda.val)

def sourceCausalCurvatureOperator (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) : SignalAmplitude→L[ℝ] (Fin 36→ℂ):=
  (spectralMatrix (originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val))).comp
    (sourceCausalFieldOperator q clock lambda)

theorem sourceCausalCurvatureOperator_actual (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) (a : SignalAmplitude) :
    sourceCausalCurvatureOperator q clock lambda a=
      originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥsourceCausalFieldOperator q clock lambda a :=by
  rw [sourceCausalCurvatureOperator,ContinuousLinearMap.comp_apply,spectralMatrix_actual]

theorem sourceCausalFieldOperator_native (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) (a : SignalAmplitude) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥsourceCausalFieldOperator q clock lambda a=
      sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda.val a-
        originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
            (sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda.val a) :=by
  rw [sourceCausalFieldOperator,ContinuousLinearMap.comp_apply,spectralMatrix_actual]
  exact nativeAction_sourceField ⟨_,lambda.property⟩ _

theorem sourceCausalCurvatureOperator_native (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) (a : SignalAmplitude) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥsourceCausalFieldOperator q clock lambda a)=
      originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda.val a-
      originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
            (sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda.val a)) :=by
  rw [sourceCausalFieldOperator_native,Matrix.mulVec_sub]

theorem sourceCausalWindow_cosources (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥsourceCausalWindow q p lambda T a) row=
      ((∫t in (0 : ℝ)..T,laplaceWeight lambda t*
          noetherTimeSource q (nativeTimeSignal (sourceRealSignal p a)) spatial t row)-
        (noetherBoundary q (nativeTimeSignal (sourceRealSignal p a)) spatial lambda T row-
          noetherBoundary q (nativeTimeSignal (sourceRealSignal p a)) spatial lambda 0 row))+
      Complex.I*((∫t in (0 : ℝ)..T,laplaceWeight lambda t*
          noetherTimeSource q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) spatial t row)-
        (noetherBoundary q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) spatial lambda T row-
          noetherBoundary q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) spatial lambda 0 row)) :=by
  rw [sourceCausalWindow_noether,Matrix.mulVec_add,Matrix.mulVec_smul]
  change _+Complex.I*_= _
  rw [noetherForcing_readback q _ (sourceTimeSignal_continuous p a) (fun t=>sourceTimeSignal_generated p a t),
    noetherForcing_readback q _ (sourceTimeSignal_continuous p (sourceQuadrature a))
      (fun t=>sourceTimeSignal_generated p (sourceQuadrature a) t)]

end LowEnergy.PreparationVacuumCurrentSignalOperator
