import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCurrentModeJacobian

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentHalfOperator
open PreparationVacuumCurrentVisibleFeedback PreparationVacuumMatterEulerFeedback
open PreparationVacuumNoetherResponsePrice PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumOrderedRealSignal PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection CanonicalGradedSpatialSource
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Interval

private theorem real_basis (force : Field289) : force=∑j : Fin 289,force j • fieldUnit j :=by
  funext i
  simp [fieldUnit,Finset.sum_apply,Pi.single_apply]

private theorem real_operator_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (operator : Field289→L[ℝ] E) : ‖operator‖≤∑j : Fin 289,‖operator (fieldUnit j)‖ :=by
  apply operator.opNorm_le_bound (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  intro force
  conv_lhs => rw [real_basis force]
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [map_smul,norm_smul,mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm force j) (norm_nonneg _)

private theorem coordinate_norm_price (value : Fin 289→ℂ) : ‖value‖≤∑i : Fin 289,‖value i‖ :=by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
  intro i
  exact Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ i)

def sourceWeightedCurrent (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ) (t : ℝ) :
    Field289→L[ℝ] (Fin 289→ℂ):=laplaceWeight lambda t • sourceModeJacobian q wave t

theorem sourceWeightedCurrent_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    sourceWeightedCurrent q wave lambda t force=
      fun i=>laplaceWeight lambda t*(modeJet q force true wave t i).value :=by
  rw [sourceWeightedCurrent,smul_apply,sourceModeJacobian_generated q wave force hz hw t]
  funext i
  simp only [Pi.smul_apply,smul_eq_mul,modeJet,realEulerTimeJet_value,ite_true]

def sourceCurrentPrice (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ) : ℝ:=
  ∑j : Fin 289,∑i : Fin 289,modeDecayCoefficient q (fieldUnit j) true wave lambda i

theorem sourceCurrentPrice_nonnegative (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) :
    0≤ sourceCurrentPrice q wave lambda :=
  Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>modeDecayCoefficient_nonnegative _ _ _ _ _ positive _))

theorem sourceWeightedCurrent_price (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) (t : ℝ) (future : 0≤t) :
    ‖sourceWeightedCurrent q wave lambda t‖≤ sourceCurrentPrice q wave lambda*Real.exp (-(lambda.re/2)*t) :=by
  refine (real_operator_price _).trans ?_
  unfold sourceCurrentPrice
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  refine (coordinate_norm_price _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [sourceWeightedCurrent_generated q wave lambda (fieldUnit j) hz hw t]
  exact weightedModeSource_price q (fieldUnit j) true wave lambda positive t future i

private theorem sourceCurrent_basis (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (t : ℝ) : sourceWeightedCurrent q wave lambda t=
      ∑j : Fin 289,(ContinuousLinearMap.proj j : Field289→L[ℝ] ℝ).smulRight
        (sourceWeightedCurrent q wave lambda t (fieldUnit j)) :=by
  ext force i
  have same:=congrArg (sourceWeightedCurrent q wave lambda t) (real_basis force)
  simpa only [map_sum,map_smul,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,Pi.smul_apply] using congrFun same i

theorem sourceWeightedCurrent_continuous (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    Continuous (sourceWeightedCurrent q wave lambda) :=by
  have basis (j : Fin 289) : Continuous (fun t=>sourceWeightedCurrent q wave lambda t (fieldUnit j)) :=by
    apply continuous_pi
    intro i
    have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
    have generated : (fun t=>sourceWeightedCurrent q wave lambda t (fieldUnit j) i)=
        fun t=>laplaceWeight lambda t*(modeJet q (fieldUnit j) true wave t i).value :=by
      funext t
      exact congrFun (sourceWeightedCurrent_generated q wave lambda (fieldUnit j) hz hw t) i
    rw [generated]
    exact weight.mul (realEulerTimeJets_continuous q (fieldUnit j) true (-wave) i).1
  have whole : Continuous (fun t=>∑j : Fin 289,
      (ContinuousLinearMap.proj j : Field289→L[ℝ] ℝ).smulRight
        (sourceWeightedCurrent q wave lambda t (fieldUnit j))) :=by
    apply continuous_finsetSum
    intro j _
    exact (ContinuousLinearMap.smulRightL ℝ Field289 (Fin 289→ℂ)
      (ContinuousLinearMap.proj j)).continuous.comp (basis j)
  exact whole.congr (fun t=>(sourceCurrent_basis q wave lambda t).symm)

theorem sourceWeightedCurrent_integrable (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) :
    IntegrableOn (sourceWeightedCurrent q wave lambda) (Ioi (0:ℝ)) :=by
  have majorant : IntegrableOn (fun t=>sourceCurrentPrice q wave lambda*Real.exp (-(lambda.re/2)*t)) (Ioi (0:ℝ)) :=
    (integrableOn_exp_mul_Ioi (a:=-(lambda.re/2)) (by linarith) 0).const_mul _
  apply majorant.mono' (sourceWeightedCurrent_continuous q wave lambda hz hw).aestronglyMeasurable.restrict
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  exact sourceWeightedCurrent_price q wave lambda hz hw positive t ht.le

/-- The full physical-real derivative is integrated as one Bochner operator. -/
def sourceHalfCurrent (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ) :
    Field289→L[ℝ] (Fin 289→ℂ):=∫t in Ioi (0:ℝ),sourceWeightedCurrent q wave lambda t

theorem sourceHalfCurrent_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) :
    sourceHalfCurrent q wave lambda force=modeHalfForcing q force true wave lambda :=by
  have integrable:=sourceWeightedCurrent_integrable q wave lambda hz hw positive
  rw [sourceHalfCurrent,ContinuousLinearMap.integral_apply integrable]
  funext i
  have evaluated : Integrable (fun t=>sourceWeightedCurrent q wave lambda t force) (volume.restrict (Ioi (0:ℝ))) :=
    (ContinuousLinearMap.apply ℝ (Fin 289→ℂ) force).integrable_comp integrable
  have projection:=(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ] ℂ).integral_comp_comm evaluated
  change (ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ] ℂ)
    (∫t in Ioi (0:ℝ),sourceWeightedCurrent q wave lambda t force)=_
  rw [←projection]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>congrFun (sourceWeightedCurrent_generated q wave lambda force hz hw t) i)

theorem sourceWindowJacobian_integral (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceWindowJacobian q wave lambda T=∫t in (0:ℝ)..T,sourceWeightedCurrent q wave lambda t :=by
  rw [sourceWindowJacobian]
  apply intervalIntegral.integral_congr
  intro t _
  ext force i
  rw [sourceWindowPartial_generated q wave lambda force hz hw t,
    sourceWeightedCurrent_generated q wave lambda force hz hw t]
  simp only [Pi.smul_apply,smul_eq_mul,modeJet,realEulerTimeJet_value,ite_true]

def sourceCurrentTailPrice (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ) (T : ℝ) : ℝ:=
  (2/lambda.re)*sourceCurrentPrice q wave lambda*Real.exp (-(lambda.re/2)*T)

theorem sourceHalfCurrent_tail (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) (T : ℝ) (future : 0≤T) :
    ‖sourceHalfCurrent q wave lambda-sourceWindowJacobian q wave lambda T‖≤ sourceCurrentTailPrice q wave lambda T :=by
  have integral:=sourceWeightedCurrent_integrable q wave lambda hz hw positive
  have tail:=integral.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi integral tail
  have difference : sourceHalfCurrent q wave lambda-sourceWindowJacobian q wave lambda T=
      ∫t in Ioi T,sourceWeightedCurrent q wave lambda t :=by
    rw [sourceWindowJacobian_integral q wave lambda hz hw T,sourceHalfCurrent]
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using equation.symm
  have majorant : IntegrableOn (fun t=>sourceCurrentPrice q wave lambda*Real.exp (-(lambda.re/2)*t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (a:=-(lambda.re/2)) (by linarith) T).const_mul _
  have bound : ∀ᵐt ∂volume.restrict (Ioi T),‖sourceWeightedCurrent q wave lambda t‖≤
      sourceCurrentPrice q wave lambda*Real.exp (-(lambda.re/2)*t) :=by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact sourceWeightedCurrent_price q wave lambda hz hw positive t (future.trans ht.le)
  rw [difference]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant bound).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (show -(lambda.re/2)<0 by linarith) T]
  unfold sourceCurrentTailPrice
  field_simp

theorem sourceHalfCurrent_price (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) :
    ‖sourceHalfCurrent q wave lambda‖≤(2/lambda.re)*sourceCurrentPrice q wave lambda :=by
  have bound:=sourceHalfCurrent_tail q wave lambda hz hw positive 0 (by rfl)
  rw [sourceWindowJacobian_integral q wave lambda hz hw 0,intervalIntegral.integral_same,
    sub_zero,sourceCurrentTailPrice,mul_zero,Real.exp_zero,mul_one] at bound
  exact bound

theorem sourceCurrentTailPrice_zero (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) : Tendsto (sourceCurrentTailPrice q wave lambda) atTop (𝓝 0) :=by
  have decay : Tendsto (fun T : ℝ=>Real.exp (-(lambda.re/2)*T)) atTop (𝓝 0) :=by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (lambda.re/2) (by positivity)
  change Tendsto (fun T : ℝ=>(2/lambda.re)*sourceCurrentPrice q wave lambda*Real.exp (-(lambda.re/2)*T)) atTop (𝓝 0)
  simpa only [mul_zero] using decay.const_mul ((2/lambda.re)*sourceCurrentPrice q wave lambda)

theorem sourceWindowJacobian_operatorNorm (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) :
    Tendsto (fun T=>sourceWindowJacobian q wave lambda T) atTop (𝓝 (sourceHalfCurrent q wave lambda)) :=by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (g:=sourceCurrentTailPrice q wave lambda)
    (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) ?_
    (sourceCurrentTailPrice_zero q wave lambda positive)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T future
  rw [norm_sub_rev]
  exact sourceHalfCurrent_tail q wave lambda hz hw positive T future

end LowEnergy.PreparationVacuumCurrentHalfOperator
