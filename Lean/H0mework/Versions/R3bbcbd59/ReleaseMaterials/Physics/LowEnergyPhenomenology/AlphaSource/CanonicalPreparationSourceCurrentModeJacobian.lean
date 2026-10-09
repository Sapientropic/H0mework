import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNoetherControlledTail
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentVisibleFeedback
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumMatterEulerFeedback PreparationVacuumNoetherResponsePrice
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumOrderedRealSignal PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumOriginalDensity PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatialSource
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Interval

private def fieldPartial {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : H×ℝ→E) (u : H×ℝ) : H→L[ℝ] E:=
  (fderiv ℝ S u).comp (ContinuousLinearMap.inl ℝ H ℝ)

private theorem partial_generated {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : H×ℝ→E) (u : H×ℝ)
    (smooth : ContDiffAt ℝ 2 S u) :
    HasFDerivAt (fun h=>S (h,u.2)) (fieldPartial S u) u.1 :=by
  have actual:=smooth.differentiableAt (by norm_num) |>.hasFDerivAt
  have path:=hasFDerivAt_prodMk_left (𝕜:=ℝ) u.1 u.2
  exact actual.comp u.1 path

private theorem partial_continuousAt {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : H×ℝ→E) (u : H×ℝ)
    (smooth : ContDiffAt ℝ 2 S u) : ContinuousAt (fieldPartial S) u :=by
  exact ((smooth.fderiv_right (m:=1) (by norm_num)).clm_comp contDiffAt_const).continuousAt

/-- The actual joint source generates a compact-time tube and its derivative bound. -/
private theorem finiteWindow_frechet {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : H×ℝ→E) (T : ℝ) (sourceSmooth : ∀t∈uIcc (0:ℝ) T,ContDiffAt ℝ 2 S (0,t)) :
    IntervalIntegrable (fun t=>fieldPartial S (0,t)) volume 0 T ∧
      HasFDerivAt (fun h=>∫t in (0:ℝ)..T,S (h,t))
        (∫t in (0:ℝ)..T,fieldPartial S (0,t)) 0 :=by
  let K:=uIcc (0:ℝ) T
  let U : Set (H×ℝ):={u | ContDiffAt ℝ 2 S u}
  have openU : IsOpen U:=isOpen_iff_mem_nhds.mpr
    (fun u hu=>(show ContDiffAt ℝ 2 S u from hu).eventually (by norm_num))
  have base : ({0}:Set H) ×ˢ K⊆U:=by
    rintro ⟨h,t⟩ ⟨hh,ht⟩
    have zero : h=0:=hh
    subst h
    exact sourceSmooth t ht
  obtain ⟨a,b,ha,_hb,hzero,hcover,hproduct⟩:=
    generalized_tube_lemma (isCompact_singleton (x:=(0:H))) isCompact_uIcc openU base
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (ha.mem_nhds (hzero (by rfl)))
  let R:=e/2
  have hR : 0<R:=by dsimp [R];positivity
  have tube (h : H) (t : ℝ) (hh : h∈Metric.closedBall (0:H) R) (ht : t∈K) :
      ContDiffAt ℝ 2 S (h,t):=by
    apply hproduct
    refine ⟨hball ?_,hcover ht⟩
    rw [Metric.mem_ball,dist_zero_right]
    rw [Metric.mem_closedBall,dist_zero_right] at hh
    dsimp [R] at hh
    linarith
  have dc : ContinuousOn (fieldPartial S) (Metric.closedBall (0:H) R ×ˢ K):=
    fun u hu=>(partial_continuousAt S u (tube u.1 u.2 hu.1 hu.2)).continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:H) R).prod isCompact_uIcc
    |>.exists_bound_of_continuousOn dc
  have inBall : ∀h∈Metric.ball (0:H) R,h∈Metric.closedBall (0:H) R:=
    fun _ hh=>Metric.ball_subset_closedBall hh
  have fcont (h : H) (hh : h∈Metric.closedBall (0:H) R) : ContinuousOn (fun t=>S (h,t)) K:=by
    intro t ht
    exact (tube h t hh ht).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
      |>.continuousWithinAt
  have dcont : ContinuousOn (fun t=>fieldPartial S (0,t)) K:=by
    intro t ht
    exact (partial_continuousAt S (0,t) (tube 0 t (Metric.mem_closedBall_self hR.le) ht)).comp
      (continuous_const.prodMk continuous_id).continuousAt |>.continuousWithinAt
  have hs : Metric.ball (0:H) R∈𝓝 (0:H):=Metric.ball_mem_nhds _ hR
  have lip : ∀ᵐt ∂volume.restrict (Ι (0:ℝ) T),
      LipschitzOnWith (Real.nnabs C) (fun h=>S (h,t)) (Metric.ball (0:H) R) :=by
    apply (ae_restrict_mem measurableSet_uIoc).mono
    intro t ht
    have hk : t∈K:=uIoc_subset_uIcc ht
    apply (convex_ball (0:H) R).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun h hh=>(partial_generated S (h,t) (tube h t (inBall h hh) hk)).hasFDerivWithinAt)
    intro h hh
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_nnabs]
    exact (hC (h,t) ⟨inBall h hh,hk⟩).trans (le_abs_self C)
  exact hasFDerivAt_integral_of_dominated_loc_of_lip_interval
    (F:=fun h t=>S (h,t)) (F':=fun t=>fieldPartial S (0,t)) hs
    (by filter_upwards [hs] with h hh
        exact ((fcont h (inBall h hh)).intervalIntegrable (μ:=volume)).def'.aestronglyMeasurable)
    (fcont 0 (Metric.mem_closedBall_self hR.le)).intervalIntegrable
    (dcont.intervalIntegrable (μ:=volume)).def'.aestronglyMeasurable
    lip intervalIntegrable_const
    (by
      apply (ae_restrict_mem measurableSet_uIoc).mono
      intro t ht
      exact partial_generated S (0,t)
        (tube 0 t (Metric.mem_closedBall_self hR.le) (uIoc_subset_uIcc ht)))

def sourceModeJoint (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (u : Field289×ℝ) : Fin 289→ℂ:=actionRealEulerSource q u.2 wave u.1

theorem sourceModeJoint_C2 (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    ContDiffAt ℝ 2 (sourceModeJoint q wave) (0,t) :=
  contDiffAt_pi.mpr (fun i=>(actionRealCoefficient_jointC2 q (fieldUnit i) hz hw t (-wave)).neg)

def sourceModeJacobian (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (t : ℝ) :
    Field289→L[ℝ] (Fin 289→ℂ):=fieldPartial (sourceModeJoint q wave) (0,t)

theorem sourceModeJacobian_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    sourceModeJacobian q wave t force=realEulerSlope q force t (-wave) :=by
  have actual:=(partial_generated (sourceModeJoint q wave) (0,t)
    (sourceModeJoint_C2 q wave hz hw t)).comp_hasDerivAt_of_eq 0
      (fieldRay_derivative force 0) (by simp)
  exact actual.unique (actionRealEulerSource_generated q t wave force hz hw)

theorem sourceModeJacobian_arbitraryForce (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (t : ℝ) (force : Field289) :
    sourceModeJacobian q wave t force=∑j : Fin 289,force j • sourceModeJacobian q wave t (fieldUnit j) :=by
  have coordinates : force=∑j : Fin 289,force j • fieldUnit j:=by
    funext i
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply]
  have generated:=congrArg (sourceModeJacobian q wave t) coordinates
  simpa only [map_sum,map_smul] using generated

def sourceWindowJoint (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (u : Field289×ℝ) : Fin 289→ℂ:=laplaceWeight lambda u.2 • sourceModeJoint q wave u

theorem sourceWindowJoint_C2 (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    ContDiffAt ℝ 2 (sourceWindowJoint q wave lambda) (0,t) :=by
  have weight : ContDiffAt ℝ 2 (fun u : Field289×ℝ=>laplaceWeight lambda u.2) (0,t):=by
    unfold laplaceWeight
    exact (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (0,t) contDiffAt_snd)).cexp
  exact weight.smul (sourceModeJoint_C2 q wave hz hw t)

def sourceModeWindow (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (T : ℝ) (h : Field289) : Fin 289→ℂ:=∫t in (0:ℝ)..T,sourceWindowJoint q wave lambda (h,t)

def sourceWindowJacobian (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (T : ℝ) : Field289→L[ℝ] (Fin 289→ℂ):=
  ∫t in (0:ℝ)..T,fieldPartial (sourceWindowJoint q wave lambda) (0,t)

theorem sourceModeWindow_hasFDerivAt (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasFDerivAt (sourceModeWindow q wave lambda T) (sourceWindowJacobian q wave lambda T) 0 :=
  (finiteWindow_frechet (sourceWindowJoint q wave lambda) T
    (fun t _=>sourceWindowJoint_C2 q wave lambda hz hw t)).2

theorem sourceWindowPartial_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    fieldPartial (sourceWindowJoint q wave lambda) (0,t) force=
      laplaceWeight lambda t • realEulerSlope q force t (-wave) :=by
  have actual:=(partial_generated (sourceWindowJoint q wave lambda) (0,t)
    (sourceWindowJoint_C2 q wave lambda hz hw t)).comp_hasDerivAt_of_eq 0
      (fieldRay_derivative force 0) (by simp)
  have original:=(actionRealEulerSource_generated q t wave force hz hw).const_smul
    (laplaceWeight lambda t)
  exact actual.unique original

theorem sourceWindowJacobian_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceWindowJacobian q wave lambda T force=modeForcing q force true wave lambda T :=by
  have integrable:=(finiteWindow_frechet (sourceWindowJoint q wave lambda) T
    (fun t _=>sourceWindowJoint_C2 q wave lambda hz hw t)).1
  rw [sourceWindowJacobian,ContinuousLinearMap.intervalIntegral_apply integrable]
  funext i
  have evaluated : IntervalIntegrable
      (fun t=>fieldPartial (sourceWindowJoint q wave lambda) (0,t) force) volume 0 T :=
    ⟨(ContinuousLinearMap.apply ℝ (Fin 289→ℂ) force).integrable_comp integrable.1,
      (ContinuousLinearMap.apply ℝ (Fin 289→ℂ) force).integrable_comp integrable.2⟩
  have projection := (ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ] ℂ).intervalIntegral_comp_comm evaluated
  change (ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ] ℂ)
    (∫t in (0:ℝ)..T,fieldPartial (sourceWindowJoint q wave lambda) (0,t) force)=_
  rw [←projection]
  apply intervalIntegral.integral_congr
  intro t _
  change (fieldPartial (sourceWindowJoint q wave lambda) (0,t) force) i=
    laplaceWeight lambda t*(modeJet q force true wave t i).value
  rw [sourceWindowPartial_generated q wave lambda force hz hw t]
  simp only [Pi.smul_apply,smul_eq_mul,modeJet,realEulerTimeJet_value]
  rfl

theorem sourceWindowJacobian_arbitraryForce (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (force : Field289) :
    sourceWindowJacobian q wave lambda T force=
      ∑j : Fin 289,force j • sourceWindowJacobian q wave lambda T (fieldUnit j) :=by
  have coordinates : force=∑j : Fin 289,force j • fieldUnit j:=by
    funext i
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply]
  simpa only [map_sum,map_smul] using congrArg (sourceWindowJacobian q wave lambda T) coordinates

end LowEnergy.PreparationVacuumCurrentVisibleFeedback
