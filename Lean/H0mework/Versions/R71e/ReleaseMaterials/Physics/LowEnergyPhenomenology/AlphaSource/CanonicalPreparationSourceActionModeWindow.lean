import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActionEulerSources
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNoetherSourceInitialReturn
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMatterEulerFeedback
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumIndependentMomentumReturn
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumOrderedRealSignal PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace Interval
local instance : NormedAlgebra ℝ SourceOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
attribute [local irreducible] noetherPreparedCurrent sourceMatterEulerPrepared

def actionEulerJointKernel (q : PhysicalResponsePoint) (reader : Field289) (u : Field289×ℝ) : SourceOperator:=
  physicalTime (q.p+q.k) q.F (-u.2) u.1*jointResolvent (q.p+q.k) q.F q.z u.1*
    noetherReader reader q.p q.F u.1*jointResolvent q.p q.F q.w u.1*physicalTime q.p q.F u.2 u.1

theorem actionEulerJointKernel_C2 (q : PhysicalResponsePoint) (reader : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    ContDiffAt ℝ 2 (actionEulerJointKernel q reader) (0,t) :=by
  have actual:=((((jointPhysicalTime_C2 (q.p+q.k) q.F (-1) t).mul
    ((jointResolvent_C2 (q.p+q.k) q.F q.z hz).comp (0,t) contDiffAt_fst)).mul
    ((noetherReader_C2 reader q.p q.F).comp (0,t) contDiffAt_fst)).mul
    ((jointResolvent_C2 q.p q.F q.w hw).comp (0,t) contDiffAt_fst)).mul
    (jointPhysicalTime_C2 q.p q.F 1 t)
  convert! actual using 1
  funext u
  simp only [actionEulerJointKernel,jointPhysicalTime,Function.comp_apply,neg_one_mul,one_mul]

theorem actionEulerInsertion_jointC2 (q : PhysicalResponsePoint) (reader : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    ContDiffAt ℝ 2 (fun u : Field289×ℝ=>sourceMatterEulerPrepared q reader u.1 u.2) (0,t) :=by
  have original:=(sourceRead q).restrictScalars ℝ |>.contDiff.contDiffAt.comp (0,t)
    (actionEulerJointKernel_C2 q reader hz hw t)
  apply original.congr_of_eventuallyEq
  have nearby:=(continuous_fst.tendsto (0,t)).eventually (actionEulerInsertion_uniform q reader)
  filter_upwards [nearby] with u same
  rw [same u.2]
  change noetherPreparedCurrent q reader u.1 u.2=
    inner ℂ (responseLeft q) (actionEulerJointKernel q reader u (responseRight q))
  simp only [noetherPreparedCurrent,preparedDual,independentDual,preparedPrimal,
    actionEulerJointKernel,ContinuousLinearMap.comp_apply,innerSL_apply_apply,mul_apply_eq_comp]

private theorem star_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F→ℂ} {x : F} (source : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (fun y=>star (f y)) x :=
  (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp x source

private theorem atMode_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F→ℂ} {x : F} (source : ContDiffAt ℝ 2 f x) (key wave : PhysicalMomentum) :
    ContDiffAt ℝ 2 (fun y=>Finsupp.single key (f y) wave) x :=by
  by_cases same : key=wave
  · simpa only [Finsupp.single_apply,if_pos same] using source
  · simp only [Finsupp.single_apply,if_neg same]
    exact contDiffAt_const

theorem actionRealCoefficient_jointC2 (q : PhysicalResponsePoint) (reader : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (wave : PhysicalMomentum) :
    ContDiffAt ℝ 2 (fun u : Field289×ℝ=>actionRealCoefficients q reader u.1 u.2 wave) (0,t) :=by
  have F:=actionEulerInsertion_jointC2 q reader hz hw t
  have R:=actionEulerInsertion_jointC2 (oppositeCoordinates q) reader hw hz t
  have DR:=actionEulerInsertion_jointC2 (crossRightCoordinates q) reader hw hw t
  have DL:=actionEulerInsertion_jointC2 (crossLeftCoordinates q) reader hz hz t
  have a:=atMode_smooth ((F.add (star_smooth R)).const_smul (1/2:ℂ)) (-q.k) wave
  have b:=atMode_smooth ((R.add (star_smooth F)).const_smul (1/2:ℂ)) q.k wave
  have c:=atMode_smooth ((DR.add (star_smooth DL)).const_smul (1/2:ℂ)) (2 • q.p+q.k) wave
  have d:=atMode_smooth ((DL.add (star_smooth DR)).const_smul (1/2:ℂ)) (-(2 • q.p+q.k)) wave
  convert! ((a.add b).add c).add d using 1

def actionModeWindowSample (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : ℂ) (i : Fin 289) (u : ℝ×ℝ) : ℂ:=
  laplaceWeight lambda u.2*actionRealEulerSource q u.2 wave (u.1 • force) i

theorem actionModeWindowSample_C2 (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : ℂ) (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) (t : ℝ) :
    ContDiffAt ℝ 2 (actionModeWindowSample q force wave lambda i) (0,t) :=by
  have path : ContDiffAt ℝ 2 (fun u : ℝ×ℝ=>(u.1 • force,u.2)) (0,t):=
    (contDiffAt_fst.smul contDiffAt_const).prodMk contDiffAt_snd
  have sourceAt : ContDiffAt ℝ 2
      (fun u : Field289×ℝ=> -actionRealCoefficients q (fieldUnit i) u.1 u.2 (-wave))
      ((0:ℝ) • force,t):=by
    simpa only [zero_smul] using (actionRealCoefficient_jointC2 q (fieldUnit i) hz hw t (-wave)).neg
  have source:=sourceAt.comp (0,t) path
  have weight : ContDiffAt ℝ 2 (fun u : ℝ×ℝ=>laplaceWeight lambda u.2) (0,t):=by
    unfold laplaceWeight
    exact (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (0,t) contDiffAt_snd)).cexp
  exact weight.mul source

private def firstPartial (S : ℝ×ℝ→ℂ) (u : ℝ×ℝ) : ℂ:=fderiv ℝ S u (1,0)

private theorem partial_derivative (S : ℝ×ℝ→ℂ) (u : ℝ×ℝ) (smooth : ContDiffAt ℝ 2 S u) :
    HasDerivAt (fun r=>S (r,u.2)) (firstPartial S u) u.1 :=by
  have hd:=smooth.differentiableAt (by norm_num) |>.hasFDerivAt
  have path:=(hasDerivAt_id u.1).prodMk (hasDerivAt_const u.1 u.2)
  exact hd.comp_hasDerivAt_of_eq u.1 path (by rfl)

private theorem partial_continuousAt (S : ℝ×ℝ→ℂ) (u : ℝ×ℝ) (smooth : ContDiffAt ℝ 2 S u) :
    ContinuousAt (firstPartial S) u :=
  ((smooth.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const).continuousAt

/-- Compactness produces the actual local derivative bound; it is not a caller-supplied response. -/
private theorem sourceFiniteWindow_derivative (S : ℝ×ℝ→ℂ) (T : ℝ)
    (sourceSmooth : ∀t∈uIcc (0:ℝ) T,ContDiffAt ℝ 2 S (0,t)) :
    HasDerivAt (fun r : ℝ=>∫t in (0:ℝ)..T,S (r,t))
      (∫t in (0:ℝ)..T,firstPartial S (0,t)) 0 :=by
  let K:=uIcc (0:ℝ) T
  let U : Set (ℝ×ℝ):={u | ContDiffAt ℝ 2 S u}
  have openU : IsOpen U:=isOpen_iff_mem_nhds.mpr (fun u hu=>(show ContDiffAt ℝ 2 S u from hu).eventually (by norm_num))
  have base : ({0}:Set ℝ) ×ˢ K⊆U:=by
    rintro ⟨r,t⟩ ⟨hr,ht⟩
    have zero : r=0:=hr
    subst r
    exact sourceSmooth t ht
  obtain ⟨a,b,ha,_hb,hzero,hcover,hproduct⟩:=
    generalized_tube_lemma (isCompact_singleton (x:=(0:ℝ))) isCompact_uIcc openU base
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (ha.mem_nhds (hzero (by rfl)))
  let R:=e/2
  have hR : 0<R:=by dsimp [R];positivity
  have tube (r : ℝ) (t : ℝ) (hr : r∈Metric.closedBall (0:ℝ) R) (ht : t∈K) : ContDiffAt ℝ 2 S (r,t):=by
    apply hproduct
    refine ⟨hball ?_,hcover ht⟩
    rw [Metric.mem_ball,dist_zero_right]
    rw [Metric.mem_closedBall,dist_zero_right] at hr
    dsimp [R] at hr
    change |r|<e
    linarith
  have dc : ContinuousOn (firstPartial S) (Metric.closedBall (0:ℝ) R ×ˢ K):=
    fun u hu=>(partial_continuousAt S u (tube u.1 u.2 hu.1 hu.2)).continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:ℝ) R).prod isCompact_uIcc |>.exists_bound_of_continuousOn dc
  have inBall : ∀r∈Metric.ball (0:ℝ) R,r∈Metric.closedBall (0:ℝ) R:=
    fun _ hr=>Metric.ball_subset_closedBall hr
  have fcont (r : ℝ) (hr : r∈Metric.closedBall (0:ℝ) R) : ContinuousOn (fun t=>S (r,t)) K:=by
    intro t ht
    exact (tube r t hr ht).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
      |>.continuousWithinAt
  have dcont : ContinuousOn (fun t=>firstPartial S (0,t)) K:=by
    intro t ht
    exact (partial_continuousAt S (0,t) (tube 0 t (Metric.mem_closedBall_self hR.le) ht)).comp
      (continuous_const.prodMk continuous_id).continuousAt |>.continuousWithinAt
  have hs : Metric.ball (0:ℝ) R∈𝓝 (0:ℝ):=Metric.ball_mem_nhds _ hR
  have lip : ∀ᵐt ∂volume.restrict (Ι (0:ℝ) T),
      LipschitzOnWith (Real.nnabs C) (fun r=>S (r,t)) (Metric.ball (0:ℝ) R) :=by
    apply (ae_restrict_mem measurableSet_uIoc).mono
    intro t ht
    have hk : t∈K:=uIoc_subset_uIcc ht
    apply (convex_ball (0:ℝ) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr=>(partial_derivative S (r,t) (tube r t (inBall r hr) hk)).hasDerivWithinAt)
    intro r hr
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_nnabs]
    exact (hC (r,t) ⟨inBall r hr,hk⟩).trans (le_abs_self C)
  have actual := hasFDerivAt_integral_of_dominated_loc_of_lip_interval
    (F:=fun r t=>S (r,t))
    (F':=fun t=>(1 : ℝ→L[ℝ] ℝ).smulRight (firstPartial S (0,t))) hs
    (by filter_upwards [hs] with r hr
        exact ((fcont r (inBall r hr)).intervalIntegrable (μ:=volume)).def'.aestronglyMeasurable)
    (fcont 0 (Metric.mem_closedBall_self hR.le)).intervalIntegrable
    (by
      have c : ContinuousOn (fun t=>(1 : ℝ→L[ℝ] ℝ).smulRight (firstPartial S (0,t))) K:=by
        intro t ht
        exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ→L[ℝ] ℝ)).continuous.continuousAt.comp_continuousWithinAt (dcont t ht))
      exact (c.intervalIntegrable (μ:=volume)).def'.aestronglyMeasurable)
    lip intervalIntegrable_const
    (by
      apply (ae_restrict_mem measurableSet_uIoc).mono
      intro t ht
      exact (partial_derivative S (0,t) (tube 0 t (Metric.mem_closedBall_self hR.le) (uIoc_subset_uIcc ht))).hasFDerivAt)
  have derivative:=actual.2.hasDerivAt
  convert derivative using 1 <;> first
    | rfl
    | (rw [ContinuousLinearMap.intervalIntegral_apply actual.1]
       simp only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul])


def actionModeWindowCurve (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : ℂ) (T r : ℝ) : Fin 289→ℂ:=
  fun i=>∫t in (0:ℝ)..T,actionModeWindowSample q force wave lambda i (r,t)

theorem actionModeWindowCurve_initial (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) :
    actionModeWindowCurve q force wave lambda T 0=modeForcing q force false wave lambda T :=by
  funext i
  apply intervalIntegral.integral_congr
  intro t _
  change laplaceWeight lambda t*actionRealEulerSource q t wave ((0:ℝ) • force) i=
    laplaceWeight lambda t*(modeJet q force false wave t i).value
  rw [zero_smul,actionRealEulerSource_timePort q t wave force i]
  rfl

theorem actionModeWindowCurve_generated (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : ℂ) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasDerivAt (actionModeWindowCurve q force wave lambda T) (modeForcing q force true wave lambda T) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  have actual:=sourceFiniteWindow_derivative (actionModeWindowSample q force wave lambda i) T
    (fun t _=>actionModeWindowSample_C2 q force wave lambda hz hw i t)
  have each (t : ℝ) : firstPartial (actionModeWindowSample q force wave lambda i) (0,t)=
      laplaceWeight lambda t*(modeJet q force true wave t i).value:=by
    have first:=partial_derivative _ (0,t) (actionModeWindowSample_C2 q force wave lambda hz hw i t)
    have source:=((hasDerivAt_pi.mp (actionRealEulerSource_generated q t wave force hz hw)) i).const_mul
      (laplaceWeight lambda t)
    have same:=first.unique source
    change firstPartial (actionModeWindowSample q force wave lambda i) (0,t)=
      laplaceWeight lambda t*realEulerSlope q force t (-wave) i at same
    rw [same,modeJet,realEulerTimeJet_value]
    rfl
  apply actual.congr_deriv
  exact intervalIntegral.integral_congr (fun t _=>each t)

end LowEnergy.PreparationVacuumMatterEulerFeedback
