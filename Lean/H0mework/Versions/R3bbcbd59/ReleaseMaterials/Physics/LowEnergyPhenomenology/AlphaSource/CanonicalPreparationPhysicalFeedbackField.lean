import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalFullSourceWindow
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalGreenFeedback
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace Interval
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator jointResolvent rawReader rawReaderContact
  originalJacobi originalChange originalReadback originalRowLift extendedKernel sourceGreen sourceCompatibility

def jointPhysicalTime (p : PhysicalMomentum) (F : Index) (rate : ℝ) (u : Field289×ℝ) : Op:=
  physicalTime p F (rate*u.2) u.1

theorem jointPhysicalTime_C2 (p : PhysicalMomentum) (F : Index) (rate t : ℝ) :
    ContDiffAt ℝ 2 (jointPhysicalTime p F rate) (0,t) :=by
  have hc:=(jointGenerator_C2 p F 0).comp (0,t) contDiffAt_fst
  have inner : ContDiffAt ℝ 2 (fun u : Field289×ℝ=>(rate*u.2) • ((-Complex.I) • jointGenerator p F 0 u.1)) (0,t):=
    (contDiffAt_const.mul contDiffAt_snd).smul (hc.const_smul (-Complex.I))
  exact (NormedSpace.exp_analytic (𝕂:=ℝ) _).contDiffAt.comp (0,t) inner

def jointFiveKernel (reader : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ)
    (u : Field289×ℝ) : Op:=fiveKernel reader p k F z w u.2 u.1

theorem jointFiveKernel_C2 (reader : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (t : ℝ) :
    ContDiffAt ℝ 2 (jointFiveKernel reader p k F z w) (0,t) :=by
  have hl:=jointPhysicalTime_C2 (p+k) F (-1) t
  have hr:=jointPhysicalTime_C2 p F 1 t
  have l:=(jointResolvent_C2 (p+k) F z hz).comp (0,t) contDiffAt_fst
  have r:=(jointResolvent_C2 p F w hw).comp (0,t) contDiffAt_fst
  have a:=(rawReader_C2 reader p F).comp (0,t) contDiffAt_fst
  have all:=(((hl.mul l).mul a).mul r).mul hr
  convert! all using 1
  funext u
  simp only [jointPhysicalTime,jointFiveKernel,fiveKernel,neg_one_mul,one_mul,Function.comp_apply]

def windowSample (q : PhysicalResponsePoint) (force : Field289) (lambda : ℂ) (i : Fin 289)
    (u : ℝ×ℝ) : ℂ:=
  laplaceWeight lambda u.2*(sourceJet q (u.1 • force) u.2 i).value

theorem windowSample_C2 (q : PhysicalResponsePoint) (force : Field289) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) (t : ℝ) :
    ContDiffAt ℝ 2 (windowSample q force lambda i) (0,t) :=by
  have path : ContDiffAt ℝ 2 (fun u : ℝ×ℝ=>(u.1 • force,u.2)) (0,t):=
    (contDiffAt_fst.smul contDiffAt_const).prodMk contDiffAt_snd
  have kernel:=jointFiveKernel_C2 (fieldUnit i) q.p q.k q.F q.z q.w hz hw t
  have kernelPath : ContDiffAt ℝ 2 (fun u : ℝ×ℝ=>jointFiveKernel (fieldUnit i) q.p q.k q.F q.z q.w (u.1 • force,u.2)) (0,t):=by
    have aligned : ContDiffAt ℝ 2 (jointFiveKernel (fieldUnit i) q.p q.k q.F q.z q.w) ((0:ℝ) • force,t):=by
      simpa only [zero_smul] using kernel
    exact aligned.comp (0,t) path
  have source:=(sourceRead q).restrictScalars ℝ |>.contDiff.contDiffAt.comp (0,t) kernelPath
  have weight : ContDiffAt ℝ 2 (fun u : ℝ×ℝ=>laplaceWeight lambda u.2) (0,t):=by
    unfold laplaceWeight
    exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (0,t) contDiffAt_snd)).cexp
  have generated:=weight.mul source.neg
  convert! generated using 1
  ext u
  simp only [windowSample,sourceJet,negativeJet,pairJet,rawKernelJet_value,sourceRead,
    ContinuousLinearMap.coe_restrictScalars,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    jointFiveKernel,Function.comp_apply]
  rfl

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
private theorem finiteWindow_derivative (S : ℝ×ℝ→ℂ) (T : ℝ)
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

def windowForcingCurve (q : PhysicalResponsePoint) (force : Field289) (lambda : ℂ) (T r : ℝ) : Fin 289→ℂ:=
  fun i=>∫t in (0:ℝ)..T,windowSample q force lambda i (r,t)

theorem fullForcing_generated (q : PhysicalResponsePoint) (force : Field289) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasDerivAt (windowForcingCurve q force lambda T) (fullForcing q force true lambda T) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  have actual:=finiteWindow_derivative (windowSample q force lambda i) T
    (fun t _=>windowSample_C2 q force lambda hz hw i t)
  have same (t : ℝ) : firstPartial (windowSample q force lambda i) (0,t)=
      laplaceWeight lambda t*(sourceSlopeJet q force t i).value :=by
    have h:=(partial_derivative _ (0,t) (windowSample_C2 q force lambda hz hw i t))
    have hs := ((rawPrepared_generated q.epsilon q.precision (fieldUnit i) force q.p q.k q.F q.z q.w hz hw t
      q.left q.right q.lc q.ls q.rc q.rs).neg).const_mul (laplaceWeight lambda t)
    simp only [windowSample,sourceJet_value,sourceSlopeJet_value,eulerCovector,eulerCovectorSlope] at h ⊢
    exact h.unique hs
  apply actual.congr_deriv
  simp only [fullForcing,fullSourceJet,↓reduceIte]
  exact intervalIntegral.integral_congr (fun t _=>same t)

def physicalSpatial (k : PhysicalMomentum) : Fin 3→ℂ:=fun i=>Complex.I*(k i:ℂ)

def physicalSpectralDomain (k : PhysicalMomentum) : Set ℂ:=
  {lambda | fullMomentum (physicalSpatial k) lambda∈regularSource}

/-- The original H consumes the actual signed full source directly. -/
def physicalField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (physicalSpatial k) lambda.val,lambda.property⟩
    (fullForcing q force response lambda.val T)

theorem physicalField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ) :
    originalJacobi (fullMomentum (physicalSpatial k) lambda.val)*ᵥphysicalField q force response k lambda T=
      fullForcing q force response lambda.val T-originalRowLift (fullMomentum (physicalSpatial k) lambda.val)*ᵥ
        sourceCompatibility (fullMomentum (physicalSpatial k) lambda.val) (fullForcing q force response lambda.val T) :=
  original_forced_field ⟨fullMomentum (physicalSpatial k) lambda.val,lambda.property⟩
    (fullForcing q force response lambda.val T)

theorem physicalField_cosources (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ) :
    physicalField q force response k lambda T=
      originalChange (fullMomentum (physicalSpatial k) lambda.val)*ᵥ
        ((contactInverse (fullMomentum (physicalSpatial k) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (physicalSpatial k) lambda.val))⁻¹)*ᵥ
            (fun row=>(∫r in (0:ℝ)..T,laplaceWeight lambda.val r*
              fullTimeSource q force response (physicalSpatial k) r row)-
                (fullBoundary q force response (physicalSpatial k) lambda.val T row-
                  fullBoundary q force response (physicalSpatial k) lambda.val 0 row))) :=by
  have read : originalReadback (fullMomentum (physicalSpatial k) lambda.val)*ᵥfullForcing q force response lambda.val T=_ :=
    funext (fullForcing_readback q force response (physicalSpatial k) lambda.val T)
  unfold physicalField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,read]

def physicalFieldCurve (q : PhysicalResponsePoint) (force : Field289)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T r : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (physicalSpatial k) lambda.val,lambda.property⟩
    (windowForcingCurve q force lambda.val T r)

theorem physicalFieldCurve_original (q : PhysicalResponsePoint) (force : Field289)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ) :
    physicalFieldCurve q force k lambda T 0=physicalField q force false k lambda T :=by
  unfold physicalFieldCurve physicalField
  congr 1
  funext i
  simp only [windowForcingCurve,windowSample,zero_smul,fullForcing,fullSourceJet,
    Bool.false_eq_true,↓reduceIte]

theorem physicalField_generated (q : PhysicalResponsePoint) (force : Field289)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasDerivAt (physicalFieldCurve q force k lambda T) (physicalField q force true k lambda T) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  simp only [physicalFieldCurve,physicalField,PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (fullForcing_generated q force lambda.val hz hw T)) j).const_mul _

end LowEnergy.PreparationVacuumPhysicalFeedback
