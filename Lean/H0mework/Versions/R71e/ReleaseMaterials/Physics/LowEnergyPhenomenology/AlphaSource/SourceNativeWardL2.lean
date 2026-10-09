import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeWardTime
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeSoftWardBoundary
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace
local instance : NormedAlgebra ℝ FiberOperators:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ FiberOperators:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : CompleteSpace FiberOperators:=ContinuousLinearMap.instCompleteSpace

/-- The full source flow acts on every original L2 preparation. -/
def sourceWardSpatial (dual : Bool) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  spatialFlow 0 (-time)*(sourceWardGenerator dual).compLpL 2 volume*spatialFlow 0 time

def sourceWardCurrent (dual : Bool) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  spatialFlow 0 (-time)*(sourceWardInsertion dual).compLpL 2 volume*spatialFlow 0 time

private theorem constant_conjugate_fourier (A : FiberOperators) (time : ℝ) (v : FullMatterL2) :
    fourier ((spatialFlow 0 (-time)*A.compLpL 2 volume*spatialFlow 0 time : FullMatterL2→L[ℂ]FullMatterL2) v)=ᵐ[volume]
      fun k=>(evolution actual 0 (physicalMomentum k) (-time)*A*evolution actual 0 (physicalMomentum k) time)
        (fourier v k) := by
  filter_upwards [spatialFlow_fourier_ae 0 (-time) (A.compLpL 2 volume (spatialFlow 0 time v)),
    A.coeFn_compLpL (fourier (spatialFlow 0 time v)),spatialFlow_fourier_ae 0 time v] with k outer middle inner
  change fourier (spatialFlow 0 (-time) (A.compLpL 2 volume (spatialFlow 0 time v))) k=_
  rw [outer,GaugeGreen.constant_fourier,middle,inner]
  rfl

private theorem constant_conjugate_read (A : FiberOperators) (time : ℝ) (u v : FullMatterL2) :
    inner ℂ u ((spatialFlow 0 (-time)*A.compLpL 2 volume*spatialFlow 0 time : FullMatterL2→L[ℂ]FullMatterL2) v)=
      ∫k : Position,inner ℂ (fourier u k)
        ((evolution actual 0 (physicalMomentum k) (-time)*A*evolution actual 0 (physicalMomentum k) time)
          (fourier v k)) := by
  rw [←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae ((constant_conjugate_fourier A time v).mono fun k h=>congrArg (fun w : Hilbert=>inner ℂ (fourier u k) w) h)

private theorem fiber_continuous (A : FiberOperators) (time : ℝ) :
    Continuous (fun k : Position=>evolution actual 0 (physicalMomentum k) (-time)*A*
      evolution actual 0 (physicalMomentum k) time) := by
  have flow (s : ℝ) : Continuous (fun k : Position=>evolution actual 0 (physicalMomentum k) s):=
    (fullMatrices_continuous 0).comp (continuous_const.prodMk continuous_id)
  exact ((flow (-time)).mul continuous_const).mul (flow time)

theorem sourceWardConjugate_continuous (A : FiberOperators) (v : FullMatterL2) :
    Continuous (fun t=>(spatialFlow 0 (-t)*A.compLpL 2 volume*spatialFlow 0 t : FullMatterL2→L[ℂ]FullMatterL2) v) := by
  let curve (t : ℝ):=A.compLpL 2 volume (spatialFlow 0 t v)
  have continuousCurve : Continuous curve:=
    (A.compLpL 2 volume).continuous.comp (spatialFlow_stronglyContinuous 0 v)
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have size : Continuous (fun t : ℝ=>1+|t| *sourceRate 0):=by fun_prop
  have scalarLimit : Tendsto (fun t=>(1+|t| *sourceRate 0)*‖curve t-curve t₀‖) (𝓝 t₀) (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using
      (size.tendsto t₀).mul ((continuousCurve.tendsto t₀).sub (tendsto_const_nhds (x:=curve t₀))).norm
  have zeroLimit : Tendsto (fun t=>spatialFlow 0 (-t) (curve t-curve t₀)) (𝓝 t₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun t=>norm_nonneg _) _ scalarLimit
    intro t
    have bound:=spatialFlow_norm 0 (-t)
    simp only [abs_neg] at bound
    exact ((spatialFlow 0 (-t)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
  have generated:=zeroLimit.add (((spatialFlow_stronglyContinuous 0 (curve t₀)).comp continuous_neg).tendsto t₀)
  simpa only [ContinuousAt,Function.comp_apply,map_sub,sub_add_cancel,zero_add,curve,mul_apply_eq_comp] using generated

/-- Original linear growth supplies a uniform current bound; no momentum profile is an input. -/
theorem sourceWardCurrent_bound (dual : Bool) (time : ℝ) :
    ‖sourceWardCurrent dual time‖≤(1+|time| *sourceRate 0)^2*‖sourceWardInsertion dual‖ := by
  have backward:=spatialFlow_norm 0 (-time)
  simp only [abs_neg] at backward
  exact (norm_mul_le_of_le (norm_mul_le_of_le backward
    ((sourceWardInsertion dual).norm_compLpL_le (p:=2) (μ:=volume))) (spatialFlow_norm 0 time)).trans_eq (by ring)

theorem sourceWardCurrent_continuous (dual : Bool) (v : FullMatterL2) :
    Continuous (fun t=>sourceWardCurrent dual t v):=sourceWardConjugate_continuous _ _

/-- Fourier differentiation keeps all 252 components and the same full-Y current. -/
theorem sourceWardSpatial_weakDerivative (dual : Bool) (u v : FullMatterL2) (time : ℝ) :
    HasDerivAt (fun t=>inner ℂ u (sourceWardSpatial dual t v))
      (inner ℂ u (Complex.I • sourceWardCurrent dual time v)) time := by
  let F (t : ℝ) (k : Position):=inner ℂ (fourier u k) (sourceWardFiber dual (physicalMomentum k) t (fourier v k))
  let D (t : ℝ) (k : Position):=inner ℂ (fourier u k)
    (Complex.I • sourceWardCurrentFiber dual (physicalMomentum k) t (fourier v k))
  let M:=(1+(|time|+1)*sourceRate 0)^2*‖sourceWardInsertion dual‖
  let bound (k : Position):=M*(‖fourier u k‖^2+‖fourier v k‖^2)
  have measurableF (t : ℝ) : AEStronglyMeasurable (F t) volume:=
    (Lp.aestronglyMeasurable (fourier u)).inner
      (multiplier_measurable _ (fiber_continuous (sourceWardGenerator dual) t) (fourier v))
  have measurableD (t : ℝ) : AEStronglyMeasurable (D t) volume:=
    (Lp.aestronglyMeasurable (fourier u)).inner
      ((multiplier_measurable _ (fiber_continuous (sourceWardInsertion dual) t) (fourier v)).const_smul Complex.I)
  have integrableF : Integrable (F time) volume := by
    have actual:=L2.integrable_inner (𝕜:=ℂ) (fourier u) (fourier (sourceWardSpatial dual time v))
    exact actual.congr ((constant_conjugate_fourier (sourceWardGenerator dual) time v).mono fun k h=>congrArg (fun w : Hilbert=>inner ℂ (fourier u k) w) h)
  have integrableBound : Integrable bound volume:=
    (((memLp_two_iff_integrable_sq_norm (Lp.memLp (fourier u)).aestronglyMeasurable).mp (Lp.memLp (fourier u))).add
      ((memLp_two_iff_integrable_sq_norm (Lp.memLp (fourier v)).aestronglyMeasurable).mp (Lp.memLp (fourier v)))).const_mul M
  have derivative (t : ℝ) (k : Position) : HasDerivAt (fun s=>F s k) (D t k) t := by
    let read : FiberOperators→L[ℝ]ℂ:=
      ((innerSL ℂ (fourier u k)).comp (ContinuousLinearMap.apply ℂ Hilbert (fourier v k))).restrictScalars ℝ
    exact read.hasFDerivAt.comp_hasDerivAt t (sourceWardFiber_derivative dual (physicalMomentum k) t)
  have bounded : ∀ᵐ k ∂volume,∀ t∈Metric.ball time 1,‖D t k‖≤bound k := by
    apply ae_of_all
    intro k t near
    have near' : |t-time|<1:=by simpa only [Metric.mem_ball,Real.dist_eq] using near
    have small : |t|≤|time|+1:=by
      have triangle:=abs_add_le (t-time) time
      rw [sub_add_cancel] at triangle
      linarith
    have op : ‖sourceWardCurrentFiber dual (physicalMomentum k) t‖≤M :=
      (sourceWardCurrentFiber_bound dual _ t).trans (by dsimp [M,sourceRate]; gcongr)
    have pos : 0≤M:=by dsimp [M,sourceRate]; positivity
    calc
      ‖D t k‖≤‖fourier u k‖*‖Complex.I • sourceWardCurrentFiber dual (physicalMomentum k) t (fourier v k)‖:=norm_inner_le_norm _ _
      _=‖fourier u k‖*‖sourceWardCurrentFiber dual (physicalMomentum k) t (fourier v k)‖:=by rw [norm_smul,Complex.norm_I,one_mul]
      _≤‖fourier u k‖*(M*‖fourier v k‖):=mul_le_mul_of_nonneg_left
        (((sourceWardCurrentFiber dual (physicalMomentum k) t).le_opNorm _).trans (mul_le_mul_of_nonneg_right op (norm_nonneg _))) (norm_nonneg _)
      _=M*(‖fourier u k‖*‖fourier v k‖):=by ring
      _≤bound k:=mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (‖fourier u k‖-‖fourier v k‖),sq_nonneg ‖fourier u k‖,sq_nonneg ‖fourier v k‖]) pos
  have generated:=(hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds time (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall measurableF) integrableF (measurableD time) bounded integrableBound
    (ae_of_all _ fun k t _=>derivative t k)).2
  have read (t : ℝ) : inner ℂ u (sourceWardSpatial dual t v)=∫k : Position,F t k:=
    constant_conjugate_read (sourceWardGenerator dual) t u v
  have readD : inner ℂ u (Complex.I • sourceWardCurrent dual time v)=∫k : Position,D time k := by
    rw [sourceWardCurrent,inner_smul_right,constant_conjugate_read,←integral_const_mul]
    simp only [D,sourceWardCurrentFiber,inner_smul_right]
  simpa only [←read,←readD] using generated

/-- Whole-carrier Duhamel: both initial and final preparation variations are retained. -/
theorem sourceWardSpatial_boundary (dual : Bool) (v : FullMatterL2) (time : ℝ) :
    Complex.I • (∫s in (0:ℝ)..time,sourceWardCurrent dual s v)=
      sourceWardSpatial dual time v-(sourceWardGenerator dual).compLpL 2 volume v := by
  apply ext_inner_left ℂ
  intro u
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>sourceWardSpatial_weakDerivative dual u v s)
    ((continuous_const.inner ((sourceWardCurrent_continuous dual v).const_smul Complex.I)).intervalIntegrable (0:ℝ) time)
  have pull:=(innerSL ℂ u).intervalIntegral_comp_comm
    ((sourceWardCurrent_continuous dual v).intervalIntegrable (μ:=volume) (0:ℝ) time)
  change (∫s in (0:ℝ)..time,inner ℂ u (sourceWardCurrent dual s v))=
    inner ℂ u (∫s in (0:ℝ)..time,sourceWardCurrent dual s v) at pull
  simpa only [inner_smul_right,intervalIntegral.integral_const_mul,sourceWardSpatial,neg_zero,
    mul_apply_eq_comp,spatialFlow_zero,inner_sub_right,←pull] using generated

/-- The strong derivative is generated from the whole-L2 Duhamel law. -/
theorem sourceWardSpatial_derivative (dual : Bool) (v : FullMatterL2) (time : ℝ) :
    HasDerivAt (fun t=>sourceWardSpatial dual t v)
      (Complex.I • sourceWardCurrent dual time v) time := by
  have continuous:=sourceWardCurrent_continuous dual v
  have generated:=(intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable (0:ℝ) time)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt).const_smul Complex.I
  have initial (t : ℝ) : Complex.I • (∫s in (0:ℝ)..t,sourceWardCurrent dual s v)+
      (sourceWardGenerator dual).compLpL 2 volume v=sourceWardSpatial dual t v := by
    rw [sourceWardSpatial_boundary,sub_add_cancel]
  simpa only [Pi.smul_apply,initial] using generated.add_const ((sourceWardGenerator dual).compLpL 2 volume v)

end LowEnergy.PreparationPhysicalNativeSoftWardBoundary
