import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteTransferFiber

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteTransferWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalNativeSoftWardBoundary CanonicalGradedSpatialSource
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace
local instance : NormedAlgebra ℝ FiberOperators:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ FiberOperators:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : CompleteSpace FiberOperators:=ContinuousLinearMap.instCompleteSpace

/-- The original finite momentum translation has the same generated whole-carrier growth price. -/
theorem sourceTransferShiftFlow_bound (shift : PhysicalMomentum) (time : ℝ) :
    ‖shiftFlow shift time‖≤1+|time| *sourceRate 0 := by
  have bound : ‖momentumShiftFlow shift time‖≤1+|time| *sourceRate 0:=
    multiplier_norm _ _ _ _ (by unfold sourceRate;positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold sourceRate;positivity)
  intro v
  change ‖fourier.symm (momentumShiftFlow shift time (fourier v))‖≤_
  rw [fourier.symm.norm_map]
  exact ((momentumShiftFlow shift time).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right bound (norm_nonneg _)).trans_eq (by rw [fourier.norm_map]))

/-- This continuity belongs to the actual translated flow on all original L2 inputs. -/
theorem sourceTransferShiftFlow_continuous (shift : PhysicalMomentum) (v : FullMatterL2) :
    Continuous (fun time=>shiftFlow shift time v) := by
  have joint : Continuous (fun tx : ℝ×Position=>shiftMatrices shift tx.1 tx.2) := by
    have momentum : Continuous (fun tx : ℝ×Position=>fun j=>physicalMomentum tx.2 j+shift j) :=
      (physicalMomentum_continuous.comp continuous_snd).add continuous_const
    have generator:=(original_drift_continuous 0).comp momentum
    exact NormedSpace.exp_continuous.comp (continuous_fst.smul generator)
  have generated:=liftedFamily_stronglyContinuous (shiftMatrices shift) joint
    (sourceRate 0) (norm_nonneg _) (shiftMatrices_bound shift) (fourier v)
  exact fourier.symm.continuous.comp generated

theorem sourceTransferShiftFlow_zero (shift : PhysicalMomentum) : shiftFlow shift 0=(1:FullMatterL2→L[ℂ]FullMatterL2) := by
  apply ContinuousLinearMap.ext
  intro v
  apply fourier.injective
  apply Lp.ext
  filter_upwards [shiftFlow_fourier shift 0 v] with k value
  change fourier (shiftFlow shift 0 v) k=fourier v k
  rw [value,evolution_zero]
  rfl

private theorem sourceTransferShiftFlow_zero_apply (shift : PhysicalMomentum) (v : FullMatterL2) : shiftFlow shift 0 v=v := by
  rw [sourceTransferShiftFlow_zero]
  rfl

theorem sourceTransferShiftFlow_zeroShift (time : ℝ) : shiftFlow 0 time=spatialFlow 0 time := by
  apply ContinuousLinearMap.ext
  intro v
  apply fourier.injective
  apply Lp.ext
  filter_upwards [shiftFlow_fourier 0 time v,spatialFlow_fourier_ae 0 time v] with k shifted original
  simp only [Pi.zero_apply,add_zero] at shifted
  exact shifted.trans original.symm

theorem sourceTransferShiftFlow_group (shift : PhysicalMomentum) (t s : ℝ) :
    shiftFlow shift t*shiftFlow shift s=shiftFlow shift (t+s) := by
  apply ContinuousLinearMap.ext
  intro v
  apply fourier.injective
  apply Lp.ext
  filter_upwards [shiftFlow_fourier shift t (shiftFlow shift s v),shiftFlow_fourier shift s v,
    shiftFlow_fourier shift (t+s) v] with k outer inner both
  change fourier (shiftFlow shift t (shiftFlow shift s v)) k=_
  rw [outer,inner,both,evolution_add]
  rfl

/-- The full source flow acts on every original L2 preparation. -/
def sourceTransferSpatial (dual : Bool) (left right : PhysicalMomentum) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  shiftFlow left (-time)*(sourceWardGenerator dual).compLpL 2 volume*shiftFlow right time

def sourceTransferCurrent (dual : Bool) (left right : PhysicalMomentum) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  shiftFlow left (-time)*(sourceTransferInsertion dual (left-right)).compLpL 2 volume*shiftFlow right time

private theorem constant_transport_fourier (A : FiberOperators) (left right : PhysicalMomentum) (time : ℝ) (v : FullMatterL2) :
    fourier ((shiftFlow left (-time)*A.compLpL 2 volume*shiftFlow right time : FullMatterL2→L[ℂ]FullMatterL2) v)=ᵐ[volume]
      fun k=>(evolution actual 0 (physicalMomentum k+left) (-time)*A*evolution actual 0 (physicalMomentum k+right) time)
        (fourier v k) := by
  filter_upwards [shiftFlow_fourier left (-time) (A.compLpL 2 volume (shiftFlow right time v)),
    A.coeFn_compLpL (fourier (shiftFlow right time v)),shiftFlow_fourier right time v] with k outer middle inner
  change fourier (shiftFlow left (-time) (A.compLpL 2 volume (shiftFlow right time v))) k=_
  rw [outer,GaugeGreen.constant_fourier,middle,inner]
  rfl

private theorem constant_transport_read (A : FiberOperators) (left right : PhysicalMomentum) (time : ℝ) (u v : FullMatterL2) :
    inner ℂ u ((shiftFlow left (-time)*A.compLpL 2 volume*shiftFlow right time : FullMatterL2→L[ℂ]FullMatterL2) v)=
      ∫k : Position,inner ℂ (fourier u k)
        ((evolution actual 0 (physicalMomentum k+left) (-time)*A*evolution actual 0 (physicalMomentum k+right) time)
          (fourier v k)) := by
  rw [←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae ((constant_transport_fourier A left right time v).mono fun k h=>congrArg (fun w : Hilbert=>inner ℂ (fourier u k) w) h)

private theorem fiber_continuous (A : FiberOperators) (left right : PhysicalMomentum) (time : ℝ) :
    Continuous (fun k : Position=>evolution actual 0 (physicalMomentum k+left) (-time)*A*
      evolution actual 0 (physicalMomentum k+right) time) :=
  ((shiftMatrices_continuous left (-time)).mul continuous_const).mul (shiftMatrices_continuous right time)

theorem sourceTransferTransport_continuous (A : FiberOperators) (left right : PhysicalMomentum) (v : FullMatterL2) :
    Continuous (fun t=>(shiftFlow left (-t)*A.compLpL 2 volume*shiftFlow right t : FullMatterL2→L[ℂ]FullMatterL2) v) := by
  let curve (t : ℝ):=A.compLpL 2 volume (shiftFlow right t v)
  have continuousCurve : Continuous curve:=
    (A.compLpL 2 volume).continuous.comp (sourceTransferShiftFlow_continuous right v)
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have size : Continuous (fun t : ℝ=>1+|t| *sourceRate 0):=by fun_prop
  have scalarLimit : Tendsto (fun t=>(1+|t| *sourceRate 0)*‖curve t-curve t₀‖) (𝓝 t₀) (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using
      (size.tendsto t₀).mul ((continuousCurve.tendsto t₀).sub (tendsto_const_nhds (x:=curve t₀))).norm
  have zeroLimit : Tendsto (fun t=>shiftFlow left (-t) (curve t-curve t₀)) (𝓝 t₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun t=>norm_nonneg _) _ scalarLimit
    intro t
    have bound:=sourceTransferShiftFlow_bound left (-t)
    simp only [abs_neg] at bound
    exact ((shiftFlow left (-t)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
  have generated:=zeroLimit.add (((sourceTransferShiftFlow_continuous left (curve t₀)).comp continuous_neg).tendsto t₀)
  simpa only [ContinuousAt,Function.comp_apply,map_sub,sub_add_cancel,zero_add,curve,mul_apply_eq_comp] using generated

/-- Original linear growth supplies a uniform current bound; no momentum profile is an input. -/
theorem sourceTransferCurrent_bound (dual : Bool) (left right : PhysicalMomentum) (time : ℝ) :
    ‖sourceTransferCurrent dual left right time‖≤(1+|time| *sourceRate 0)^2*‖sourceTransferInsertion dual (left-right)‖ := by
  have backward:=sourceTransferShiftFlow_bound left (-time)
  simp only [abs_neg] at backward
  exact (norm_mul_le_of_le (norm_mul_le_of_le backward
    ((sourceTransferInsertion dual (left-right)).norm_compLpL_le (p:=2) (μ:=volume))) (sourceTransferShiftFlow_bound right time)).trans_eq (by ring)

theorem sourceTransferCurrent_continuous (dual : Bool) (left right : PhysicalMomentum) (v : FullMatterL2) :
    Continuous (fun t=>sourceTransferCurrent dual left right t v):=sourceTransferTransport_continuous _ left right _

/-- Fourier differentiation keeps all 252 components and the same full-Y current. -/
theorem sourceTransferSpatial_weakDerivative (dual : Bool) (left right : PhysicalMomentum) (u v : FullMatterL2) (time : ℝ) :
    HasDerivAt (fun t=>inner ℂ u (sourceTransferSpatial dual left right t v))
      (inner ℂ u (Complex.I • sourceTransferCurrent dual left right time v)) time := by
  let F (t : ℝ) (k : Position):=inner ℂ (fourier u k) (sourceTransferFiber dual left right (physicalMomentum k) t (fourier v k))
  let D (t : ℝ) (k : Position):=inner ℂ (fourier u k)
    (Complex.I • sourceTransferCurrentFiber dual left right (physicalMomentum k) t (fourier v k))
  let M:=(1+(|time|+1)*sourceRate 0)^2*‖sourceTransferInsertion dual (left-right)‖
  let bound (k : Position):=M*(‖fourier u k‖^2+‖fourier v k‖^2)
  have measurableF (t : ℝ) : AEStronglyMeasurable (F t) volume:=
    (Lp.aestronglyMeasurable (fourier u)).inner
      (multiplier_measurable _ (fiber_continuous (sourceWardGenerator dual) left right t) (fourier v))
  have measurableD (t : ℝ) : AEStronglyMeasurable (D t) volume:=
    (Lp.aestronglyMeasurable (fourier u)).inner
      ((multiplier_measurable _ (fiber_continuous (sourceTransferInsertion dual (left-right)) left right t) (fourier v)).const_smul Complex.I)
  have integrableF : Integrable (F time) volume := by
    have actual:=L2.integrable_inner (𝕜:=ℂ) (fourier u) (fourier (sourceTransferSpatial dual left right time v))
    exact actual.congr ((constant_transport_fourier (sourceWardGenerator dual) left right time v).mono fun k h=>congrArg (fun w : Hilbert=>inner ℂ (fourier u k) w) h)
  have integrableBound : Integrable bound volume:=
    (((memLp_two_iff_integrable_sq_norm (Lp.memLp (fourier u)).aestronglyMeasurable).mp (Lp.memLp (fourier u))).add
      ((memLp_two_iff_integrable_sq_norm (Lp.memLp (fourier v)).aestronglyMeasurable).mp (Lp.memLp (fourier v)))).const_mul M
  have derivative (t : ℝ) (k : Position) : HasDerivAt (fun s=>F s k) (D t k) t := by
    let read : FiberOperators→L[ℝ]ℂ:=
      ((innerSL ℂ (fourier u k)).comp (ContinuousLinearMap.apply ℂ Hilbert (fourier v k))).restrictScalars ℝ
    exact read.hasFDerivAt.comp_hasDerivAt t (sourceTransferFiber_derivative dual left right (physicalMomentum k) t)
  have bounded : ∀ᵐ k ∂volume,∀ t∈Metric.ball time 1,‖D t k‖≤bound k := by
    apply ae_of_all
    intro k t near
    have near' : |t-time|<1:=by simpa only [Metric.mem_ball,Real.dist_eq] using near
    have small : |t|≤|time|+1:=by
      have triangle:=abs_add_le (t-time) time
      rw [sub_add_cancel] at triangle
      linarith
    have op : ‖sourceTransferCurrentFiber dual left right (physicalMomentum k) t‖≤M :=
      (sourceTransferCurrentFiber_bound dual left right _ t).trans (by dsimp [M,sourceRate]; gcongr)
    have pos : 0≤M:=by dsimp [M,sourceRate]; positivity
    calc
      ‖D t k‖≤‖fourier u k‖*‖Complex.I • sourceTransferCurrentFiber dual left right (physicalMomentum k) t (fourier v k)‖:=norm_inner_le_norm _ _
      _=‖fourier u k‖*‖sourceTransferCurrentFiber dual left right (physicalMomentum k) t (fourier v k)‖:=by rw [norm_smul,Complex.norm_I,one_mul]
      _≤‖fourier u k‖*(M*‖fourier v k‖):=mul_le_mul_of_nonneg_left
        (((sourceTransferCurrentFiber dual left right (physicalMomentum k) t).le_opNorm _).trans (mul_le_mul_of_nonneg_right op (norm_nonneg _))) (norm_nonneg _)
      _=M*(‖fourier u k‖*‖fourier v k‖):=by ring
      _≤bound k:=mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (‖fourier u k‖-‖fourier v k‖),sq_nonneg ‖fourier u k‖,sq_nonneg ‖fourier v k‖]) pos
  have generated:=(hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds time (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall measurableF) integrableF (measurableD time) bounded integrableBound
    (ae_of_all _ fun k t _=>derivative t k)).2
  have read (t : ℝ) : inner ℂ u (sourceTransferSpatial dual left right t v)=∫k : Position,F t k:=
    constant_transport_read (sourceWardGenerator dual) left right t u v
  have readD : inner ℂ u (Complex.I • sourceTransferCurrent dual left right time v)=∫k : Position,D time k := by
    rw [sourceTransferCurrent,inner_smul_right,constant_transport_read,←integral_const_mul]
    simp only [D,sourceTransferCurrentFiber,inner_smul_right]
  simpa only [←read,←readD] using generated

/-- Whole-carrier Duhamel: both initial and final preparation variations are retained. -/
theorem sourceTransferSpatial_boundary (dual : Bool) (left right : PhysicalMomentum) (v : FullMatterL2) (time : ℝ) :
    Complex.I • (∫s in (0:ℝ)..time,sourceTransferCurrent dual left right s v)=
      sourceTransferSpatial dual left right time v-(sourceWardGenerator dual).compLpL 2 volume v := by
  apply ext_inner_left ℂ
  intro u
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>sourceTransferSpatial_weakDerivative dual left right u v s)
    ((continuous_const.inner ((sourceTransferCurrent_continuous dual left right v).const_smul Complex.I)).intervalIntegrable (0:ℝ) time)
  have pull:=(innerSL ℂ u).intervalIntegral_comp_comm
    ((sourceTransferCurrent_continuous dual left right v).intervalIntegrable (μ:=volume) (0:ℝ) time)
  change (∫s in (0:ℝ)..time,inner ℂ u (sourceTransferCurrent dual left right s v))=
    inner ℂ u (∫s in (0:ℝ)..time,sourceTransferCurrent dual left right s v) at pull
  simpa only [inner_smul_right,intervalIntegral.integral_const_mul,sourceTransferSpatial,neg_zero,
    mul_apply_eq_comp,sourceTransferShiftFlow_zero_apply,inner_sub_right,←pull] using generated

/-- The strong derivative is generated from the whole-L2 Duhamel law. -/
theorem sourceTransferSpatial_derivative (dual : Bool) (left right : PhysicalMomentum) (v : FullMatterL2) (time : ℝ) :
    HasDerivAt (fun t=>sourceTransferSpatial dual left right t v)
      (Complex.I • sourceTransferCurrent dual left right time v) time := by
  have continuous:=sourceTransferCurrent_continuous dual left right v
  have generated:=(intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable (0:ℝ) time)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt).const_smul Complex.I
  have initial (t : ℝ) : Complex.I • (∫s in (0:ℝ)..t,sourceTransferCurrent dual left right s v)+
      (sourceWardGenerator dual).compLpL 2 volume v=sourceTransferSpatial dual left right t v := by
    rw [sourceTransferSpatial_boundary,sub_add_cancel]
  simpa only [Pi.smul_apply,initial] using generated.add_const ((sourceWardGenerator dual).compLpL 2 volume v)

end LowEnergy.PreparationPhysicalFiniteTransferWard
