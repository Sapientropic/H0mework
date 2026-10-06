import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylCutoff
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarGuard
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeyl
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationActualFactor
open PreparationScalarCoordinates PreparationChartGuard SourceQuantumGaugeSliceCoordinates
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology FourierTransform RealInnerProductSpace

-- The total square-root convention gives the same continuous extension; no cone is averaged.
theorem total_principal_root (a t : ℝ) :
    Real.sqrt (t/Real.sqrt (t/(2*a)))=
      Real.sqrt (Real.sqrt (2*max a 0*max t 0)) := by
  by_cases positiveT : 0<t
  · by_cases positiveA : 0<a
    · rw [max_eq_left positiveA.le,max_eq_left positiveT.le]
      have ratioPos : 0<t/(2*a) := div_pos positiveT (by positivity)
      have clockPos : 0<Real.sqrt (t/(2*a)) := Real.sqrt_pos.mpr ratioPos
      have square : (t/Real.sqrt (t/(2*a)))^2=2*a*t := by
        rw [div_pow,Real.sq_sqrt ratioPos.le]
        field_simp
      have same : t/Real.sqrt (t/(2*a))=Real.sqrt (2*a*t) := by
        rw [←square,Real.sqrt_sq (div_nonneg positiveT.le clockPos.le)]
      rw [same]
    · have nonpositiveA : a≤0 := le_of_not_gt positiveA
      have ratioNonpositive : t/(2*a)≤0 :=
        div_nonpos_of_nonneg_of_nonpos positiveT.le (by linarith)
      rw [Real.sqrt_eq_zero_of_nonpos ratioNonpositive,div_zero,Real.sqrt_zero,
        max_eq_right nonpositiveA]
      simp
  · have nonpositiveT : t≤0 := le_of_not_gt positiveT
    rw [Real.sqrt_eq_zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg nonpositiveT (Real.sqrt_nonneg _)),
      max_eq_right nonpositiveT]
    simp

theorem principalFactor_total (z : SourceCoordinateSlice) (p : Cotangent) :
    principalFactor z p=Real.sqrt (Real.sqrt (2*max (A z p) 0*max (T z p) 0)) :=
  total_principal_root _ _

theorem principalFactor_continuous_at (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈GaussHistoryHilbert.physicalChart) :
    ContinuousAt (fun q : SourceCoordinateSlice × Cotangent => principalFactor q.1 q.2) zp := by
  have same : (fun q : SourceCoordinateSlice × Cotangent => principalFactor q.1 q.2)=
      fun q => Real.sqrt (Real.sqrt (2*max (A q.1 q.2) 0*max (T q.1 q.2) 0)) :=
    funext (fun q => principalFactor_total q.1 q.2)
  rw [same]
  exact ((continuousAt_const.mul
    ((A_smooth zp physical).continuousAt.max continuousAt_const)).mul
      ((T_smooth zp physical).continuousAt.max continuousAt_const)).sqrt.sqrt

theorem theta_position_physical {z : FlatConfiguration} (box : z∈thetaPositionClosed) :
    PreparationScalarCoordinates.fullCoordinates.symm z∈GaussHistoryHilbert.physicalChart := by
  apply actual_source_chart_guard z
  intro i
  exact (box i).trans (by linarith [radius_small.1])

theorem b1_continuous : Continuous b1 := by
  rw [continuous_iff_continuousAt]
  intro zp
  by_cases inside : zp.1∈thetaPositionClosed
  · exact factorWeight_smooth.continuous.continuousAt.mul
      ((principalFactor_continuous_at (nativePhase zp) (theta_position_physical inside)).comp
        nativePhase_smooth.continuous.continuousAt)
  · have nearby : ∀ᶠ q : FlatConfiguration × PhysicalMomentum in 𝓝 zp,
        q.1∉thetaPositionClosed :=
      (thetaPositionClosed_closed.isOpen_compl.preimage continuous_fst).mem_nhds inside
    have zero : b1 =ᶠ[𝓝 zp] (fun _ => (0 : ℝ)) := by
      filter_upwards [nearby] with q outside
      simp only [b1,factorWeight,sourceThetaRoot_split,positionRoot_zero_outside outside,
        zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq zero

def angularCompact : Set (FlatConfiguration × PhysicalMomentum) :=
  thetaPositionClosed ×ˢ Metric.closedBall 0 1

def angularPrincipal (zp : FlatConfiguration × PhysicalMomentum) : ℝ :=
  principalFactor (nativePhase zp).1 (nativePhase zp).2

theorem angularCompact_compact : IsCompact angularCompact :=
  thetaPositionClosed_compact.prod (isCompact_closedBall _ _)

theorem angularPrincipal_continuous : ContinuousOn angularPrincipal angularCompact := by
  intro zp hz
  exact ((principalFactor_continuous_at (nativePhase zp) (theta_position_physical hz.1)).comp
    nativePhase_smooth.continuous.continuousAt).continuousWithinAt

theorem source_angular_bound_exists :
    ∃ bound : ℝ, 0≤ bound ∧ ∀ zp∈angularCompact, |angularPrincipal zp|≤ bound := by
  obtain ⟨bound,hbound⟩ :=
    angularCompact_compact.bddAbove_image angularPrincipal_continuous.abs
  refine ⟨max bound 0,le_max_right _ _,?_⟩
  intro zp hz
  exact (hbound (mem_image_of_mem _ hz)).trans (le_max_left _ _)

-- Generated from the complete native angular carrier; it is never a caller's normalization input.
def sourceOrderOneBound : ℝ := Classical.choose source_angular_bound_exists

theorem sourceOrderOneBound_nonnegative : 0≤ sourceOrderOneBound :=
  (Classical.choose_spec source_angular_bound_exists).1

theorem sourceOrderOneBound_bounds (zp : FlatConfiguration × PhysicalMomentum)
    (inside : zp∈angularCompact) : |angularPrincipal zp|≤ sourceOrderOneBound :=
  (Classical.choose_spec source_angular_bound_exists).2 zp inside

theorem b1_nonnegative (zp : FlatConfiguration × PhysicalMomentum) : 0≤b1 zp :=
  mul_nonneg (factorWeight_nonnegative zp) (Real.sqrt_nonneg _)

theorem b1_order_one (zp : FlatConfiguration × PhysicalMomentum) :
    ‖b1 zp‖≤ sourceOrderOneBound*‖zp.2‖ := by
  by_cases zero : zp.2=0
  · rw [b1_zero_low zp (by rw [zero]; norm_num),norm_zero,zero,norm_zero,mul_zero]
  by_cases position : zp.1∈thetaPositionClosed
  · let u : PhysicalMomentum := ‖zp.2‖⁻¹ • zp.2
    have normp : 0<‖zp.2‖ := norm_pos_iff.mpr zero
    have unit : ‖u‖=1 := by
      rw [show u=‖zp.2‖⁻¹ • zp.2 from rfl,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr normp),inv_mul_cancel₀ normp.ne']
    have inside : (zp.1,u)∈angularCompact :=
      ⟨position,by simp only [Metric.mem_closedBall,dist_zero_right,unit,le_refl]⟩
    have amplitude : principalFactor (fullCoordinates.symm zp.1) (nativeCovector u)
        ≤ sourceOrderOneBound :=
      (le_abs_self _).trans (sourceOrderOneBound_bounds (zp.1,u) inside)
    rw [Real.norm_eq_abs,abs_of_nonneg (b1_nonnegative zp),b1_radial_readback zp zero]
    calc
      _ ≤ ‖zp.2‖*sourceOrderOneBound := by
        apply mul_le_mul _ amplitude (Real.sqrt_nonneg _) (norm_nonneg _)
        simpa using mul_le_mul_of_nonneg_right (factorWeight_le_one zp) (norm_nonneg zp.2)
      _ = sourceOrderOneBound*‖zp.2‖ := mul_comm _ _
  · have bzero : b1 zp=0 := by
      simp only [b1,factorWeight,sourceThetaRoot_split,positionRoot_zero_outside position,zero_mul]
    rw [bzero,norm_zero]
    exact mul_nonneg sourceOrderOneBound_nonnegative (norm_nonneg _)

def flatPosition : PhysicalMomentum ≃L[ℝ] FlatConfiguration :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 100 => ℝ)

def symbolSlice (p : PhysicalMomentum) (x : PhysicalMomentum) : ℂ :=
  (b1 (flatPosition x,p) : ℂ)

theorem symbolSlice_continuous (p : PhysicalMomentum) : Continuous (symbolSlice p) :=
  Complex.continuous_ofReal.comp
    (b1_continuous.comp (flatPosition.continuous.prodMk continuous_const))

theorem symbolSlice_compact (p : PhysicalMomentum) : HasCompactSupport (symbolSlice p) := by
  have realSupport : HasCompactSupport (fun x : PhysicalMomentum => b1 (flatPosition x,p)) :=
    (b1_position_compact p).comp_homeomorph flatPosition.toHomeomorph
  exact realSupport.comp_left (by norm_num : (Complex.ofReal : ℝ→ℂ) 0=0)

theorem symbolSlice_integrable (p : PhysicalMomentum) : Integrable (symbolSlice p) :=
  (symbolSlice_continuous p).integrable_of_hasCompactSupport (symbolSlice_compact p)

theorem raw100_volume : (volume : Measure FlatConfiguration)=flatMeasure :=
  MeasureTheory.volume_pi

theorem actual_flatPosition_measure : MeasurePreserving flatPosition volume flatMeasure := by
  rw [←raw100_volume]
  exact PiLp.volume_preserving_ofLp (Fin 100)

theorem symbolSlice_integral_raw (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum, symbolSlice p x)=
      ∫ z : FlatConfiguration, (b1 (z,p) : ℂ) ∂flatMeasure := by
  exact actual_flatPosition_measure.integral_comp flatPosition.toHomeomorph.measurableEmbedding
    (fun z : FlatConfiguration => (b1 (z,p) : ℂ))

end LowEnergy.PreparationVacuumWeyl
