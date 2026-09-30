import H0mework.NavierStokes.WindowStressHeat.OseenSource
import H0mework.NavierStokes.WindowEnergyHighTransport.Relative
import H0mework.NavierStokes.WindowSourceGreen.FormTest

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedGreen
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativePhysicalFourier NativeFiniteActionResolvent NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowOperatorGreen NativeWindowStressOseenTest NativeWindowHighTransportRelative
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def correctionForm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes F : Finset IntegerWavevector) (radius : ℕ) :
    physicalSpace modes →ₗ[ℝ] physicalSpace modes →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ output : Coordinate,∑ input : Coordinate,
    inner ℝ (primitiveField seed F radius 0 time output input)
      (NativeWindowStressHeatSource.physical (evaluate modes F output x*evaluate modes F input y)))
    (fun _ _ _ => by simp only [map_add,add_mul,inner_add_right,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,smul_mul_assoc,real_inner_smul_right,smul_eq_mul,Finset.mul_sum])
    (fun _ _ _ => by simp only [map_add,mul_add,inner_add_right,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,real_inner_smul_right,smul_eq_mul,Finset.mul_sum])

def correction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes F : Finset IntegerWavevector) (radius : ℕ) : Module.End ℝ (physicalSpace modes) :=
  (duality modes).symm.toLinearMap.comp (correctionForm seed time modes F radius).flip

theorem correction_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace modes) :
    pairing modes x (correction seed time modes F radius y)=correctionForm seed time modes F radius x y := by
  have original := congrArg (fun functional : Module.Dual ℝ (physicalSpace modes) => functional x)
    ((duality modes).apply_symm_apply ((correctionForm seed time modes F radius).flip y))
  change pairing modes (correction seed time modes F radius y) x=_ at original
  rw [pairing_symmetric] at original
  exact original

def matrixTest (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes F : Finset IntegerWavevector) (radius : ℕ) : Module.End ℝ (physicalSpace modes) :=
  NativeWindowStressOseenTest.operator seed time modes F+correction seed time modes F radius

def test (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (zero : 0∉modes) (closed : FiniteModeNegClosed modes) (radius : ℕ) : Module.End ℝ (physicalSpace modes) :=
  LinearMap.id+nu.coeff • laplacian modes zero closed nu+matrixTest seed time modes F radius

theorem test_diagonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (zero : 0∉modes) (closed : FiniteModeNegClosed modes) (radius : ℕ) (value : physicalSpace modes) :
    pairing modes value (test seed time modes F zero closed radius value)=
      pairing modes value value+nu.coeff*curlPair modes value.1 value.1+
        form seed time modes F value value+correctionForm seed time modes F radius value value := by
  simp only [test,matrixTest,LinearMap.add_apply,LinearMap.id_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_eq_mul,laplacian_pairing,NativeWindowStressOseenTest.operator_pairing,correction_pairing]
  ring

theorem laplacian_adjoint (modes : Finset IntegerWavevector) (zero : 0∉modes)
    (closed : FiniteModeNegClosed modes) (x y : physicalSpace modes) :
    pairing modes (laplacian modes zero closed nu x) y=pairing modes x (laplacian modes zero closed nu y) := by
  simp only [laplacian,LinearMap.smul_apply,map_smul,smul_eq_mul]
  rw [dissipative_adjoint]

theorem lyapunov_augmented (modes : Finset IntegerWavevector) (zero : 0∉modes)
    (closed : FiniteModeNegClosed modes) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (T : Module.End ℝ (physicalSpace modes)) :
    let L:=laplacian modes zero closed nu
    let K:=convection modes zero closed nu advector reality
    lyapunov modes zero closed nu advector reality (LinearMap.id+nu.coeff • L+T)=
      (-2*nu.coeff) • L+(-2*nu.coeff^2) • L.comp L+
        nu.coeff • (L.comp K-K.comp L)+lyapunov modes zero closed nu advector reality T := by
  dsimp only
  apply LinearMap.ext
  intro value
  simp only [lyapunov,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
    LinearMap.comp_apply,map_add,map_smul]
  module

theorem actual_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes F : Finset IntegerWavevector) (zero : 0∉modes) (closed : FiniteModeNegClosed modes)
    (radius : ℕ) (advector : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality advector)
    (value : physicalSpace modes) :
    let L:=laplacian modes zero closed nu
    let K:=convection modes zero closed nu advector reality
    let A:=physicalOperator modes zero closed nu advector reality
    let B:=test seed time modes F zero closed radius
    pairing modes (A value) (B value)+pairing modes value (B (A value))=
      -2*nu.coeff*curlPair modes value.1 value.1-2*nu.coeff^2*pairing modes (L value) (L value)+
        nu.coeff*pairing modes value (L (K value)-K (L value))+
        pairing modes value (lyapunov modes zero closed nu advector reality (matrixTest seed time modes F radius) value) := by
  dsimp only
  rw [whole_green,test,lyapunov_augmented]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    map_add,map_smul,smul_eq_mul]
  have palin := laplacian_adjoint (nu := nu) modes zero closed value (laplacian modes zero closed nu value)
  rw [← palin,laplacian_pairing modes zero closed nu value value]
  ring

theorem source_green (seed : GeneratedWholeRestartCurrent nu) (observation sample : ℝ)
    (innerRadius radius : ℕ) (F : Finset IntegerWavevector) :
    let modes:=NativeWholeH1Mixed.modes innerRadius
    let zero:=NativeWholeH1Mixed.modes_zero innerRadius
    let closed:=NativeWholeH1Mixed.modes_closed innerRadius
    let U:=NativeWindowStressOseenSource.load innerRadius seed sample
    let L:=laplacian modes zero closed nu
    let K:=NativeWindowStressOseenSource.K innerRadius seed sample
    let A:=physicalOperator modes zero closed nu (NativeWindowStressOseenSource.advector innerRadius seed sample)
      (NativeWindowStressOseenSource.advector_reality innerRadius seed sample)
    let B:=test seed observation modes F zero closed radius
    pairing modes (A U) (B U)+pairing modes U (B (A U))=
      -2*nu.coeff*curlPair modes U.1 U.1-2*nu.coeff^2*pairing modes (L U) (L U)+
        nu.coeff*pairing modes U (L (K U)-K (L U))+
        pairing modes U (lyapunov modes zero closed nu (NativeWindowStressOseenSource.advector innerRadius seed sample)
          (NativeWindowStressOseenSource.advector_reality innerRadius seed sample) (matrixTest seed observation modes F radius) U) :=
  actual_green seed observation _ F _ _ radius _ _ _

theorem graph_commutator (modes : Finset IntegerWavevector) (zero : 0∉modes)
    (closed : FiniteModeNegClosed modes) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (value : physicalSpace modes) :
    let L:=laplacian modes zero closed nu
    let K:=convection modes zero closed nu advector reality
    pairing modes value (L (K value)-K (L value))=2*pairing modes (L value) (K value) := by
  dsimp only
  rw [map_sub,← laplacian_adjoint]
  have skew := convection_skew modes zero closed nu advector reality value (laplacian modes zero closed nu value)
  rw [pairing_symmetric modes (convection modes zero closed nu advector reality value)] at skew
  linarith only [skew]

def matrixField (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time F output input)+
    primitiveField seed F radius 0 time output input

theorem matrix_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace modes) :
    pairing modes x (matrixTest seed time modes F radius y)=∑ output : Coordinate,∑ input : Coordinate,
      inner ℝ (matrixField seed time F radius output input)
        (NativeWindowStressHeatSource.physical (evaluate modes F output x*evaluate modes F input y)) := by
  simp only [matrixTest,LinearMap.add_apply,map_add,NativeWindowStressOseenTest.operator_pairing,
    correction_pairing,NativeWindowStressOseenTest.form_apply,correctionForm,LinearMap.mk₂_apply,
    matrixField,inner_add_left,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [mean_apply,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  simp only [ContinuousMap.mul_apply]
  ring

theorem matrix_average (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (innerRadius radius order : ℕ) (F : Finset IntegerWavevector)
    (cover : ∀ wave∈F,wave≠0 →wave∈NativeWholeH1Mixed.modes innerRadius) :
    (∫ sample in observation+1..observation+2,NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample*
      pairing (NativeWholeH1Mixed.modes innerRadius) (NativeWindowStressOseenSource.load innerRadius seed sample)
        (matrixTest seed observation (NativeWholeH1Mixed.modes innerRadius) F radius
          (NativeWindowStressOseenSource.load innerRadius seed sample)))=
    ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (matrixField seed observation F radius output input)
      (NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet seed F output input order observation)) := by
  let observed (output input : Coordinate) : C(Torus,ℝ) →L[ℝ] ℝ :=
    (innerSL ℝ (matrixField seed observation F radius output input)).comp NativeWindowStressHeatSource.physical
  have paid (output input : Coordinate) :=
    ((NativeWindowStressHeatTime.product_ac seed F output input (observation+1) (observation+2)
      (by linarith) (by linarith)).continuousOn.intervalIntegrable (μ := volume)).continuousOn_smul
        (NativeUnheatedStressPairEvolution.kernelWeight_continuous order observation 0).continuousOn
  have row (output input : Coordinate) := (observed output input).intervalIntegral_comp_comm (paid output input)
  have integrated (output input : Coordinate) : IntervalIntegrable (fun sample => observed output input
      (NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample • NativeWindowStressHeatTime.product seed F output input sample))
      volume (observation+1) (observation+2) :=
    ⟨(observed output input).integrable_comp (paid output input).1,(observed output input).integrable_comp (paid output input).2⟩
  have actual : (∫ sample in observation+1..observation+2,NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample*
      pairing (NativeWholeH1Mixed.modes innerRadius) (NativeWindowStressOseenSource.load innerRadius seed sample)
        (matrixTest seed observation (NativeWholeH1Mixed.modes innerRadius) F radius
          (NativeWindowStressOseenSource.load innerRadius seed sample)))=
      ∫ sample in observation+1..observation+2,∑ output : Coordinate,∑ input : Coordinate,
        observed output input (NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample •
          NativeWindowStressHeatTime.product seed F output input sample) := by
    apply intervalIntegral.integral_congr
    intro sample inside
    have sample0 : 0 ≤ sample := by rw [Set.uIcc_of_le (by linarith : observation+1 ≤ observation+2)] at inside; linarith [inside.1]
    simp only [matrix_pairing,NativeWindowStressOseenSource.evaluate_load innerRadius seed sample sample0 F cover,
      Finset.mul_sum,map_smul,smul_eq_mul,observed,ContinuousLinearMap.comp_apply,NativeWindowStressHeatTime.product]
    rfl
  rw [actual,intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun output sample => ∑ input : Coordinate,observed output input
      (NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample • NativeWindowStressHeatTime.product seed F output input sample))
    (fun output _ => by simpa only [Finset.sum_apply] using! IntervalIntegrable.sum Finset.univ (fun input _ => integrated output input))]
  apply Finset.sum_congr rfl
  intro output _
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun input _ => integrated output input)]
  apply Finset.sum_congr rfl
  intro input _
  rw [row output input,← NativeWindowStressHeatTime.kernel_integral]
  rfl

section FullMatrixForm
open NativeWindowGreenTestForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
theorem fractional_norm (T : Test H) : ‖fractional T‖≤‖T‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
  intro k
  change ‖NativeCompleteStressCarrier.weight k^(1/16 : ℝ)*‖T k‖‖≤‖T k‖
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (NativeCompleteStressCarrier.weight_pos k).le _) (norm_nonneg _))]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one (NativeCompleteStressCarrier.weight_pos k).le
    (NativeWindowGreenTestForm.weight_le_one k) (by norm_num))

def correctionFourierForm (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius order : ℕ) (time : ℝ) (A : Coordinate → Coordinate → H →L[ℂ] H) (T : Test H) : ℂ :=
  ∑ output : Coordinate,∑ input : Coordinate,NativeWindowGreenTestForm.form
    (NativeWindowHighTransportResolvent.primitive seed F radius order time output input) (A output input) T

theorem correction_uniform_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (horizon : ℝ) (nonnegative : 0≤horizon) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Set.Icc 0 horizon →
      ∀ (A : Coordinate → Coordinate → H →L[ℂ] H), (∀ output input,‖A output input‖≤1) →∀ T : Test H,
        ‖correctionFourierForm seed F radius order time A T‖≤epsilon*(gradient T+‖decode T‖^2) := by
  let q:=1+Real.sqrt testKernel.cap
  have qpos : 0<q := by dsimp [q]; positivity
  obtain ⟨low,paid⟩ := NativeWindowHighTransportResolvent.primitive_small seed order horizon nonnegative
    (epsilon/(9*q)) (by positivity)
  refine ⟨low,fun radius above F time inside A operatorBound T => ?_⟩
  have row (output input : Coordinate) : ‖NativeWindowGreenTestForm.form
      (NativeWindowHighTransportResolvent.primitive seed F radius order time output input) (A output input) T‖≤
        epsilon/9*(gradient T+‖decode T‖^2) := by
    have factor : ‖A output input‖*Real.sqrt testKernel.cap*
        ‖NativeWindowHighTransportResolvent.primitive seed F radius order time output input‖≤epsilon/9 := by
      have first : ‖A output input‖*Real.sqrt testKernel.cap≤q :=
        (mul_le_of_le_one_left (Real.sqrt_nonneg _) (operatorBound output input)).trans (by dsimp [q]; linarith)
      exact (mul_le_mul first (paid radius above F time inside output input).le (norm_nonneg _) qpos.le).trans_eq (by field_simp)
    have testBound : ‖fractional T‖^2≤gradient T+‖decode T‖^2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (fractional_norm T) 2).trans (high_le_gradient_mass T)
    exact (form_bound _ _ T).trans (mul_le_mul factor testBound (sq_nonneg _) (by positivity))
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun output _ => norm_sum_le _ _)).trans
  exact (Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)

end FullMatrixForm

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedGreen
