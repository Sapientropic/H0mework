import H0mework.NavierStokes.WindowEnergyTraceTerminal.Cubic
import H0mework.NavierStokes.WindowEnergyAugmented.GradientSource
import H0mework.NavierStokes.WindowEnergyTrace.HalfKernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalSynthesis
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint NativeWindowOperatorGreen
open NativePhysicalFourier NativeWindowStressOseenTest NativeWindowStressHeatEnergy
open NativeWindowStressHeatSource (physical)
open NativeCompleteStressCarrier (weight weight_pos weight_summable)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def cap : ℝ := 1+Real.sqrt (∑' k,weight k^2)

theorem cap_positive : 0<cap := by unfold cap; positivity

theorem coordinate_square_bound (M F : Finset IntegerWavevector) (v : physicalSpace M) (i : Coordinate) :
    (∑ k∈F,‖v.1 k i‖^2)≤‖coefficients M v‖^2 := by
  have mass : ‖coefficients M v‖^2=∑ k∈M,complexCoordinateVectorNormSq (v.1 k) := by
    rw [← real_inner_self_eq_norm_sq]
    change pairing M v v=_
    rw [pairing_eq]
    simp only [complexCoordinateRealInner_self]
  have outside (k : IntegerWavevector) (absent : k∉M) : complexCoordinateVectorNormSq (v.1 k)=0 := by
    rw [physical_supported v k absent]
    simp [complexCoordinateVectorNormSq]
  have paid : Summable (fun k : IntegerWavevector => complexCoordinateVectorNormSq (v.1 k)) := summable_of_ne_finset_zero outside
  rw [mass]
  apply (Finset.sum_le_sum (s := F) (fun k _ => show ‖v.1 k i‖^2≤complexCoordinateVectorNormSq (v.1 k) by
    rw [Complex.sq_norm]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))).trans
  exact (paid.sum_le_tsum F (fun k _ => complexCoordinateVectorNormSq_nonneg _)).trans_eq (tsum_eq_sum outside)

theorem basis_bound (k : IntegerWavevector) (z : ℂ) : ‖NativeWindowStressHeatBalance.basis k z‖≤‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).2
  intro point
  change ‖(z*UnitAddTorus.mFourier k point).re‖≤‖z‖
  rw [Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((UnitAddTorus.mFourier k).norm_coe_le_norm point |>.trans_eq UnitAddTorus.mFourier_norm)

theorem evaluate_bound (nu : Viscosity) (M F : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (v : physicalSpace M) (i : Coordinate) : ‖evaluate M F i v‖≤cap*‖coefficients M (laplacian M zero closed nu v)‖ := by
  let L:=laplacian M zero closed nu v
  have row (k : IntegerWavevector) : ‖v.1 k i‖≤weight k*‖L.1 k i‖ := by
    by_cases nonzero : k=0
    · subst k
      rw [physical_supported v 0 zero,Pi.zero_apply,norm_zero]
      positivity [weight_pos 0]
    · have native : (weight k)*integerWaveViscousMultiplier k=(2*Real.pi)^2 := by
        rw [weight,if_neg nonzero,integerWaveViscousMultiplier]
        field_simp [(integerWaveNormSq_pos nonzero).ne']
      change _≤weight k*‖(laplacian M zero closed nu v).1 k i‖
      rw [laplacian_row]
      change _≤weight k*‖(integerWaveViscousMultiplier k : ℝ) • v.1 k i‖
      rw [norm_smul,Real.norm_of_nonneg (integerWaveViscousMultiplier_pos ⟨k,nonzero⟩).le,← mul_assoc,native]
      apply le_mul_of_one_le_left (norm_nonneg _)
      nlinarith [Real.pi_gt_three,sq_nonneg (2*Real.pi-1)]
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq F weight (fun k => ‖L.1 k i‖)
  have bounded := cauchy.trans (mul_le_mul (weight_summable.sum_le_tsum F (fun k _ => sq_nonneg _))
    (coordinate_square_bound M F L i) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (tsum_nonneg fun _ => sq_nonneg _))
  have normed : (∑ k∈F,weight k*‖L.1 k i‖)≤Real.sqrt (∑' k,weight k^2)*‖coefficients M L‖ := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun k _ => mul_nonneg (weight_pos k).le (norm_nonneg _)) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]
    exact bounded
  rw [evaluate_apply]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun k _ => (basis_bound k _).trans (row k)).trans
  exact normed.trans (mul_le_mul_of_nonneg_right (by unfold cap; linarith) (norm_nonneg _))

theorem evaluate_physical (M F : Finset IntegerWavevector) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (v : physicalSpace M) (i : Coordinate) : physical (evaluate M F i v)=field (finiteSequence F (fun k => v.1 k i)) := by
  have reality (k : IntegerWavevector) : v.1 (waveNeg k) i=conj (v.1 k i) :=
    congrFun (physical_reality (fun {_} inside => closedM _ inside) v k) i
  change ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (evaluate M F i v)).toLp 2 volume ℂ=_
  have same : evaluate M F i v=NativeWindowHighPressurePhysical.realSynthesis F (fun k => v.1 k i) := by
    rw [evaluate_apply]
    rfl
  rw [same,NativeWindowHighPressurePhysical.realSynthesis_complex F closedF _ reality]
  have native := NativeWindowStressHeatSource.polynomial_field F (fun k => v.1 k i) 0 0
  simpa only [finiteJet,pow_zero,one_mul] using native

theorem evaluate_physical_bound (M F : Finset IntegerWavevector) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (v : physicalSpace M) (i : Coordinate) : ‖physical (evaluate M F i v)‖≤‖coefficients M v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [evaluate_physical M F closedM closedF,NativeWindowTraceHalfKernel.scalar_norm_square]
  exact coordinate_square_bound M F v i

theorem physical_square (f : C(Torus,ℝ)) : ‖physical f‖^2=∫ point : Torus,(f point)^2 := by
  rw [← real_inner_self_eq_norm_sq,NativeWindowStressHeatSource.physical_inner]
  simp only [pow_two]

theorem product_bound (f g : C(Torus,ℝ)) : ‖physical (f*g)‖≤‖f‖*‖physical g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,physical_square,physical_square,← integral_const_mul]
  have paid : Integrable (fun point : Torus => (g point)^2) (volume : Measure Torus) := by
    simpa only [IntegrableOn,Measure.restrict_univ,Pi.pow_apply] using!
      ((g.continuous.pow 2).continuousOn.integrableOn_compact (μ := (volume : Measure Torus)) isCompact_univ)
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) (paid.const_mul (‖f‖^2))
  filter_upwards with point
  simp only [ContinuousMap.mul_apply,mul_pow]
  have bound := pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm point) 2
  rw [Real.norm_eq_abs,sq_abs] at bound
  exact mul_le_mul_of_nonneg_right bound (sq_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalSynthesis
