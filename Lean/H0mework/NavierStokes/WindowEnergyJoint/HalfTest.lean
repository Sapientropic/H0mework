import H0mework.NavierStokes.WindowEnergyJoint.EnergyGate

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowJointHalfTest
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativePhysicalGradient (multiplier multiplier_sum_norm_sq)
open NativeUnheatedSexticLatticePower (radical density)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem finite_norm_square {E : Type*} [NormedAddCommGroup E] (F : Finset IntegerWavevector) (a : IntegerWavevector → E) :
    ‖∑ k ∈ F,lp.single (2 : ℝ≥0∞) k (a k)‖^2=∑ k ∈ F,‖a k‖^2 := by
  have read (k : IntegerWavevector) : (∑ p ∈ F,lp.single (2 : ℝ≥0∞) p (a p)) k=if k∈F then a k else 0 := by
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  have normed := lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal) (∑ k ∈ F,lp.single (2 : ℝ≥0∞) k (a k))
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at normed
  rw [normed]
  rw [tsum_eq_sum (s := F) (fun k outside => by rw [read,if_neg outside,norm_zero,zero_pow (by decide : 2≠0)])]
  exact Finset.sum_congr rfl fun k member => by rw [read,if_pos member]

private theorem scalar_norm_square (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) :
    ‖field (finiteSequence F a)‖^2=∑ k ∈ F,‖a k‖^2 := by
  rw [field,LinearIsometryEquiv.norm_map]
  exact finite_norm_square F a

def test (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    NativeCompleteStressCarrier.Space :=
  -(∑ k ∈ NativeWindowJointHeat.frequencies F,lp.single 2 k
    (radical k • NativeCompleteStressCarrier.tensor (NativeWindowJointHeat.coefficients seed F radius time k)))

theorem test_apply (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (k : IntegerWavevector) (output input : Coordinate) :
    test seed F radius time k (output,input)=if k∈NativeWindowJointHeat.frequencies F then
      -(radical k:ℂ)*NativeWindowJointHeat.coefficients seed F radius time k output input else 0 := by
  simp only [test,lp.coeFn_neg,Pi.neg_apply,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs <;> simp [NativeCompleteStressCarrier.tensor,PiLp.smul_apply,Complex.real_smul]

theorem test_read (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    (UnitAddTorus.mFourierBasis (d := Coordinate)).repr
      (NativeWindowPressureStrainHistory.relative seed F radius time output input) k=
        (density 1 k:ℂ)*NativeWindowPressureLowSource.component (test seed F radius time) output input k := by
  rw [NativeWindowJointHeat.relative_original seed F radius time closed output input,map_neg]
  simp only [field,LinearIsometryEquiv.apply_symm_apply,lp.coeFn_neg,Pi.neg_apply]
  change -(finiteSequence (NativeWindowJointHeat.frequencies F)
    (fun wave => NativeWindowJointHeat.coefficients seed F radius time wave output input) k)=_
  change _=(density 1 k:ℂ)*test seed F radius time k (output,input)
  rw [test_apply,finiteSequence_apply]
  split_ifs
  · simp only [density,pow_one,Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr (NativeUnheatedSexticLatticePower.radical_positive k).ne']
  · simp

private theorem radical_energy (k : IntegerWavevector) : radical k^2≤1+integerWaveViscousMultiplier k := by
  rw [NativeUnheatedSexticLatticePower.radical_square]
  have mass : 1≤NativeUnheatedSexticLatticePower.mass k := NativeUnheatedSexticLatticePower.mass_one k
  have root : Real.sqrt (NativeUnheatedSexticLatticePower.mass k)≤NativeUnheatedSexticLatticePower.mass k := by
    have square := Real.sq_sqrt (by linarith : 0≤NativeUnheatedSexticLatticePower.mass k)
    have nonnegative := Real.sqrt_nonneg (NativeUnheatedSexticLatticePower.mass k)
    nlinarith only [square,nonnegative,mass]
  have spatial := integerWaveNormSq_nonneg k
  have pi := Real.pi_gt_three
  unfold NativeUnheatedSexticLatticePower.mass integerWaveViscousMultiplier at *
  have scale : 1≤(2*Real.pi)^2 := by nlinarith only [pi,sq_nonneg (2*Real.pi-1)]
  nlinarith only [root,mul_nonneg (sub_nonneg.mpr scale) spatial]

private theorem sum_output (G : Finset IntegerWavevector) (f : Coordinate → Coordinate → IntegerWavevector → ℝ) :
    (∑ output : Coordinate,∑ input : Coordinate,∑ k ∈ G,f output input k)=
      ∑ k ∈ G,∑ output : Coordinate,∑ input : Coordinate,f output input k := by
  calc
    _ = ∑ output : Coordinate,∑ k ∈ G,∑ input : Coordinate,f output input k :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem test_norm_square (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) :
    ‖test seed F radius time‖^2≤2*NativeWindowJointNormalForm.energy seed F radius time+
      NativeWindowJointHeat.dirichlet seed F radius time := by
  rw [test,norm_neg,finite_norm_square]
  simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,NativeCompleteStressCarrier.tensor_norm_sq]
  have row (k : IntegerWavevector) : radical k^2*(∑ output : Coordinate,∑ input : Coordinate,
      ‖NativeWindowJointHeat.coefficients seed F radius time k output input‖^2)≤
        (1+integerWaveViscousMultiplier k)*(∑ output : Coordinate,∑ input : Coordinate,
          ‖NativeWindowJointHeat.coefficients seed F radius time k output input‖^2) :=
    mul_le_mul_of_nonneg_right (radical_energy k) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply (Finset.sum_le_sum fun k _ => row k).trans_eq
  simp only [NativeWindowJointNormalForm.energy,NativeWindowJointHeat.relative_original seed F radius time closed,
    norm_neg,NativeWindowJointHeat.dirichlet,scalar_norm_square,finiteJet,scalar_norm_square]
  simp only [pow_one,norm_mul,mul_pow,Finset.mul_sum]
  have gradient (a : IntegerWavevector → Coordinate → Coordinate → ℂ) (G : Finset IntegerWavevector) :
      (∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,∑ k ∈ G,
        ‖multiplier k j‖^2*‖a k output input‖^2)=
          ∑ k ∈ G,∑ output : Coordinate,∑ input : Coordinate,integerWaveViscousMultiplier k*‖a k output input‖^2 := by
    simp_rw [sum_output]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,← Finset.sum_mul,multiplier_sum_norm_sq,integerWaveViscousMultiplier]
  rw [gradient]
  rw [sum_output]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem test_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    test seed F radius (step.2.clockAdvance+time)=test step.1 F radius time := by
  apply lp.ext
  funext k
  apply PiLp.ext
  rintro ⟨output,input⟩
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (NativeUnheatedSexticLatticePower.density_positive 1 k).ne')
  change (density 1 k:ℂ)*NativeWindowPressureLowSource.component (test seed F radius (step.2.clockAdvance+time)) output input k=
    (density 1 k:ℂ)*NativeWindowPressureLowSource.component (test step.1 F radius time) output input k
  rw [← test_read seed F closed radius (step.2.clockAdvance+time),
    NativeWindowPressureStrainHistory.relative_next seed step generated radius time nonnegative F,
    test_read step.1 F closed radius time]

end
end SaturationMonoid.NavierStokes.NativeWindowJointHalfTest
