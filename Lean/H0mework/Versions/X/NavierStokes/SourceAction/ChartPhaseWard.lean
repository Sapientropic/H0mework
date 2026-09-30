import H0mework.Versions.X.NavierStokes.SourceAction.ChartPhysicalAction
import H0mework.Versions.X.NavierStokes.PhysicalReadout.CanonicalCoframe

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeTimeChartPhaseWard

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFullOrderSynthesis NativeFullOrderAction NativeMixedTimeSpace NativeReceiptTimeProfile
open NativeFinitePrefixTimeChart NativeCanonicalFluidCoframe

noncomputable section

def divergenceRead :
    ContinuousMultilinearMap ℝ (fun _ : Fin 1 => PhysicalSpace) PhysicalSpace →L[ℝ] ℝ :=
  ∑ direction : Coordinate, (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) direction).comp
    (evaluateJet 1 (fun _ => EuclideanSpace.single direction 1))

theorem divergenceRead_apply
    (jet : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => PhysicalSpace) PhysicalSpace) :
    divergenceRead jet = ∑ direction : Coordinate, (jet (fun _ => EuclideanSpace.single direction 1)) direction := by
  simp only [divergenceRead, sum_apply, ContinuousLinearMap.comp_apply,
    evaluateJet, LinearMap.mkContinuous_apply, PiLp.proj_apply]
  rfl

theorem phase_single (wave : IntegerWavevector) (direction : Coordinate) :
    phase wave (EuclideanSpace.single direction 1) = 2 * Real.pi * (wave direction : ℝ) := by
  rw [phase_apply]
  simp

theorem mode_divergence_zero (velocity : ComplexVorticityHilbertState) (transverse : WholeStateTransverse velocity)
    (wave : IntegerWavevector) (point : PhysicalSpace) :
    divergenceRead (iteratedFDeriv ℝ 1 (mode velocity wave) point) = 0 := by
  rw [divergenceRead_apply]
  simp_rw [mode_word_eq]
  simp only [Fin.prod_univ_one, pow_one, phase_single]
  change (∑ direction : Coordinate, (velocity wave direction *
    ((2 * Real.pi * (wave direction : ℝ)) • (Complex.I * UnitAddTorus.mFourier wave (circlePoint point)))).re) = 0
  have combined : (∑ direction : Coordinate, velocity wave direction *
      ((2 * Real.pi * (wave direction : ℝ)) • (Complex.I * UnitAddTorus.mFourier wave (circlePoint point)))) = 0 := by
    calc
      _ = (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * UnitAddTorus.mFourier wave (circlePoint point))) *
          (complexWavevector wave ⬝ᵥ velocity wave) := by
        rw [dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro direction _
        simp only [Complex.real_smul, Complex.ofReal_mul, complexWavevector]
        ring
      _ = 0 := by rw [transverse wave, mul_zero]
  simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re combined

theorem spatial_divergence_of_transverse (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * amplitude velocity wave)
    (transverse : WholeStateTransverse velocity) (point : PhysicalSpace) :
    (∑ direction : Coordinate,
      (fderiv ℝ (spatialField velocity) point (EuclideanSpace.single direction 1)) direction) = 0 := by
  have paid : Summable fun wave => iteratedFDeriv ℝ 1 (mode velocity wave) point :=
    ((moments 1).mul_left ((2 * Real.pi) ^ 1)).of_norm_bounded
      (fun wave => mode_iterated_bound velocity wave 1 point)
  have original := divergenceRead.map_tsum paid
  rw [← spatialField_iterated_eq velocity moments 1 point] at original
  rw [divergenceRead_apply] at original
  simp only [iteratedFDeriv_one_apply, mode_divergence_zero velocity transverse, tsum_zero] at original
  exact original

theorem velocity_moments (index : ℕ) (parameter : ℝ) (order : ℕ) :
    Summable fun wave => frequencySize wave ^ order * amplitude (velocity index parameter) wave := by
  have inside : physicalTime index parameter ∈ Icc (window index).first (window index).last :=
    ⟨(physicalTime_mem index parameter).1.le, (physicalTime_mem index parameter).2.le⟩
  change Summable fun wave => frequencySize wave ^ order *
    amplitude (NativeReceiptSpacetime.velocity (receipt index) (physicalTime index parameter)) wave
  rw [← NativeReceiptSpacetime.velocity_read (window index) _ inside]
  exact summable_moment_of_square _ order
    (profile_square_moments (jets (window index) 0) (order + 2) _).1

theorem velocity_transverse (index : ℕ) (parameter : ℝ) : WholeStateTransverse (velocity index parameter) := by
  intro wave
  change complexWavevector wave ⬝ᵥ biotSavartVelocityCoefficient wave
    (NativeReceiptSpacetime.state (receipt index) (physicalTime index parameter) wave) = 0
  exact complexWavevector_dot_biotSavartVelocityCoefficient _ _

theorem source_spatial_divergence (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    (∑ direction : Coordinate,
      (fderiv ℝ (spatialField (velocity index parameter)) point (EuclideanSpace.single direction 1)) direction) = 0 :=
  spatial_divergence_of_transverse _ (velocity_moments index parameter) (velocity_transverse index parameter) point

theorem source_coordinate_fderiv (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) (direction : Coordinate) :
    fderiv ℝ (fun space => spatialField (velocity index parameter) space direction) point =
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) direction).comp
        (fderiv ℝ (spatialField (velocity index parameter)) point) := by
  have smooth := spatialField_smooth _ (velocity_moments index parameter)
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) direction).hasFDerivAt.comp point
    (smooth.differentiable (by simp) point).hasFDerivAt).fderiv

theorem source_densitized_divergence (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    (∑ direction : Coordinate,
      fderiv ℝ (fun space => densitizedCurrent (spatialField (velocity index parameter) space) direction.succ)
        point (EuclideanSpace.single direction 1)) = 0 := by
  simp only [densitizedCurrent_spatial, source_coordinate_fderiv, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  exact source_spatial_divergence index parameter point

theorem source_phase_divergence (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    (∑ direction : Coordinate,
      fderiv ℝ (fun space => phaseMomentum (spatialField (velocity index parameter) space) direction.succ)
        point (EuclideanSpace.single direction 1)) = 0 := by
  simp only [phaseMomentum_spatial, fderiv_fun_neg, neg_apply, source_coordinate_fderiv,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  rw [Finset.sum_neg_distrib, source_spatial_divergence, neg_zero]

theorem source_phase_temporal (index : ℕ) (actual : ℝ) (point : PhysicalSpace) :
    HasDerivAt (fun time => phaseMomentum
      (spatialField (NativeReceiptSpacetime.velocity (receipt index) time) point) 0) 0 actual := by
  simp only [phaseMomentum_temporal]
  exact hasDerivAt_const actual (-1)

theorem source_current_continuity (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    deriv (fun time => densitizedCurrent
        (spatialField (NativeReceiptSpacetime.velocity (receipt index) time) point) 0) (physicalTime index parameter) +
      (∑ direction : Coordinate,
        fderiv ℝ (fun space => densitizedCurrent (spatialField (velocity index parameter) space) direction.succ)
          point (EuclideanSpace.single direction 1)) = 0 := by
  rw [(densitizedCurrent_temporal_hasDerivAt _ _).deriv, source_densitized_divergence, add_zero]

theorem source_phase_ward (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    deriv (fun time => phaseMomentum
        (spatialField (NativeReceiptSpacetime.velocity (receipt index) time) point) 0) (physicalTime index parameter) +
      (∑ direction : Coordinate,
        fderiv ℝ (fun space => phaseMomentum (spatialField (velocity index parameter) space) direction.succ)
          point (EuclideanSpace.single direction 1)) = 0 := by
  rw [(source_phase_temporal index (physicalTime index parameter) point).deriv, source_phase_divergence, add_zero]

end
end SaturationMonoid.NavierStokes.NativeTimeChartPhaseWard
