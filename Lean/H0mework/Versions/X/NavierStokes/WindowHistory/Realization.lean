import H0mework.Versions.X.NavierStokes.WindowHistory.Vectors
import H0mework.NavierStokes.SourcePairing.PairingKernelRealization

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryGNS
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCofinalStressPositivity
noncomputable section
variable {nu : Viscosity}

def residual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    NativePositiveKernelCarrier.Space (NativeStressPairingCarrier.kernel (NativeForwardWindowPairing.data seed time)) →ₗᵢ[ℂ] HistoryHilbert :=
  NativePositiveKernelRealization.realize _ (vector seed time) (vector_inner seed time)

theorem residual_vector (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    residual seed time (NativePositiveKernelCarrier.vector (NativeStressPairingCarrier.kernel (NativeForwardWindowPairing.data seed time)) index) =
      vector seed time index := NativePositiveKernelRealization.realize_vector _ _ _ index

theorem residual_orthogonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (value : ScalarSequence)
    (fluctuation : NativePositiveKernelCarrier.Space (NativeStressPairingCarrier.kernel (NativeForwardWindowPairing.data seed time))) :
    inner ℂ (constant value) (residual seed time fluctuation) = 0 := by
  induction fluctuation using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_const.inner (residual seed time).continuous) continuous_const
  | ih coefficients =>
      rw [residual, NativePositiveKernelRealization.realize_coe]
      simp only [Finsupp.sum, inner_sum, inner_smul_right, constant_vector, mul_zero, Finset.sum_const_zero]

def realization (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time) →ₗᵢ[ℂ] HistoryHilbert where
  toFun value := constant (WithLp.fst value)+residual seed time (WithLp.snd value)
  map_add' first last := by
    change constant (WithLp.fst first+WithLp.fst last)+residual seed time (WithLp.snd first+WithLp.snd last) = _
    rw [constant_add,map_add]
    abel
  map_smul' scalar value := by
    change constant (scalar • WithLp.fst value)+residual seed time (scalar • WithLp.snd value) = _
    rw [constant_smul,map_smul,smul_add]
    rfl
  norm_map' value := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖constant (WithLp.fst value)+residual seed time (WithLp.snd value)‖^2 = ‖value‖^2
    have orthogonal := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (residual_orthogonal seed time (WithLp.fst value) (WithLp.snd value))
    simp only [← pow_two] at orthogonal
    rw [orthogonal, (residual seed time).norm_map, WithLp.prod_norm_sq_eq_of_L2]
    have same : ‖constant (WithLp.fst value)‖ = ‖WithLp.fst value‖ := constantIsometry.norm_map _
    rw [same]

theorem realization_background (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    realization seed time (NativeStressPairingCarrier.background (NativeForwardWindowPairing.data seed time) wave) =
      constant (lp.single 2 wave (1 : ℂ)) := by
  change constant (lp.single 2 wave (1 : ℂ))+residual seed time 0 = _
  rw [map_zero,add_zero]

theorem realization_component (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    realization seed time (NativeStressPairingCarrier.component (NativeForwardWindowPairing.data seed time) index) =
      history seed time index := by
  change constant (mean seed time index)+residual seed time (NativePositiveKernelCarrier.vector _ index) = _
  rw [residual_vector,vector]
  abel

theorem realization_component_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    realization seed time (NativeStressPairingCarrier.component (NativeForwardWindowPairing.data seed time) index) =ᵐ[NativeForwardWindowPairingReadout.averageMeasure]
      fun shift => shiftedComponent (NativeUnifiedCompleteSource.source seed (time-shift)).fst index := by
  rw [realization_component]
  exact (history_ae seed time index).trans (Eventually.of_forall (sample_original seed time index))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryGNS
