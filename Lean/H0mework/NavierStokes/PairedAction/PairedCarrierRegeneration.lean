import H0mework.NavierStokes.ResolvedAction.ResolvedPairingTransfer
import H0mework.NavierStokes.CofinalAction.CofinalCurrentResponseAction

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativePairedCarrierRegeneration

open Set UnitAddTorus
open PhysicsCore.DiracCliffordRepresentation
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeEndpointVelocityCarrier NativeStressPairingCarrier NativeHilbertDiracCurrent
open NativeResolvedPairingTransfer
open NativeCofinalUnifiedField (target)

noncomputable section

variable {nu : Viscosity}

def mean (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState (NativeReceiptSpacetime.state (NativeCofinalUnifiedField.receipt initial) actual)

theorem mean_velocity (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) :
    wholeVelocity (mean initial actual) = NativeCofinalCurrentResponse.regeneratedVelocity initial actual := wholeVelocity_punctured _

theorem mean_reality (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : WholeRestartVelocityEndpointReality (mean initial actual) := by
  have source : FiniteStateFourierReality (wholeVelocity (mean initial actual)) := by
    rw [mean_velocity]
    exact NativeCofinalCurrentResponse.regenerated_reality initial actual
  intro wave coordinate
  have row := congrFun (source wave.1) coordinate
  change wholeVelocity (mean initial actual) (nonzeroIntegerWavevectorNeg wave).1 coordinate =
    star (wholeVelocity (mean initial actual) wave.1 coordinate) at row
  simpa only [wholeVelocity_nonzero] using row

def sourceMatter (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (wave : IntegerWavevector) : Spinor (cofinal initial) :=
  writtenMatter (cofinal initial) (mean initial actual) (mean_reality initial actual) wave

def sourceCurrent (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual (cofinal initial) (sourceMatter initial actual wave)
    (action (cofinal initial) (diracGamma direction) (sourceMatter initial actual 0))

theorem source_current_eq_regenerated (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    sourceCurrent initial actual direction wave = NativeCofinalCurrentResponse.regenerated initial actual direction wave := by
  rw [sourceCurrent, sourceMatter, sourceMatter]
  change writtenCurrent (cofinal initial) (mean initial actual) (mean_reality initial actual) direction wave = _
  rw [writtenCurrent_eq, mean_velocity, NativeCofinalCurrentResponse.regenerated,
    NativePairedCurrentFourier.current_fourier _ (NativeCofinalCurrentResponse.regenerated_reality initial actual)]

def difference (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (wave : IntegerWavevector) : Spinor (cofinal initial) :=
  sourceMatter initial actual wave - matter (cofinal initial) wave

theorem difference_retains_covariance (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (wave : IntegerWavevector) (spin : Fin 4) (color : Fin 2) :
    WithLp.snd (difference initial actual wave spin color) = -WithLp.snd (matter (cofinal initial) wave spin color) := by
  change WithLp.snd (sourceMatter initial actual wave spin color - matter (cofinal initial) wave spin color) = _
  rw [WithLp.sub_snd]
  change (0 : NativePositiveKernelCarrier.Space (kernel (cofinal initial))) - _ = _
  exact zero_sub _

theorem canonicalDual_sub (data : Data) (first second candidate : Spinor data) :
    canonicalDual data (first - second) candidate = canonicalDual data first candidate - canonicalDual data second candidate := by
  simp only [canonicalDual, map_sub, Pi.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  rfl

theorem source_current_effect (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    sourceCurrent initial actual direction wave - diracCurrent (cofinal initial) direction wave =
      canonicalDual (cofinal initial) (matter (cofinal initial) wave)
        (action (cofinal initial) (diracGamma direction) (difference initial actual 0)) +
      canonicalDual (cofinal initial) (difference initial actual wave)
        (action (cofinal initial) (diracGamma direction) (matter (cofinal initial) 0)) +
      canonicalDual (cofinal initial) (difference initial actual wave)
        (action (cofinal initial) (diracGamma direction) (difference initial actual 0)) := by
  unfold sourceCurrent diracCurrent difference
  simp only [map_sub, canonicalDual_sub]
  abel

theorem source_temporal_response (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (wave : IntegerWavevector) :
    sourceCurrent initial actual 0 wave - diracCurrent (cofinal initial) 0 wave =
      -NativePairedCurrentFourier.trace (NativeCofinalCurrentResponse.regenerationStress initial actual) wave / 8 := by
  rw [source_current_eq_regenerated, NativeHilbertDiracCurrent.cofinal_current]
  exact NativeCofinalCurrentResponse.temporal_response initial actual wave

theorem source_response_all_time_jets (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (direction : Fin 4) (wave : IntegerWavevector) :
    iteratedDerivWithin order (fun sample => sourceCurrent initial sample direction wave - diracCurrent (cofinal initial) direction wave)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual =
        NativeCofinalCurrentResponseAction.responseJet initial order actual direction wave := by
  simp only [source_current_eq_regenerated, NativeHilbertDiracCurrent.cofinal_current]
  exact NativeCofinalCurrentResponseAction.response_iteratedDerivWithin initial order actual inside direction wave

theorem source_generated_next_current (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    sourceCurrent initial (target initial).next.contact.time.1 direction wave =
      mFourierCoeff (fun point =>
        (NativePairedCurrentFourier.field (wholeBiotSavartVelocityState (target initial).next.contact.physicalState) direction point : ℂ)) wave := by
  rw [source_current_eq_regenerated]
  exact NativeCofinalCurrentResponse.generated_next_current initial direction wave

end
end SaturationMonoid.NavierStokes.NativePairedCarrierRegeneration
