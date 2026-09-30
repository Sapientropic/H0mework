import H0mework.NavierStokes.StressResolvent.WholeResolventIdentity
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativePhysicalPairing

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open NativeFiniteActionResolvent NativeWholeResolvent NativeEndpointVelocityCarrier

noncomputable section

instance : CompleteSpace wholePhysical := wholePhysical_closed.isComplete.completeSpace_coe

theorem physical_real_inner (first last : NativeResolventCompactness.State) :
    inner ℝ first last = (inner ℂ first last).re := by
  have realNorm := norm_add_sq_real first last
  have complexNorm := norm_add_sq (𝕜 := ℂ) first last
  change ‖first + last‖ ^ 2 = ‖first‖ ^ 2 + 2 * (inner ℂ first last).re + ‖last‖ ^ 2 at complexNorm
  linarith

theorem included_physical (frequencies : Finset IntegerWavevector) (closed : FiniteModeNegClosed frequencies)
    (value : physicalSpace frequencies) : puncturedEuclideanize value.1 ∈ wholePhysical := by
  constructor
  · intro wave
    exact finiteTransverseSupportProjection_fixed_transverse value.2.1 wave.1
  · intro wave coordinate
    exact congrFun (physical_reality (fun {_} member => closed _ member) value wave.1) coordinate

def includeCLM (frequencies : Finset IntegerWavevector) (closed : FiniteModeNegClosed frequencies) :
    physicalSpace frequencies →L[ℝ] wholePhysical :=
  ((puncturedEuclideanizeCLM.restrictScalars ℝ).comp (physicalSpace frequencies).subtypeL).codRestrict
    wholePhysical (included_physical frequencies closed)

theorem include_norm (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (value : physicalSpace frequencies) :
    ‖includeCLM frequencies closed value‖ = ‖NativeFiniteActionResolvent.coefficients frequencies value‖ :=
  physical_norm frequencies zeroNotMem value

theorem restrict_include (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (value : physicalSpace frequencies) :
    restrictCLM frequencies zeroNotMem closed (includeCLM frequencies closed value) = value :=
  NativeWholeResolventIdentity.restrict_embedded frequencies zeroNotMem closed value _

theorem include_inner (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (value : physicalSpace frequencies) (test : wholePhysical) :
    inner ℝ (includeCLM frequencies closed value) test =
      pairing frequencies value (restrictCLM frequencies zeroNotMem closed test) := by
  classical
  change inner ℝ (puncturedEuclideanize value.1) test.1 = _
  rw [lp.inner_eq_tsum, pairing_eq]
  have row (wave : NativeResolventCompactness.Wave) :
      inner ℝ (puncturedEuclideanize value.1 wave) (test.1 wave) =
        complexCoordinateRealInner (value.1 wave.1) (wholeVelocity test.1 wave.1) := by
    rw [PiLp.inner_apply]
    unfold complexCoordinateRealInner
    apply Finset.sum_congr rfl
    intro coordinate _
    rw [wholeVelocity_nonzero test.1 wave coordinate]
    change (test.1 wave coordinate * star (value.1 wave.1 coordinate)).re = _
    simp [Complex.mul_re, mul_comm]
  simp_rw [row]
  let density (wave : IntegerWavevector) := complexCoordinateRealInner (value.1 wave) (wholeVelocity test.1 wave)
  let observed : Finset NativeResolventCompactness.Wave := frequencies.subtype (fun wave => wave ≠ 0)
  have finite : (∑' wave : NativeResolventCompactness.Wave, density wave.1) =
      ∑ wave ∈ observed, density wave.1 :=
    tsum_eq_sum (fun wave outside => by
      have excluded : wave.1 ∉ frequencies := by simpa only [observed, Finset.mem_subtype] using outside
      dsimp only [density]
      rw [physical_supported value wave.1 excluded]
      simp [complexCoordinateRealInner])
  have full : (∑' wave : NativeResolventCompactness.Wave, density wave.1) = ∑ wave ∈ frequencies, density wave :=
    finite.trans (Finset.sum_subtype_of_mem density (fun wave member zero => zeroNotMem (zero ▸ member)))
  change (∑' wave : NativeResolventCompactness.Wave, density wave.1) = _
  rw [full]
  apply Finset.sum_congr rfl
  intro wave included
  change complexCoordinateRealInner (value.1 wave) (wholeVelocity test.1 wave) =
    complexCoordinateRealInner (value.1 wave)
      (complexSharpSupportProjection frequencies (wholeVelocity test.1) wave)
  rw [complexSharpSupportProjection_apply, if_pos included]

end
end SaturationMonoid.NavierStokes.NativePhysicalPairing
