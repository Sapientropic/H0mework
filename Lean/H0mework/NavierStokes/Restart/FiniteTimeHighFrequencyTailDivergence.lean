import H0mework.NavierStokes.Restart.FiniteTimeVorticityDivergence
import H0mework.NavierStokes.Restart.HighFrequencyEscape

/-!
# Tailwise high-frequency escape at a finite whole-restart accumulation

The complete physical vorticity mass now tends to infinity along every late
actual contact of a bounded elapsed whole-restart run.  The native kinetic
ledger independently bounds the physical coefficient mass inside each fixed
canonical Fourier cube.  Their exact sharp-projection partition therefore
forces the complementary vorticity mass to tend to infinity along the entire
tail.

Consequently every sufficiently late actual contact, and in particular every
sufficiently late contact on the already generated velocity-endpoint
subsequence, contains a concrete nonzero physical Fourier row outside any
fixed native cube.  The cube is universally quantified conclusion structure;
it does not control source generation.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

noncomputable section

/-- Outside every fixed source-native cube, actual physical vorticity mass
tends to infinity along the whole bounded-time tail. -/
theorem
    tendsto_restartPhysicalHighFrequencyTailMass_atTop_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : ℕ) :
    Tendsto
      (fun index =>
        restartPhysicalHighFrequencyTailMass initial index radius)
      atTop atTop := by
  let coreBound :=
    finiteModeKineticAmbientFactor (wholeRestartModes radius) *
      puncturedWholeVorticityKineticMass
        (run initial 0).contact.physicalState
  have totalTendsto :=
    tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded
  apply Filter.tendsto_atTop.2
  intro bound
  have totalEventually :
      ∀ᶠ index in atTop,
        bound + coreBound ≤
          restartPhysicalVorticityMass initial index :=
    Filter.tendsto_atTop.1 totalTendsto (bound + coreBound)
  filter_upwards [totalEventually] with index totalLarge
  have lowLe :
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (wholeRestartModes radius)
            (run initial index).contact.physicalState) ≤
        coreBound := by
    simpa only [coreBound] using
      restartPhysicalLowFrequencyMass_le_initialKinetic
        initial index radius
  have partition :=
    restartPhysicalVorticityMass_eq_low_add_tail
      initial index radius
  linarith

/-- Every sufficiently late actual contact carries a concrete nonzero
physical row outside a fixed canonical native cube.  The wave and occurrence
are conclusion data selected from the exact nonzero complement. -/
theorem
    eventually_generates_nonzero_wave_outside_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : ℕ) :
    ∀ᶠ index : ℕ in atTop,
      ∃ wave : IntegerWavevector,
        wave ∉ wholeRestartModes radius ∧
          (run initial index).contact.physicalState wave ≠ 0 := by
  have tailEventually :
      ∀ᶠ index in atTop,
        1 ≤ restartPhysicalHighFrequencyTailMass
          initial index radius :=
    Filter.tendsto_atTop.1
      (tendsto_restartPhysicalHighFrequencyTailMass_atTop_of_elapsedTime_bddAbove
        initial elapsedBounded radius) 1
  filter_upwards [tailEventually] with index tailPositive
  by_contra noOutside
  push Not at noOutside
  have projectionEq :
      complexSharpSupportProjection
          (wholeRestartModes radius)
          (run initial index).contact.physicalState =
        (run initial index).contact.physicalState := by
    ext wave
    by_cases waveMem : wave ∈ wholeRestartModes radius
    · simp [complexSharpSupportProjection_apply, waveMem]
    · simp [complexSharpSupportProjection_apply, waveMem,
        noOutside wave waveMem]
  have tailZero :
      restartPhysicalHighFrequencyTailMass initial index radius = 0 := by
    change
      wholeVorticityEuclideanMass
        (complexSharpSupportProjection
            (wholeRestartModes radius)
            (run initial index).contact.physicalState -
          (run initial index).contact.physicalState) = 0
    rw [projectionEq, sub_self]
    simp [wholeVorticityEuclideanMass, vorticityRowAmplitude,
      complexCoordinateAmplitudeSq]
  rw [tailZero] at tailPositive
  norm_num at tailPositive

/-- The exact cofinal contact subsequence already used to build the physical
velocity endpoint inherits the eventual concrete high-frequency occurrence.
No second subsequence is selected. -/
theorem
    sourceGeneratedVelocityEndpoint_eventually_nonzero_wave_outside
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : ℕ) :
    let endpoint :=
      generatedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded
    ∀ᶠ index : ℕ in atTop,
      ∃ wave : IntegerWavevector,
        wave ∉ wholeRestartModes radius ∧
          (run initial (endpoint.subsequence index)).contact.physicalState
            wave ≠ 0 := by
  dsimp only
  let endpoint :=
    generatedWholeRestartVelocityWeakEndpointAtAccumulation
      initial elapsedBounded
  exact endpoint.subsequence_strictMono.tendsto_atTop.eventually
    (eventually_generates_nonzero_wave_outside_of_elapsedTime_bddAbove
      initial elapsedBounded radius)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence
end NavierStokes
end SaturationMonoid
