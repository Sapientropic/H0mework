import H0mework.NavierStokes.Restart.FiniteTimeObstruction
import H0mework.NavierStokes.Galerkin.KineticAmbientBound

/-!
# High-frequency escape of the native whole-flow restart chain

The actual kinetic ledger of the generated restart chain controls every
fixed native punctured cube.  The exact sharp-projection mass partition
therefore converts the finite-time whole-vorticity cascade into an
unbounded physical complement outside every such cube.

The cube is the canonical source inventory `wholeRestartModes radius` and
the crossing occurrence is conclusion data.  No tail bound, crossing
index, wave, amplitude, cutoff certificate, or target solution is accepted
from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open
  ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction

noncomputable section

/-- Actual Euclidean coefficient mass outside one canonical native cube,
measured before the omitted occurrence information is quotiented away. -/
def restartPhysicalHighFrequencyTailMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  let state := (run initial index).contact.physicalState
  wholeVorticityEuclideanMass
    (complexSharpSupportProjection (wholeRestartModes radius) state - state)

/-- The actual low-frequency projection at every generated contact is paid
by the initial complete kinetic mass of the same restart chain. -/
theorem restartPhysicalLowFrequencyMass_le_initialKinetic
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeVorticityEuclideanMass
        (complexSharpSupportProjection
          (wholeRestartModes radius)
          (run initial index).contact.physicalState) ≤
      finiteModeKineticAmbientFactor (wholeRestartModes radius) *
        puncturedWholeVorticityKineticMass
          (run initial 0).contact.physicalState := by
  let modes := wholeRestartModes radius
  let state := (run initial index).contact.physicalState
  have zeroNotMem : 0 ∉ modes :=
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have finiteTransverse : FiniteStateTransverseOn modes state :=
    fun wave _waveMem => (run initial index).contact.transverse wave
  have enstrophyLeEnergy :
      finiteStateVorticityCoefficientEnstrophy modes state ≤
        finiteModeKineticAmbientFactor modes *
          finiteStateVorticityKineticEnergy modes state :=
    finiteStateVorticityCoefficientEnstrophy_le_kineticEnergy_factor
      modes zeroNotMem state finiteTransverse
  have twiceEnergyLe :
      2 * finiteStateVorticityKineticEnergy modes state ≤
        puncturedWholeVorticityKineticMass state :=
    two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
      modes zeroNotMem state finiteTransverse
  have energyNonneg :
      0 ≤ finiteStateVorticityKineticEnergy modes state :=
    finiteStateVorticityKineticEnergy_nonneg modes state
  have energyLeCurrent :
      finiteStateVorticityKineticEnergy modes state ≤
        puncturedWholeVorticityKineticMass state := by
    linarith
  have currentLeInitial :
      puncturedWholeVorticityKineticMass state ≤
        puncturedWholeVorticityKineticMass
          (run initial 0).contact.physicalState := by
    exact run_contact_kineticMass_antitone initial (Nat.zero_le index)
  have energyLeInitial :
      finiteStateVorticityKineticEnergy modes state ≤
        puncturedWholeVorticityKineticMass
          (run initial 0).contact.physicalState :=
    energyLeCurrent.trans currentLeInitial
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    modes (complexSharpSupportProjection modes state)
    (complexSharpSupportProjection_supported modes state)]
  rw [finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
  exact enstrophyLeEnergy.trans
    (mul_le_mul_of_nonneg_left energyLeInitial
      (finiteModeKineticAmbientFactor_nonneg modes))

/-- Low cube plus omitted complement is the exact physical mass at the same
generated contact. -/
theorem restartPhysicalVorticityMass_eq_low_add_tail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    restartPhysicalVorticityMass initial index =
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (wholeRestartModes radius)
            (run initial index).contact.physicalState) +
        restartPhysicalHighFrequencyTailMass initial index radius := by
  exact wholeVorticityEuclideanMass_eq_projection_add_complement
    (wholeRestartModes radius)
    (run initial index).contact.physicalState

/-- If physical vorticity mass is unbounded along the generated contacts,
then the actual complement outside every canonical native cube is itself
unbounded.  The kinetic ledger rules out low-frequency inflation. -/
theorem restartPhysicalHighFrequencyTailMass_not_bddAbove
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (physicalUnbounded :
      ¬ BddAbove (Set.range (restartPhysicalVorticityMass initial)))
    (radius : ℕ) :
    ¬ BddAbove
      (Set.range fun index =>
        restartPhysicalHighFrequencyTailMass initial index radius) := by
  rw [not_bddAbove_iff]
  intro bound
  let coreBound :=
    finiteModeKineticAmbientFactor (wholeRestartModes radius) *
      puncturedWholeVorticityKineticMass
        (run initial 0).contact.physicalState
  obtain ⟨mass, ⟨index, rfl⟩, massLarge⟩ :=
    not_bddAbove_iff.1 physicalUnbounded (coreBound + bound)
  refine
    ⟨restartPhysicalHighFrequencyTailMass initial index radius,
      ⟨index, rfl⟩, ?_⟩
  have lowLe :
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (wholeRestartModes radius)
            (run initial index).contact.physicalState) ≤
        coreBound := by
    simpa only [coreBound] using
      restartPhysicalLowFrequencyMass_le_initialKinetic
        initial index radius
  rw [restartPhysicalVorticityMass_eq_low_add_tail
    initial index radius] at massLarge
  linarith

/-- Finite accumulated physical time forces unbounded actual mass outside
every source-native cube. -/
theorem elapsedTime_bddAbove_forces_highFrequencyTail_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : ℕ) :
    ¬ BddAbove
      (Set.range fun index =>
        restartPhysicalHighFrequencyTailMass initial index radius) :=
  restartPhysicalHighFrequencyTailMass_not_bddAbove initial
    (elapsedTime_bddAbove_forces_physicalVorticityMass_unbounded
      initial elapsedBounded)
    radius

/-- Hence every canonical native cube is eventually escaped by an actual
nonzero Fourier responsibility on the same generated whole-flow chain. -/
theorem elapsedTime_bddAbove_generates_nonzero_wave_outside
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : ℕ) :
    ∃ index : ℕ, ∃ wave : IntegerWavevector,
      wave ∉ wholeRestartModes radius ∧
        (run initial index).contact.physicalState wave ≠ 0 := by
  have tailUnbounded :=
    elapsedTime_bddAbove_forces_highFrequencyTail_unbounded
      initial elapsedBounded radius
  obtain ⟨tail, ⟨index, rfl⟩, tailPos⟩ :=
    not_bddAbove_iff.1 tailUnbounded 0
  refine ⟨index, ?_⟩
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
  change
    0 < wholeVorticityEuclideanMass
      (complexSharpSupportProjection
          (wholeRestartModes radius)
          (run initial index).contact.physicalState -
        (run initial index).contact.physicalState) at tailPos
  rw [projectionEq, sub_self] at tailPos
  simp [wholeVorticityEuclideanMass, vorticityRowAmplitude,
    complexCoordinateAmplitudeSq] at tailPos

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
end NavierStokes
end SaturationMonoid
