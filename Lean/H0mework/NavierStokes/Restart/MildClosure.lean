import H0mework.NavierStokes.Restart.CriticalClosure
import H0mework.NavierStokes.Restart.FiniteObservedCompactness
import H0mework.NavierStokes.ShellSources.InfiniteMildDuhamel
import H0mework.NavierStokes.Fourier.WholeVelocityFixedOutputNonlinearRow

/-!
# Continuous mild rows of the generated whole restart limit

Finite-observation compactness restores a continuous representative of each
nonzero Fourier row of the strong whole-state limit.  Canonical cube
exhaustion makes that row eventually belong to the actual unforced Galerkin
law, while the projected initial states converge to the exact restart state.
The resulting mild law therefore starts from the same actual whole contact;
no cutoff, target path, or continuation witness is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMildClosure

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-! ## Kinetic time modulus before finite-observation quotient -/

/-- Twice the finite kinetic energy is the complete Euclidean velocity-row
square on the same finite carrier. -/
private theorem velocityRowAmplitude_sq_sum_eq_two_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes, velocityRowAmplitude state wave ^ 2) =
      2 * finiteStateVorticityKineticEnergy modes state := by
  unfold finiteStateVorticityKineticEnergy
  have rowIdentity :
      (∑ wave ∈ modes, velocityRowAmplitude state wave ^ 2) =
        ∑ wave ∈ modes,
          complexCoordinateVectorNormSq
            (finiteStateVelocityCoefficient state wave) := by
    apply Finset.sum_congr rfl
    intro wave _waveMem
    rw [velocityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [rowIdentity]
  ring

/-- Installing a finite velocity table on the whole carrier loses no more
than its exact finite kinetic square. -/
private theorem finiteStateWholeVelocity_norm_sq_le_two_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ‖finiteStateWholeVelocity modes state‖ ^ 2 ≤
      2 * finiteStateVorticityKineticEnergy modes state := by
  calc
    ‖finiteStateWholeVelocity modes state‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy modes
          (finiteStateWholeVelocity modes state) :=
      complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        modes (finiteStateWholeVelocity modes state) (by
          intro wave waveNotMem
          simp [finiteStateWholeVelocity_apply, waveNotMem])
    _ = ∑ wave ∈ modes, velocityRowAmplitude state wave ^ 2 := by
      unfold finiteStateVorticityCoefficientEnstrophy
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [finiteStateWholeVelocity_apply, if_pos waveMem,
        ← velocityRowAmplitude_sq]
    _ = 2 * finiteStateVorticityKineticEnergy modes state :=
      velocityRowAmplitude_sq_sum_eq_two_kineticEnergy modes state

/-- Every canonical Galerkin stage's installed velocity norm is paid by the
kinetic mass of the exact source contact that generated the stage. -/
private theorem canonicalStage_finiteStateWholeVelocity_norm_sq_le_contact
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    ‖finiteStateWholeVelocity
        (wholeRestartModes radius) (stage.trajectory time.1)‖ ^ 2 ≤
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState contact) := by
  let modes := wholeRestartModes radius
  have zeroNotMem : 0 ∉ modes :=
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  calc
    ‖finiteStateWholeVelocity modes (stage.trajectory time.1)‖ ^ 2 ≤
        2 * finiteStateVorticityKineticEnergy modes
          (stage.trajectory time.1) :=
      finiteStateWholeVelocity_norm_sq_le_two_kineticEnergy
        modes (stage.trajectory time.1)
    _ ≤ puncturedWholeVorticityKineticMass
          (stage.trajectory time.1) :=
      two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
        modes zeroNotMem (stage.trajectory time.1)
        (fun wave waveMem =>
          (stage.physical time.1 time.2).2.2.1 wave)
    _ ≤ puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact) :=
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure.GeneratedWholeRestartCanonicalStage.kineticMass_le
        stage time

private theorem biotSavartVelocityCoefficient_real_smul
    (wave : IntegerWavevector)
    (scalar : ℝ)
    (vorticity : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient wave (scalar • vorticity) =
      scalar • biotSavartVelocityCoefficient wave vorticity := by
  change
    biotSavartVelocityCoefficient wave ((scalar : ℂ) • vorticity) =
      (scalar : ℂ) • biotSavartVelocityCoefficient wave vorticity
  exact biotSavartVelocityCoefficient_smul wave scalar vorticity

/-- On a retained nonzero row, Biot--Savart compiles the actual vorticity
generator to the Leray-projected velocity convection minus viscosity. -/
private theorem biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector)
    (outputMem : output ∈ modes) :
    biotSavartVelocityCoefficient output
        (finiteStateVorticityGenerator modes ν state output) =
      transverseProjection output
          (finiteStateVelocityNonlinearCoefficientAt modes state output) -
        (ν * integerWaveViscousMultiplier output) •
          finiteStateVelocityCoefficient state output := by
  have outputNe : output ≠ 0 := fun outputZero =>
    zeroNotMem (outputZero ▸ outputMem)
  rw [finiteStateVorticityGenerator_apply, if_pos outputMem,
    biotSavartVelocityCoefficient_sub,
    finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
      modes zeroNotMem state stateTransverse output,
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      output (finiteStateVelocityNonlinearCoefficientAt modes state output)
      outputNe,
    biotSavartVelocityCoefficient_real_smul]
  rfl

/-- Source-owned fixed-wave speed ceiling.  It depends only on the exact
contact kinetic mass, viscosity, and the observed physical wave; no
Galerkin radius or target path occurs. -/
def wholeRestartFixedWaveVelocitySpeedCeiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (wave : IntegerWavevector) : ℝ :=
  let mass :=
    puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact)
  ‖transverseProjectionCLM wave‖ *
      ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) * mass) +
    (ν.coeff * integerWaveViscousMultiplier wave) * (mass + 1)

theorem wholeRestartFixedWaveVelocitySpeedCeiling_nonneg
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (wave : IntegerWavevector) :
    0 ≤ wholeRestartFixedWaveVelocitySpeedCeiling contact wave := by
  unfold wholeRestartFixedWaveVelocitySpeedCeiling
  have massNonneg :=
    puncturedWholeVorticityKineticMass_nonneg
      (wholeRestartPhysicalState contact)
  have multiplierNonneg : 0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
  exact add_nonneg
    (mul_nonneg (norm_nonneg _)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)
          (Real.sqrt_nonneg _))
        massNonneg))
    (mul_nonneg
      (mul_nonneg ν.coeff_pos.le multiplierNonneg)
      (by linarith))

/-- The speed ceiling is monotone in its kinetic-mass argument.  This is the
bridge used by a whole native run, whose contact kinetic mass is antitone. -/
theorem wholeRestartFixedWaveVelocitySpeedCeiling_le_of_kineticMass_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {left right : Seed}
    (massLe :
      puncturedWholeVorticityKineticMass (wholeRestartPhysicalState left) ≤
        puncturedWholeVorticityKineticMass (wholeRestartPhysicalState right))
    (wave : IntegerWavevector) :
    wholeRestartFixedWaveVelocitySpeedCeiling left wave ≤
      wholeRestartFixedWaveVelocitySpeedCeiling right wave := by
  unfold wholeRestartFixedWaveVelocitySpeedCeiling
  have angularNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Real.sqrt_nonneg _)
  have multiplierNonneg :
      0 ≤ ν.coeff * integerWaveViscousMultiplier wave := by
    exact mul_nonneg ν.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left massLe angularNonneg)
      (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (by linarith) multiplierNonneg)

/-- One actual canonical Galerkin row has the source-owned speed ceiling,
uniformly in the internally generated radius. -/
private theorem canonicalStage_velocityWave_speed_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact))
    (output : IntegerWavevector)
    (outputMem : output ∈ wholeRestartModes radius) :
    ‖biotSavartVelocityCoefficient output
        (finiteStateVorticityGenerator
          (wholeRestartModes radius) ν.coeff
          (stage.trajectory time.1) output)‖ ≤
      wholeRestartFixedWaveVelocitySpeedCeiling contact output := by
  let modes := wholeRestartModes radius
  let state := stage.trajectory time.1
  let velocity := finiteStateWholeVelocity modes state
  let mass :=
    puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact)
  have zeroNotMem : 0 ∉ modes :=
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have massNonneg : 0 ≤ mass :=
    puncturedWholeVorticityKineticMass_nonneg _
  have velocitySqLe : ‖velocity‖ ^ 2 ≤ mass := by
    exact canonicalStage_finiteStateWholeVelocity_norm_sq_le_contact
      stage time
  have velocityLe : ‖velocity‖ ≤ mass + 1 := by
    nlinarith [sq_nonneg (‖velocity‖ - 1), norm_nonneg velocity]
  have nonlinearLe :
      ‖finiteStateVelocityNonlinearCoefficientAt modes state output‖ ≤
        (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) * mass := by
    rw [← wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity]
    calc
      ‖wholeStateVelocityNonlinearCoefficientAt velocity output‖ ≤
          (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            ‖velocity‖ * ‖velocity‖ :=
        wholeStateVelocityBilinearCoefficientAt_norm_le
          velocity velocity (finiteStateWholeVelocity_transverse modes state)
          output
      _ = (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            ‖velocity‖ ^ 2 := by ring
      _ ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) * mass :=
        mul_le_mul_of_nonneg_left velocitySqLe (by positivity)
  have outputRowLe :
      ‖finiteStateVelocityCoefficient state output‖ ≤ mass + 1 := by
    have rowLe := lp.norm_apply_le_norm (by norm_num) velocity output
    rw [finiteStateWholeVelocity_apply, if_pos outputMem] at rowLe
    exact rowLe.trans velocityLe
  have coefficientNonneg :
      0 ≤ ν.coeff * integerWaveViscousMultiplier output := by
    exact mul_nonneg ν.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  rw [biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
    modes zeroNotMem ν.coeff state
    (fun wave waveMem => (stage.physical time.1 time.2).2.2.1 wave)
    output outputMem]
  calc
    ‖transverseProjection output
          (finiteStateVelocityNonlinearCoefficientAt modes state output) -
        (ν.coeff * integerWaveViscousMultiplier output) •
          finiteStateVelocityCoefficient state output‖ ≤
      ‖transverseProjection output
          (finiteStateVelocityNonlinearCoefficientAt modes state output)‖ +
        ‖(ν.coeff * integerWaveViscousMultiplier output) •
          finiteStateVelocityCoefficient state output‖ := norm_sub_le _ _
    _ ≤
      ‖transverseProjectionCLM output‖ *
          ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) * mass) +
        (ν.coeff * integerWaveViscousMultiplier output) * (mass + 1) := by
      apply add_le_add
      · exact (transverseProjectionCLM output).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_left nonlinearLe (norm_nonneg _))
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg coefficientNonneg]
        exact mul_le_mul_of_nonneg_left outputRowLe coefficientNonneg
    _ = wholeRestartFixedWaveVelocitySpeedCeiling contact output := rfl

/-- Distance form on one finite stage, including the radii before the wave
enters the canonical cube (where the actual row is identically zero). -/
private theorem canonicalStage_velocityWave_dist_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (output : IntegerWavevector)
    (first second : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    dist
        (finiteStateVelocityCoefficient (stage.trajectory first.1) output)
        (finiteStateVelocityCoefficient (stage.trajectory second.1) output) ≤
      wholeRestartFixedWaveVelocitySpeedCeiling contact output *
        dist first second := by
  by_cases outputMem : output ∈ wholeRestartModes radius
  · let path : ℝ → ComplexCoordinateVector := fun time =>
      finiteStateVelocityCoefficient (stage.trajectory time) output
    let tangent : ℝ → ComplexCoordinateVector := fun time =>
      biotSavartVelocityCoefficient output
        (finiteStateVorticityGenerator
          (wholeRestartModes radius) ν.coeff
          (stage.trajectory time) output)
    have pathDerivative :
        ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
          HasDerivWithinAt path (tangent time)
            (Icc (0 : ℝ) (wholeRestartDuration contact)) time := by
      intro time timeMem
      exact
        (finiteStateVelocityTrajectoryWave_hasDerivAt
          stage.trajectory time
          (finiteStateVorticityGenerator
            (wholeRestartModes radius) ν.coeff (stage.trajectory time))
          output (stage.physical time timeMem).1).hasDerivWithinAt
    have tangentBound :
        ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
          ‖tangent time‖ ≤
            wholeRestartFixedWaveVelocitySpeedCeiling contact output := by
      intro time timeMem
      exact canonicalStage_velocityWave_speed_le
        stage ⟨time, timeMem⟩ output outputMem
    have increment :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        pathDerivative tangentBound
        (convex_Icc (0 : ℝ) (wholeRestartDuration contact))
        first.2 second.2
    simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev, path, tangent] using
      (show
        ‖path second.1 - path first.1‖ ≤
          wholeRestartFixedWaveVelocitySpeedCeiling contact output *
            ‖(second.1 - first.1 : ℝ)‖ from increment)
  · have firstZero : stage.trajectory first.1 output = 0 :=
      (stage.physical first.1 first.2).2.1 output outputMem
    have secondZero : stage.trajectory second.1 output = 0 :=
      (stage.physical second.1 second.2).2.1 output outputMem
    have ceilingNonneg :=
      wholeRestartFixedWaveVelocitySpeedCeiling_nonneg contact output
    have rightNonneg :
        0 ≤ wholeRestartFixedWaveVelocitySpeedCeiling contact output *
          dist first second :=
      mul_nonneg ceilingNonneg dist_nonneg
    simpa [finiteStateVelocityCoefficient, firstZero, secondZero] using
      rightNonneg

/-- One canonical fixed-wave Galerkin row along the exact strong-limit
subsequence selected by the whole restart closure. -/
noncomputable def wholeRestartFixedWaveCanonicalBoundedPath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (index : Nat) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) (wholeRestartDuration contact))
      ComplexCoordinateVector :=
  let observed : Finset IntegerWavevector := {wave}
  let coordinate : {actual : IntegerWavevector // actual ∈ observed} :=
    ⟨wave, by simp [observed]⟩
  (((ContinuousLinearMap.proj coordinate :
      FiniteObservedCoefficientState observed →L[ℂ]
        ComplexCoordinateVector)).compLeftContinuousBounded
    (Icc (0 : ℝ) (wholeRestartDuration contact)))
      (wholeRestartFiniteObservedBoundedPath replay observed
        (closure.weakClosure.subsequence index))

private theorem commonTimeBoundedContinuous_toLp_injective
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (requestedTime : Real)
    (requestedTimePos : 0 < requestedTime) :
    Function.Injective
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ :
        BoundedContinuousFunction (Icc (0 : Real) requestedTime)
            E →L[ℂ]
          ↥(MeasureTheory.Lp E 2 (commonTimeMeasure requestedTime))) := by
  intro left right equality
  have leftAE := BoundedContinuousFunction.coeFn_toLp
    (2 : ℝ≥0∞) (commonTimeMeasure requestedTime) ℂ left
  have rightAE := BoundedContinuousFunction.coeFn_toLp
    (2 : ℝ≥0∞) (commonTimeMeasure requestedTime) ℂ right
  have subtypeAE : left =ᵐ[commonTimeMeasure requestedTime] right := by
    filter_upwards [leftAE, rightAE] with time leftEq rightEq
    rw [equality] at leftEq
    exact leftEq.symm.trans rightEq
  let extendedLeft : Real → E := fun time =>
    left (projIcc 0 requestedTime requestedTimePos.le time)
  let extendedRight : Real → E := fun time =>
    right (projIcc 0 requestedTime requestedTimePos.le time)
  have extendedLeftContinuous : Continuous extendedLeft := by
    exact left.continuous.comp continuous_projIcc
  have extendedRightContinuous : Continuous extendedRight := by
    exact right.continuous.comp continuous_projIcc
  have measureEq : commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : Real) requestedTime → Real) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  rw [measureEq] at subtypeAE
  have extendedAE :
      extendedLeft =ᵐ[volume.restrict (Icc (0 : Real) requestedTime)]
        extendedRight := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [subtypeAE] with time timeEq
    simpa only [extendedLeft, extendedRight,
      projIcc_of_mem requestedTimePos.le time.property] using timeEq
  have extendedEq := Measure.eqOn_Icc_of_ae_eq
    (μ := volume) requestedTimePos.ne extendedAE
      extendedLeftContinuous.continuousOn
      extendedRightContinuous.continuousOn
  apply BoundedContinuousFunction.ext
  intro time
  have pointEq := extendedEq time.property
  simpa only [extendedLeft, extendedRight,
    projIcc_of_mem requestedTimePos.le time.property] using pointEq

theorem tendsto_of_compact_of_continuous_injective_map_tendsto
    {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    (sequence : Nat → X)
    (target : X)
    (compact : Set X)
    (compact_isCompact : IsCompact compact)
    (sequence_mem : ∀ index, sequence index ∈ compact)
    (map : X → Y)
    (map_continuous : Continuous map)
    (map_injective : Function.Injective map)
    (mapped_tendsto : Tendsto (fun index => map (sequence index))
      atTop (𝓝 (map target))) :
    Tendsto sequence atTop (𝓝 target) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro subsequence subsequenceTendsto
  obtain ⟨limit, limitMem, refinement, refinementMono, limitTendsto⟩ :=
    compact_isCompact.tendsto_subseq
      (fun index => sequence_mem (subsequence index))
  refine ⟨refinement, ?_⟩
  have mappedLimit : Tendsto
      (fun index => map (sequence (subsequence (refinement index))))
      atTop (𝓝 (map limit)) := by
    exact (map_continuous.tendsto limit).comp limitTendsto
  have refinementTendsto : Tendsto refinement atTop atTop :=
    refinementMono.tendsto_atTop
  have mappedTarget : Tendsto
      (fun index => map (sequence (subsequence (refinement index))))
      atTop (𝓝 (map target)) := by
    exact mapped_tendsto.comp
      (subsequenceTendsto.comp refinementTendsto)
  have limitEq : limit = target :=
    map_injective (tendsto_nhds_unique mappedLimit mappedTarget)
  rw [limitEq] at limitTendsto
  change Tendsto (fun n => sequence (subsequence (refinement n)))
    atTop (𝓝 target) at limitTendsto
  exact limitTendsto

/-- The fixed-wave continuous mild representative together with the
source-owned quantitative modulus that survives finite-observation
compactness.  The modulus is inherited from the same canonical Galerkin
replay; it is not supplied by a target path. -/
structure GeneratedWholeRestartFixedWaveMildHolderReceipt
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (_waveNonzero : wave ≠ 0) where
  mildData :
    FixedWaveContinuousMildData
      (wholeRestartDuration contact) ν.coeff wave
      (fun radius => (replay.current radius).trajectory 0)
      closure.weakClosure.stateLimit
      (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)
  refinement : Nat → Nat
  refinement_strictMono : StrictMono refinement
  row_tendsto :
    Tendsto
      (fun index =>
        wholeRestartFixedWaveCanonicalBoundedPath closure wave
          (refinement index))
      atTop (𝓝 mildData.rowPath)
  row_full_tendsto :
    Tendsto
      (wholeRestartFixedWaveCanonicalBoundedPath closure wave)
      atTop (𝓝 mildData.rowPath)
  increment_sq_le :
    ∀ first second : Icc (0 : ℝ) (wholeRestartDuration contact),
      dist (mildData.rowPath first) (mildData.rowPath second) ^ 2 ≤
        dist first second *
          wholeRestartFiniteObservedHalfHolderEnergy replay {wave}
  velocity_increment_le :
    ∀ first second : Icc (0 : ℝ) (wholeRestartDuration contact),
      dist
          (biotSavartVelocityCoefficient wave (mildData.rowPath first))
          (biotSavartVelocityCoefficient wave (mildData.rowPath second)) ≤
        wholeRestartFixedWaveVelocitySpeedCeiling contact wave *
          dist first second

/-- Every nonzero row of the canonical restart limit has a continuous mild
representative whose initial trace is the exact actual restart state, and
the finite-observation square-increment law is written back to that same
representative. -/
theorem
    GeneratedWholeRestartCriticalClosure.exists_fixedWaveContinuousMildHolderReceipt
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    Nonempty
      (GeneratedWholeRestartFixedWaveMildHolderReceipt
        closure wave waveNonzero) := by
  classical
  let observed : Finset IntegerWavevector := {wave}
  let coordinate : {actual : IntegerWavevector // actual ∈ observed} :=
    ⟨wave, by simp [observed]⟩
  let observedSequence :
      ℕ →
        BoundedContinuousFunction
          (Icc (0 : ℝ) (wholeRestartDuration contact))
          (FiniteObservedCoefficientState observed) :=
    fun index =>
      wholeRestartFiniteObservedBoundedPath replay observed
        (closure.weakClosure.subsequence index)
  have observedSequenceMem :
      ∀ index,
        observedSequence index ∈
          _root_.closure
            (wholeRestartFiniteObservedPathFamily replay observed) := by
    intro index
    apply subset_closure
    exact ⟨closure.weakClosure.subsequence index, rfl⟩
  rcases
      (wholeRestartFiniteObservedPathFamily_isCompact_closure
        replay observed).tendsto_subseq observedSequenceMem with
    ⟨observedLimit, _observedLimitMem, refinement,
      refinementStrictMono, observedTendsto⟩
  let observedRowMap :
      BoundedContinuousFunction
          (Icc (0 : ℝ) (wholeRestartDuration contact))
          (FiniteObservedCoefficientState observed) →L[ℂ]
        BoundedContinuousFunction
          (Icc (0 : ℝ) (wholeRestartDuration contact))
          ComplexCoordinateVector :=
    (ContinuousLinearMap.proj coordinate).compLeftContinuousBounded
      (Icc (0 : ℝ) (wholeRestartDuration contact))
  let rowPath :
      BoundedContinuousFunction
        (Icc (0 : ℝ) (wholeRestartDuration contact))
        ComplexCoordinateVector :=
    observedRowMap observedLimit
  have observedValue_eq_actual :
      ∀ (index : ℕ)
        (time : Icc (0 : ℝ) (wholeRestartDuration contact)),
        observedRowMap (observedSequence index) time =
          (replay.current
            (closure.weakClosure.subsequence index)).trajectory
              time.1 wave := by
    intro index time
    rfl
  have observedRowTendsto :
      Tendsto
        (fun index =>
          observedRowMap (observedSequence (refinement index)))
        atTop (𝓝 rowPath) := by
    have mapped :=
      (observedRowMap.continuous.tendsto observedLimit).comp
        observedTendsto
    change
      Tendsto
        (observedRowMap ∘ observedSequence ∘ refinement)
        atTop (𝓝 rowPath)
    simpa only [rowPath] using mapped
  have observedRowSpaceTimeTendsto :
      Tendsto
        (fun index =>
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
            (observedRowMap (observedSequence (refinement index))))
        atTop
        (𝓝 ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (wholeRestartDuration contact)) ℂ) rowPath)) :=
    ((BoundedContinuousFunction.toLp 2
      (commonTimeMeasure
        (wholeRestartDuration contact)) ℂ).continuous.tendsto rowPath).comp
      observedRowTendsto
  have stateRefinedTendsto :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (replay.current
              (closure.weakClosure.subsequence
                (refinement index))).trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              ((replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).physical time timeMem).1))
        atTop (𝓝 closure.weakClosure.stateLimit) := by
    have refined :=
      closure.weakClosure.state_tendsto.comp
        refinementStrictMono.tendsto_atTop
    have pathEq :
        (fun index =>
          wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (replay.current
              (closure.weakClosure.subsequence
                (refinement index))).trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              ((replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).physical time timeMem).1)) =
          (fun index =>
            wholeRestartSpaceTimePath replay
              (closure.weakClosure.subsequence (refinement index))) := by
      funext index
      exact
        (wholeRestartSpaceTimePath_eq_wholeTrajectory replay
          (closure.weakClosure.subsequence (refinement index))).symm
    rw [pathEq]
    exact refined
  have fixedStateRefinedTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn fun time timeMem =>
                ((replay.current
                  (closure.weakClosure.subsequence
                    (refinement index))).physical time timeMem).1)))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit)) :=
    ((fixedWaveSpaceTimeRestriction
      (wholeRestartDuration contact) wave).continuous.tendsto
        closure.weakClosure.stateLimit).comp stateRefinedTendsto
  have observedRowSpaceTime_eq_fixedWave :
      ∀ index,
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
            (observedRowMap (observedSequence (refinement index))) =
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn fun time timeMem =>
                ((replay.current
                  (closure.weakClosure.subsequence
                    (refinement index))).physical time timeMem).1)) := by
    intro index
    apply MeasureTheory.Lp.ext
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (observedRowMap (observedSequence (refinement index)))
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        (wholeRestartDuration contact) wave
        (wholeTrajectorySpaceTimePath
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory
          (HasDerivAt.continuousOn fun time timeMem =>
            ((replay.current
              (closure.weakClosure.subsequence
                (refinement index))).physical time timeMem).1))
    have wholeAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory
          (HasDerivAt.continuousOn fun time timeMem =>
            ((replay.current
              (closure.weakClosure.subsequence
                (refinement index))).physical time timeMem).1))
    filter_upwards [rowAE, restrictionAE, wholeAE] with
      time rowEq restrictionEq wholeEq
    rw [rowEq, restrictionEq]
    have statePoint :
        (wholeTrajectorySpaceTimePath
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory
          (HasDerivAt.continuousOn fun actual actualMem =>
            ((replay.current
              (closure.weakClosure.subsequence
                (refinement index))).physical actual actualMem).1)) time =
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory time.1 := by
      have statePoint' :
          (wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (replay.current
              (closure.weakClosure.subsequence
                (refinement index))).trajectory
            (HasDerivAt.continuousOn fun actual actualMem =>
              ((replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).physical actual actualMem).1)) time =
            wholeTrajectoryBoundedPath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn fun actual actualMem =>
                ((replay.current
                  (closure.weakClosure.subsequence
                    (refinement index))).physical actual actualMem).1) time := by
        simpa [wholeTrajectorySpaceTimePath] using wholeEq
      exact statePoint'.trans rfl
    rw [statePoint]
    exact observedValue_eq_actual (refinement index) time
  have observedAsFixedTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn fun time timeMem =>
                ((replay.current
                  (closure.weakClosure.subsequence
                    (refinement index))).physical time timeMem).1)))
        atTop
        (𝓝 ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (wholeRestartDuration contact)) ℂ) rowPath)) := by
    simpa only [observedRowSpaceTime_eq_fixedWave] using
      observedRowSpaceTimeTendsto
  have rowSpaceTimeEq :
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ) rowPath =
        fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit :=
    tendsto_nhds_unique observedAsFixedTendsto fixedStateRefinedTendsto
  have observedRowSpaceTime_eq_fixedWave_base :
      ∀ index,
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
            (observedRowMap (observedSequence index)) =
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence index)).trajectory
              (HasDerivAt.continuousOn fun time timeMem =>
                ((replay.current
                  (closure.weakClosure.subsequence index)).physical
                    time timeMem).1)) := by
    intro index
    apply MeasureTheory.Lp.ext
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (observedRowMap (observedSequence index))
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        (wholeRestartDuration contact) wave
        (wholeTrajectorySpaceTimePath
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence index)).trajectory
          (HasDerivAt.continuousOn fun time timeMem =>
            ((replay.current
              (closure.weakClosure.subsequence index)).physical
                time timeMem).1))
    have wholeAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence index)).trajectory
          (HasDerivAt.continuousOn fun time timeMem =>
            ((replay.current
              (closure.weakClosure.subsequence index)).physical
                time timeMem).1))
    filter_upwards [rowAE, restrictionAE, wholeAE] with
      time rowEq restrictionEq wholeEq
    rw [rowEq, restrictionEq]
    have statePoint :
        (wholeTrajectorySpaceTimePath
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence index)).trajectory
          (HasDerivAt.continuousOn fun actual actualMem =>
            ((replay.current
              (closure.weakClosure.subsequence index)).physical
                actual actualMem).1)) time =
          (replay.current
            (closure.weakClosure.subsequence index)).trajectory time.1 := by
      have statePoint' :
          (wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (replay.current
              (closure.weakClosure.subsequence index)).trajectory
            (HasDerivAt.continuousOn fun actual actualMem =>
              ((replay.current
                (closure.weakClosure.subsequence index)).physical
                  actual actualMem).1)) time =
            wholeTrajectoryBoundedPath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence index)).trajectory
              (HasDerivAt.continuousOn fun actual actualMem =>
                ((replay.current
                  (closure.weakClosure.subsequence index)).physical
                    actual actualMem).1) time := by
        simpa [wholeTrajectorySpaceTimePath] using wholeEq
      exact statePoint'.trans rfl
    rw [statePoint]
    exact observedValue_eq_actual index time
  have stateBaseTendsto :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (replay.current
              (closure.weakClosure.subsequence index)).trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              ((replay.current
                (closure.weakClosure.subsequence index)).physical
                  time timeMem).1))
        atTop (𝓝 closure.weakClosure.stateLimit) := by
    have pathEq :
        (fun index =>
          wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (replay.current
              (closure.weakClosure.subsequence index)).trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              ((replay.current
                (closure.weakClosure.subsequence index)).physical
                  time timeMem).1)) =
          (fun index => wholeRestartSpaceTimePath replay
            (closure.weakClosure.subsequence index)) := by
      funext index
      exact (wholeRestartSpaceTimePath_eq_wholeTrajectory replay
        (closure.weakClosure.subsequence index)).symm
    rw [pathEq]
    exact closure.weakClosure.state_tendsto
  have fixedStateBaseTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence index)).trajectory
              (HasDerivAt.continuousOn fun time timeMem =>
                ((replay.current
                  (closure.weakClosure.subsequence index)).physical
                    time timeMem).1)))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit)) :=
    ((fixedWaveSpaceTimeRestriction
      (wholeRestartDuration contact) wave).continuous.tendsto
        closure.weakClosure.stateLimit).comp stateBaseTendsto
  have observedRowSpaceTimeFullTendsto :
      Tendsto
        (fun index =>
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
            (observedRowMap (observedSequence index)))
        atTop
        (𝓝 ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (wholeRestartDuration contact)) ℂ) rowPath)) := by
    rw [rowSpaceTimeEq]
    simpa only [observedRowSpaceTime_eq_fixedWave_base] using
      fixedStateBaseTendsto
  have observedRowFullTendsto :
      Tendsto
        (fun index => observedRowMap (observedSequence index))
        atTop (𝓝 rowPath) := by
    let compactRows := observedRowMap ''
      _root_.closure
        (wholeRestartFiniteObservedPathFamily replay observed)
    have compactRowsCompact : IsCompact compactRows :=
      (wholeRestartFiniteObservedPathFamily_isCompact_closure
        replay observed).image observedRowMap.continuous
    have sequenceMem : ∀ index,
        observedRowMap (observedSequence index) ∈ compactRows := by
      intro index
      exact ⟨observedSequence index, observedSequenceMem index, rfl⟩
    let toLpMap :
        BoundedContinuousFunction
            (Icc (0 : ℝ) (wholeRestartDuration contact))
            ComplexCoordinateVector →L[ℂ]
          FixedWaveSpaceTimeState (wholeRestartDuration contact) :=
      BoundedContinuousFunction.toLp 2
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ
    apply tendsto_of_compact_of_continuous_injective_map_tendsto
      (fun index => observedRowMap (observedSequence index)) rowPath
      compactRows compactRowsCompact sequenceMem toLpMap
    · exact toLpMap.continuous
    · exact commonTimeBoundedContinuous_toLp_injective
        (wholeRestartDuration contact) (wholeRestartDuration_pos contact)
    · exact observedRowSpaceTimeFullTendsto
  have rowRepresents :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
        rowPath time =
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            closure.weakClosure.stateLimit time := by
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ rowPath
    rw [rowSpaceTimeEq] at rowAE
    exact rowAE.symm
  have combinedIndexTendsto :
      Tendsto
        (closure.weakClosure.subsequence ∘ refinement)
        atTop atTop :=
    closure.weakClosure.subsequence_strictMono.tendsto_atTop.comp
      refinementStrictMono.tendsto_atTop
  have initialRefinedTendsto :
      Tendsto
        (fun index =>
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory 0)
        atTop (𝓝 (wholeRestartPhysicalState contact)) := by
    have refined := replay.initial_tendsto.comp combinedIndexTendsto
    change
      Tendsto
        ((fun radius => (replay.current radius).trajectory 0) ∘
          closure.weakClosure.subsequence ∘ refinement)
        atTop (𝓝 (wholeRestartPhysicalState contact))
    exact refined
  have initialRowRefinedTendsto :
      Tendsto
        (fun index =>
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory 0 wave)
        atTop (𝓝 ((wholeRestartPhysicalState contact) wave)) :=
    (((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.tendsto (wholeRestartPhysicalState contact)).comp
        initialRefinedTendsto)
  let transverseStates :
      ℕ → TransverseSpaceTimeState (wholeRestartDuration contact) :=
    fun index =>
      wholeTransverseTrajectorySpaceTimePath
        (wholeRestartDuration contact)
        (replay.current
          (closure.weakClosure.subsequence index)).trajectory
        (fun time timeMem =>
          (((replay.current
            (closure.weakClosure.subsequence index)).physical
              time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          ((replay.current
            (closure.weakClosure.subsequence index)).physical
              time timeMem).2.2.1)
  have nonlinearRefinedTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeNonlinearRow
            (transverseStates (refinement index)) wave)
        atTop
        (𝓝 (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)) := by
    have base :=
      tendsto_transverseSpaceTimeNonlinearRow
        transverseStates closure.transverseLimit
        closure.transverse_tendsto wave
    exact base.comp refinementStrictMono.tendsto_atTop
  have mildIdentity :
      ∀ time : Icc (0 : ℝ) (wholeRestartDuration contact),
        rowPath time =
          fixedWaveHeatDuhamelValue
            (wholeRestartDuration contact) ν.coeff wave
            ((wholeRestartPhysicalState contact) wave)
            (transverseSpaceTimeNonlinearRow
              closure.transverseLimit wave) time := by
    intro time
    have observedValueTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) time)
          atTop (𝓝 (rowPath time)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ time).continuous.tendsto rowPath).comp observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ time) ∘
            (fun index =>
              observedRowMap (observedSequence (refinement index))))
          atTop (𝓝 (rowPath time))
      exact evaluated
    have duhamelTendsto :
        Tendsto
          (fun index =>
            fixedWaveHeatDuhamelValue
              (wholeRestartDuration contact) ν.coeff wave
              ((replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory 0 wave)
              (transverseSpaceTimeNonlinearRow
                (transverseStates (refinement index)) wave) time)
          atTop
          (𝓝 (fixedWaveHeatDuhamelValue
            (wholeRestartDuration contact) ν.coeff wave
            ((wholeRestartPhysicalState contact) wave)
            (transverseSpaceTimeNonlinearRow
              closure.transverseLimit wave) time)) :=
      tendsto_fixedWaveHeatDuhamelValue
        (wholeRestartDuration contact) ν.coeff ν.coeff_pos.le wave time
        (fun index =>
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory 0 wave)
        (fun index =>
          transverseSpaceTimeNonlinearRow
            (transverseStates (refinement index)) wave)
        ((wholeRestartPhysicalState contact) wave)
        (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)
        initialRowRefinedTendsto nonlinearRefinedTendsto
    have retainedEventually :
        ∀ᶠ index : ℕ in atTop,
          wave ∈ wholeRestartModes
            (closure.weakClosure.subsequence (refinement index)) :=
      combinedIndexTendsto
        (nonzero_integerWave_eventually_mem_puncturedFrequencyCube
          wave waveNonzero)
    have finiteMildEventually :
        (fun index =>
          observedRowMap
            (observedSequence (refinement index)) time) =ᶠ[atTop]
          (fun index =>
            fixedWaveHeatDuhamelValue
              (wholeRestartDuration contact) ν.coeff wave
              ((replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory 0 wave)
              (transverseSpaceTimeNonlinearRow
                (transverseStates (refinement index)) wave) time) := by
      filter_upwards [retainedEventually] with index waveMem
      rw [observedValue_eq_actual (refinement index) time]
      let stage :=
        replay.current
          (closure.weakClosure.subsequence (refinement index))
      have actual :=
        finiteSupportWave_eq_fixedWaveHeatDuhamelValue
          (wholeRestartModes
            (closure.weakClosure.subsequence (refinement index)))
          wave waveMem ν.coeff (wholeRestartDuration contact)
          (wholeRestartDuration_pos contact) stage.trajectory
          (fun actual actualMem =>
            (stage.physical actual actualMem).1)
          (fun actual actualMem =>
            (stage.physical actual actualMem).2.1)
          (fun actual actualMem =>
            (stage.physical actual actualMem).2.2.1)
          time
      have rowEq :
          transverseSpaceTimeNonlinearRow
              (transverseStates (refinement index)) wave =
            wholeNonlinearRowSpaceTimePath
              (wholeRestartDuration contact)
              (replay.current
                (closure.weakClosure.subsequence
                  (refinement index))).trajectory
              (fun actual actualMem =>
                (((replay.current
                  (closure.weakClosure.subsequence
                    (refinement index))).physical
                      actual actualMem).1).continuousAt.continuousWithinAt)
              (fun actual actualMem =>
                ((replay.current
                  (closure.weakClosure.subsequence
                    (refinement index))).physical
                      actual actualMem).2.2.1)
              wave := by
        exact transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory
          (wholeRestartDuration contact)
          (replay.current
            (closure.weakClosure.subsequence
              (refinement index))).trajectory
          (fun actual actualMem =>
            (((replay.current
              (closure.weakClosure.subsequence
                (refinement index))).physical
                  actual actualMem).1).continuousAt.continuousWithinAt)
          (fun actual actualMem =>
            ((replay.current
              (closure.weakClosure.subsequence
                (refinement index))).physical
                  actual actualMem).2.2.1)
          wave
      rw [rowEq]
      simpa only [stage] using actual
    exact
      tendsto_nhds_unique observedValueTendsto
        (duhamelTendsto.congr' finiteMildEventually.symm)
  have rowIncrementSqLe :
      ∀ first second :
          Icc (0 : ℝ) (wholeRestartDuration contact),
        dist (rowPath first) (rowPath second) ^ 2 ≤
          dist first second *
            wholeRestartFiniteObservedHalfHolderEnergy replay observed := by
    intro first second
    have firstTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) first)
          atTop (𝓝 (rowPath first)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ first).continuous.tendsto rowPath).comp observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ first) ∘
            (fun index =>
              observedRowMap
                (observedSequence (refinement index))))
          atTop (𝓝 (rowPath first))
      exact evaluated
    have secondTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) second)
          atTop (𝓝 (rowPath second)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ second).continuous.tendsto rowPath).comp observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ second) ∘
            (fun index =>
              observedRowMap
                (observedSequence (refinement index))))
          atTop (𝓝 (rowPath second))
      exact evaluated
    have incrementTendsto :
        Tendsto
          (fun index =>
            dist
                (observedRowMap
                  (observedSequence (refinement index)) first)
                (observedRowMap
                  (observedSequence (refinement index)) second) ^ 2)
          atTop
          (𝓝 (dist (rowPath first) (rowPath second) ^ 2)) :=
      (firstTendsto.dist secondTendsto).pow 2
    apply le_of_tendsto' incrementTendsto
    intro index
    have firstEq :
        observedRowMap
            (observedSequence (refinement index)) first =
          wholeRestartFiniteObservedTrajectory replay observed
              (closure.weakClosure.subsequence (refinement index))
              first coordinate := by
      rfl
    have secondEq :
        observedRowMap
            (observedSequence (refinement index)) second =
          wholeRestartFiniteObservedTrajectory replay observed
              (closure.weakClosure.subsequence (refinement index))
              second coordinate := by
      rfl
    rw [firstEq, secondEq]
    let firstState :=
      wholeRestartFiniteObservedTrajectory replay observed
        (closure.weakClosure.subsequence (refinement index)) first
    let secondState :=
      wholeRestartFiniteObservedTrajectory replay observed
        (closure.weakClosure.subsequence (refinement index)) second
    have coordinateDistLe :
        dist (firstState coordinate) (secondState coordinate) ≤
          dist firstState secondState := by
      rw [dist_eq_norm, dist_eq_norm]
      simpa only [Pi.sub_apply] using
        (norm_le_pi_norm (firstState - secondState) coordinate)
    exact
      ((sq_le_sq₀ dist_nonneg dist_nonneg).2 coordinateDistLe).trans
        (wholeRestartFiniteObservedTrajectory_increment_sq_le
          replay observed
          (closure.weakClosure.subsequence (refinement index))
          first second)
  have velocityRowIncrementLe :
      ∀ first second :
          Icc (0 : ℝ) (wholeRestartDuration contact),
        dist
            (biotSavartVelocityCoefficient wave (rowPath first))
            (biotSavartVelocityCoefficient wave (rowPath second)) ≤
          wholeRestartFixedWaveVelocitySpeedCeiling contact wave *
            dist first second := by
    intro first second
    have firstTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) first)
          atTop (𝓝 (rowPath first)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ first).continuous.tendsto rowPath).comp observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ first) ∘
            (fun index =>
              observedRowMap
                (observedSequence (refinement index))))
          atTop (𝓝 (rowPath first))
      exact evaluated
    have secondTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) second)
          atTop (𝓝 (rowPath second)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ second).continuous.tendsto rowPath).comp observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ second) ∘
            (fun index =>
              observedRowMap
                (observedSequence (refinement index))))
          atTop (𝓝 (rowPath second))
      exact evaluated
    have firstVelocityTendsto :
        Tendsto
          (fun index =>
            biotSavartVelocityCoefficient wave
              (observedRowMap
                (observedSequence (refinement index)) first))
          atTop
          (𝓝 (biotSavartVelocityCoefficient wave (rowPath first))) := by
      change
        Tendsto
          ((biotSavartVelocityCLM wave) ∘ fun index =>
            observedRowMap
              (observedSequence (refinement index)) first)
          atTop
          (𝓝 ((biotSavartVelocityCLM wave) (rowPath first)))
      exact ((biotSavartVelocityCLM wave).continuous.tendsto
        (rowPath first)).comp firstTendsto
    have secondVelocityTendsto :
        Tendsto
          (fun index =>
            biotSavartVelocityCoefficient wave
              (observedRowMap
                (observedSequence (refinement index)) second))
          atTop
          (𝓝 (biotSavartVelocityCoefficient wave (rowPath second))) := by
      change
        Tendsto
          ((biotSavartVelocityCLM wave) ∘ fun index =>
            observedRowMap
              (observedSequence (refinement index)) second)
          atTop
          (𝓝 ((biotSavartVelocityCLM wave) (rowPath second)))
      exact ((biotSavartVelocityCLM wave).continuous.tendsto
        (rowPath second)).comp secondTendsto
    have incrementTendsto :
        Tendsto
          (fun index =>
            dist
              (biotSavartVelocityCoefficient wave
                (observedRowMap
                  (observedSequence (refinement index)) first))
              (biotSavartVelocityCoefficient wave
                (observedRowMap
                  (observedSequence (refinement index)) second)))
          atTop
          (𝓝 (dist
            (biotSavartVelocityCoefficient wave (rowPath first))
            (biotSavartVelocityCoefficient wave (rowPath second)))) :=
      firstVelocityTendsto.dist secondVelocityTendsto
    apply le_of_tendsto' incrementTendsto
    intro index
    rw [observedValue_eq_actual (refinement index) first,
      observedValue_eq_actual (refinement index) second]
    exact canonicalStage_velocityWave_dist_le
      (replay.current
        (closure.weakClosure.subsequence (refinement index)))
      wave first second
  exact
    ⟨{
      mildData := {
        initialLimit := (wholeRestartPhysicalState contact)
        initial_tendsto := replay.initial_tendsto
        rowPath := rowPath
        row_represents := rowRepresents
        mild_identity := mildIdentity
      }
      refinement := refinement
      refinement_strictMono := refinementStrictMono
      row_tendsto := by
        simpa only [wholeRestartFixedWaveCanonicalBoundedPath,
          observed, coordinate, observedSequence, observedRowMap] using
          observedRowTendsto
      row_full_tendsto := by
        rw [show wholeRestartFixedWaveCanonicalBoundedPath closure wave =
            fun index => observedRowMap (observedSequence index) by
          funext index
          rfl]
        exact observedRowFullTendsto
      increment_sq_le := by
        intro first second
        simpa only [observed] using rowIncrementSqLe first second
      velocity_increment_le := velocityRowIncrementLe
    }⟩

/-- Compatibility projection for consumers that need only the continuous
mild row. -/
theorem GeneratedWholeRestartCriticalClosure.exists_fixedWaveContinuousMildData
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    Nonempty
      (FixedWaveContinuousMildData
        (wholeRestartDuration contact) ν.coeff wave
        (fun radius => (replay.current radius).trajectory 0)
        closure.weakClosure.stateLimit
        (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)) := by
  rcases
      GeneratedWholeRestartCriticalClosure.exists_fixedWaveContinuousMildHolderReceipt
        closure wave waveNonzero with
    ⟨generated⟩
  exact ⟨generated.mildData⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMildClosure
end NavierStokes
end SaturationMonoid
