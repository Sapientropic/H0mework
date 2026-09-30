import H0mework.NavierStokes.Restart.WeakClosure
import H0mework.NavierStokes.ShellSources.PointwiseMassLimit
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin
import H0mework.NavierStokes.Galerkin.KineticAmbientBound

/-!
# Critical whole-carrier closure of the generated restart replay

The actual canonical replay and its strong whole limit now transport the
remaining analytic responsibilities: transverse closure, the quadratic
nonlinear row, cutoff-free `L²_t H¹_x` gradient mass, and the almost-
everywhere coefficient-mass ceiling.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure

open scoped BigOperators ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

theorem GeneratedWholeRestartCanonicalStage.gradientDensity_finsetSum_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity
          (wholeRestartDuration contact)
          (wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact) stage.trajectory
            (HasDerivAt.continuousOn
              (fun time timeMem =>
                (stage.physical time timeMem).1)))
          wave) ≤
      wholeRestartGradientCeiling contact := by
  exact
    (wholeTrajectory_gradientDensity_finsetSum_le_enstrophyIntegral
      (wholeRestartDuration contact)
      (wholeRestartDuration_pos contact)
      (wholeRestartModes radius) waves ν.coeff stage.trajectory
      (fun time timeMem => (stage.physical time timeMem).1)
      (fun time timeMem => (stage.physical time timeMem).2.1)).trans
      (stage.uniformScalarBudget).2.1

theorem GeneratedWholeRestartCanonicalStage.euclideanMass_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    wholeVorticityEuclideanMass (stage.trajectory time.1) ≤
      wholeRestartCoefficientCeiling contact := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    (wholeRestartModes radius) (stage.trajectory time.1)
    (stage.physical time.1 time.2).2.1]
  exact (stage.uniformScalarBudget).1 time.1 time.2

/-- Every canonical unforced stage pays its complete kinetic-scale mass
from the exact whole restart state.  Finite support makes the whole mass
identical to twice the finite kinetic energy, so no Fourier responsibility
is lost in the finite ledger. -/
theorem GeneratedWholeRestartCanonicalStage.kineticMass_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    puncturedWholeVorticityKineticMass (stage.trajectory time.1) ≤
      puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) := by
  let modes := wholeRestartModes radius
  have zeroNotMem : 0 ∉ modes :=
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have negClosed : FiniteModeNegClosed modes :=
    fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have energyAntitone :=
    finiteStateVorticityKineticEnergy_antitoneOn
      modes zeroNotMem negClosed ν stage.trajectory
      0 (wholeRestartDuration contact)
      (fun actual actualMem => (stage.physical actual actualMem).1)
      (fun actual actualMem wave _waveMem =>
        (stage.physical actual actualMem).2.2.1 wave)
      (fun actual actualMem wave _waveMem =>
        (stage.physical actual actualMem).2.2.2 wave)
  have energyLe :
      finiteStateVorticityKineticEnergy modes
          (stage.trajectory time.1) ≤
        finiteStateVorticityKineticEnergy modes
          (stage.trajectory 0) :=
    energyAntitone
      ⟨le_rfl, (wholeRestartDuration_pos contact).le⟩
      time.2 time.2.1
  rw [puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy
    modes zeroNotMem (stage.trajectory time.1)
    (stage.physical time.1 time.2).2.1
    (fun wave waveMem =>
      (stage.physical time.1 time.2).2.2.1 wave)]
  calc
    2 * finiteStateVorticityKineticEnergy modes
          (stage.trajectory time.1) ≤
        2 * finiteStateVorticityKineticEnergy modes
          (stage.trajectory 0) :=
      mul_le_mul_of_nonneg_left energyLe (by norm_num)
    _ = 2 * finiteStateVorticityKineticEnergy modes
          (wholeRestartInitialState contact radius) := by
      rw [stage.initial]
    _ ≤ puncturedWholeVorticityKineticMass
          (wholeRestartInitialState contact radius) :=
      two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
        modes zeroNotMem (wholeRestartInitialState contact radius)
        (wholeRestartInitialState_transverse contact radius)
    _ ≤ puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) :=
      puncturedWholeVorticityKineticMass_sharpSupportProjection_le
        modes zeroNotMem (wholeRestartPhysicalState contact)

structure GeneratedWholeRestartCriticalClosure
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) where
  weakClosure : GeneratedWholeRestartWeakClosure replay
  transverseLimit :
    TransverseSpaceTimeState (wholeRestartDuration contact)
  inclusion_eq :
    transverseSpaceTimeInclusion
        (wholeRestartDuration contact) transverseLimit =
      weakClosure.stateLimit
  transverse_tendsto :
    Tendsto
      (fun index =>
        wholeTransverseTrajectorySpaceTimePath
          (wholeRestartDuration contact)
          (replay.current
            (weakClosure.subsequence index)).trajectory
          (fun time timeMem =>
            (((replay.current
              (weakClosure.subsequence index)).physical
                time timeMem).1).continuousAt.continuousWithinAt)
          (fun time timeMem =>
            ((replay.current
              (weakClosure.subsequence index)).physical
                time timeMem).2.2.1))
      atTop (𝓝 transverseLimit)
  weak_action :
    ∀ wave : IntegerWavevector, wave ≠ 0 →
      ∀ (test testDerivative : ℝ → ℂ),
        ∀ (testHasDeriv :
            ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
              HasDerivAt test (testDerivative time) time)
          (testDerivativeContinuous :
            ContinuousOn testDerivative
              (Icc (0 : ℝ) (wholeRestartDuration contact)))
          (_testZero : test 0 = 0)
          (_testTerminalZero :
            test (wholeRestartDuration contact) = 0),
        fixedWaveWeakAction
            (wholeRestartDuration contact) ν.coeff wave
            (restrictedScalarL2
              (wholeRestartDuration contact) test
              (fun time timeMem =>
                (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
            (restrictedScalarL2
              (wholeRestartDuration contact) testDerivative
              testDerivativeContinuous)
            (restrictedScalarLInf
              (wholeRestartDuration contact) test
              (fun time timeMem =>
                (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
            weakClosure.stateLimit
            (transverseSpaceTimeNonlinearRow transverseLimit wave) = 0
  gradient_summable :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          (wholeRestartDuration contact) weakClosure.stateLimit wave)
  gradient_mass_le :
    wholeSpaceTimeVorticityGradientMass
        (wholeRestartDuration contact) weakClosure.stateLimit ≤
      wholeRestartGradientCeiling contact
  coefficientMass_ae_le :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      wholeVorticityEuclideanMass (weakClosure.stateLimit time) ≤
        wholeRestartCoefficientCeiling contact
  kineticMass_ae_le :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      puncturedWholeVorticityKineticMass
          (weakClosure.stateLimit time) ≤
        puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact)

noncomputable def generatedWholeRestartCriticalClosure
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    GeneratedWholeRestartCriticalClosure replay := by
  let weakClosure := generatedWholeRestartWeakClosure replay
  let stateSequence :
      ℕ → SpaceTimeState (wholeRestartDuration contact) := fun index =>
    wholeTrajectorySpaceTimePath
      (wholeRestartDuration contact)
      (replay.current (weakClosure.subsequence index)).trajectory
      (HasDerivAt.continuousOn
        (fun time timeMem =>
          ((replay.current (weakClosure.subsequence index)).physical
            time timeMem).1))
  let transverseStates :
      ℕ → TransverseSpaceTimeState (wholeRestartDuration contact) :=
    fun index =>
      wholeTransverseTrajectorySpaceTimePath
        (wholeRestartDuration contact)
        (replay.current (weakClosure.subsequence index)).trajectory
        (fun time timeMem =>
          (((replay.current (weakClosure.subsequence index)).physical
            time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          ((replay.current (weakClosure.subsequence index)).physical
            time timeMem).2.2.1)
  have stateTendsto :
      Tendsto stateSequence atTop (𝓝 weakClosure.stateLimit) := by
    have pathEq :
        stateSequence =
          (fun index =>
            wholeRestartSpaceTimePath replay
              (weakClosure.subsequence index)) := by
      funext index
      exact
        (wholeRestartSpaceTimePath_eq_wholeTrajectory
          replay (weakClosure.subsequence index)).symm
    rw [pathEq]
    exact weakClosure.state_tendsto
  have includedTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion
            (wholeRestartDuration contact) (transverseStates index))
        atTop (𝓝 weakClosure.stateLimit) := by
    apply stateTendsto.congr
    intro index
    exact (transverseSpaceTimeInclusion_wholeTransverseTrajectory
      (wholeRestartDuration contact)
      (replay.current (weakClosure.subsequence index)).trajectory
      (fun time timeMem =>
        (((replay.current (weakClosure.subsequence index)).physical
          time timeMem).1).continuousAt.continuousWithinAt)
      (fun time timeMem =>
        ((replay.current (weakClosure.subsequence index)).physical
          time timeMem).2.2.1)).symm
  let transverseLimitResult :=
    transverseSpaceTime_limit_of_inclusion_tendsto
      (wholeRestartDuration contact) transverseStates
      weakClosure.stateLimit includedTendsto
  let transverseLimit :
      TransverseSpaceTimeState (wholeRestartDuration contact) :=
    Classical.choose transverseLimitResult
  have transverseLimitSpec := Classical.choose_spec transverseLimitResult
  have transverseTendsto := transverseLimitSpec.1
  have inclusionEq := transverseLimitSpec.2
  have finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            (wholeRestartDuration contact) (stateSequence index) wave) ≤
          wholeRestartGradientCeiling contact := by
    intro index waves
    simpa only [stateSequence] using
      GeneratedWholeRestartCanonicalStage.gradientDensity_finsetSum_le
        (replay.current (weakClosure.subsequence index)) waves
  have gradientSummable :
      Summable
        (fun wave : IntegerWavevector =>
          wholeSpaceTimeVorticityGradientDensity
            (wholeRestartDuration contact) weakClosure.stateLimit wave) :=
    summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
      (wholeRestartDuration contact) stateSequence weakClosure.stateLimit
      stateTendsto (wholeRestartGradientCeiling contact) finiteSumBound
  have gradientMassLe :
      wholeSpaceTimeVorticityGradientMass
          (wholeRestartDuration contact) weakClosure.stateLimit ≤
        wholeRestartGradientCeiling contact :=
    wholeSpaceTimeVorticityGradientMass_le_of_uniform_bound
      (wholeRestartDuration contact) stateSequence weakClosure.stateLimit
      stateTendsto (wholeRestartGradientCeiling contact) finiteSumBound
  have weakAction :
      ∀ wave : IntegerWavevector, wave ≠ 0 →
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
                HasDerivAt test (testDerivative time) time)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ) (wholeRestartDuration contact)))
            (testZero : test 0 = 0)
            (testTerminalZero :
              test (wholeRestartDuration contact) = 0),
          fixedWaveWeakAction
              (wholeRestartDuration contact) ν.coeff wave
              (restrictedScalarL2
                (wholeRestartDuration contact) test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                (wholeRestartDuration contact) testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                (wholeRestartDuration contact) test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              weakClosure.stateLimit
              (transverseSpaceTimeNonlinearRow transverseLimit wave) = 0 := by
    intro wave waveNonzero test testDerivative
      testHasDeriv testDerivativeContinuous testZero testTerminalZero
    rcases weakClosure.puncturedRow_weak wave waveNonzero with
      ⟨nonlinearLimit, nonlinearTendsto, allTests⟩
    have transverseRowTendsto :
        Tendsto
          (fun index =>
            transverseSpaceTimeNonlinearRow
              (transverseStates index) wave)
          atTop (𝓝 nonlinearLimit) := by
      apply nonlinearTendsto.congr
      intro index
      exact (transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory
        (wholeRestartDuration contact)
        (replay.current (weakClosure.subsequence index)).trajectory
        (fun time timeMem =>
          (((replay.current (weakClosure.subsequence index)).physical
            time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          ((replay.current (weakClosure.subsequence index)).physical
            time timeMem).2.2.1)
        wave).symm
    have generatedRowTendsto :
        Tendsto
          (fun index =>
            transverseSpaceTimeNonlinearRow
              (transverseStates index) wave)
          atTop
          (𝓝 (transverseSpaceTimeNonlinearRow transverseLimit wave)) :=
      tendsto_transverseSpaceTimeNonlinearRow
        transverseStates transverseLimit transverseTendsto wave
    have nonlinearEq :
        nonlinearLimit =
          transverseSpaceTimeNonlinearRow transverseLimit wave :=
      tendsto_nhds_unique transverseRowTendsto generatedRowTendsto
    simpa only [nonlinearEq] using
      allTests test testDerivative testHasDeriv
        testDerivativeContinuous testZero testTerminalZero
  have coefficientMassAE :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
        wholeVorticityEuclideanMass
            (weakClosure.stateLimit time) ≤
          wholeRestartCoefficientCeiling contact := by
    obtain
        ⟨pointwiseSubsequence, _pointwiseSubsequenceMono,
          pointwiseTendsto⟩ :=
      (tendstoInMeasure_of_tendsto_Lp stateTendsto).exists_seq_tendsto_ae
    have approximantBounds :
        ∀ index : ℕ,
          ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
            wholeVorticityEuclideanMass
                (stateSequence (pointwiseSubsequence index) time) ≤
              wholeRestartCoefficientCeiling contact := by
      intro index
      let stage := replay.current
        (weakClosure.subsequence (pointwiseSubsequence index))
      have coeFnEq :=
        BoundedContinuousFunction.coeFn_toLp
          (p := (2 : ℝ≥0∞))
          (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
          (wholeTrajectoryBoundedPath
            (wholeRestartDuration contact) stage.trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              (stage.physical time timeMem).1))
      filter_upwards [coeFnEq] with time timeEq
      change
        wholeVorticityEuclideanMass
            (((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
              (wholeTrajectoryBoundedPath
                (wholeRestartDuration contact) stage.trajectory
                (HasDerivAt.continuousOn fun actual actualMem =>
                  (stage.physical actual actualMem).1))) time) ≤
          wholeRestartCoefficientCeiling contact
      rw [timeEq]
      exact
        GeneratedWholeRestartCanonicalStage.euclideanMass_le stage time
    have allApproximantBounds :
        ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
          ∀ index : ℕ,
            wholeVorticityEuclideanMass
                (stateSequence (pointwiseSubsequence index) time) ≤
              wholeRestartCoefficientCeiling contact :=
      eventually_countable_forall.2 approximantBounds
    filter_upwards [pointwiseTendsto, allApproximantBounds] with
      time timeTendsto timeBounds
    apply le_of_tendsto (tendsto_wholeVorticityEuclideanMass timeTendsto)
    exact Filter.Eventually.of_forall timeBounds
  have kineticMassAE :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
        puncturedWholeVorticityKineticMass
            (weakClosure.stateLimit time) ≤
          puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) := by
    obtain
        ⟨pointwiseSubsequence, _pointwiseSubsequenceMono,
          pointwiseTendsto⟩ :=
      (tendstoInMeasure_of_tendsto_Lp stateTendsto).exists_seq_tendsto_ae
    have approximantBounds :
        ∀ index : ℕ,
          ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
            puncturedWholeVorticityKineticMass
                (stateSequence (pointwiseSubsequence index) time) ≤
              puncturedWholeVorticityKineticMass
                (wholeRestartPhysicalState contact) := by
      intro index
      let stage := replay.current
        (weakClosure.subsequence (pointwiseSubsequence index))
      have coeFnEq :=
        BoundedContinuousFunction.coeFn_toLp
          (p := (2 : ℝ≥0∞))
          (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
          (wholeTrajectoryBoundedPath
            (wholeRestartDuration contact) stage.trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              (stage.physical time timeMem).1))
      filter_upwards [coeFnEq] with time timeEq
      change
        puncturedWholeVorticityKineticMass
            (((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
              (wholeTrajectoryBoundedPath
                (wholeRestartDuration contact) stage.trajectory
                (HasDerivAt.continuousOn fun actual actualMem =>
                  (stage.physical actual actualMem).1))) time) ≤
          puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact)
      rw [timeEq]
      exact GeneratedWholeRestartCanonicalStage.kineticMass_le stage time
    have allApproximantBounds :
        ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
          ∀ index : ℕ,
            puncturedWholeVorticityKineticMass
                (stateSequence (pointwiseSubsequence index) time) ≤
              puncturedWholeVorticityKineticMass
                (wholeRestartPhysicalState contact) :=
      eventually_countable_forall.2 approximantBounds
    filter_upwards [pointwiseTendsto, allApproximantBounds] with
      time timeTendsto timeBounds
    apply le_of_tendsto
      (Filter.Tendsto.comp
        (continuous_puncturedWholeVorticityKineticMass).continuousAt
        timeTendsto)
    exact Filter.Eventually.of_forall timeBounds
  exact
    { weakClosure := weakClosure
      transverseLimit := transverseLimit
      inclusion_eq := inclusionEq
      transverse_tendsto := by
        simpa only [transverseStates] using transverseTendsto
      weak_action := weakAction
      gradient_summable := gradientSummable
      gradient_mass_le := gradientMassLe
      coefficientMass_ae_le := coefficientMassAE
      kineticMass_ae_le := kineticMassAE }

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
end NavierStokes
end SaturationMonoid
