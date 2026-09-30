import H0mework.NavierStokes.EndpointSettlement.GlobalWholeBlockKineticDissipation

/-!
# Exact kinetic dissipation of the generated whole restart

The canonical finite Galerkin replay carries an equality, not merely an
energy inequality.  Its initial sharp projections converge strongly to the
actual source state, while the selected replay subsequence converges strongly
on the whole space-time carrier and pointwise almost everywhere.  Therefore
the exact finite balance survives the same source-owned limit:

```text
kinetic mass at time + complete viscous payment before time
  = kinetic mass of the actual restart state.
```

No endpoint value, strong-trace certificate, cutoff, branch, energy identity,
or target trajectory is supplied by a caller.  The source-facing update uses
the contact time already selected by `nextContact`; intermediate transport
lemmas may read an arbitrary time of the generated receipt.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger

open scoped BigOperators ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap

noncomputable section

/-! ## Exact finite replay -/

/-- The exact Galerkin balance is retained against the literal projected
initial state, before the latter is relaxed to a whole-state upper bound. -/
theorem canonicalStage_kineticDissipation_eq_projected
    {nu : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed nu Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    puncturedWholeVorticityKineticMass (stage.trajectory time.1) +
        2 * nu.coeff *
          wholePrefixVorticityMass time
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact) stage.trajectory
              (HasDerivAt.continuousOn fun actual actualMem =>
                (stage.physical actual actualMem).1)) =
      puncturedWholeVorticityKineticMass
        (wholeRestartInitialState contact radius) := by
  let modes := wholeRestartModes radius
  have zeroNotMem : 0 ∉ modes :=
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have negClosed : FiniteModeNegClosed modes :=
    fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have kineticBalance :=
    finiteStateVorticityKineticEnergy_integral_generator
      modes zeroNotMem negClosed nu.coeff stage.trajectory
      0 time.1 time.2.1
      (fun actual actualMem =>
        (stage.physical actual
          ⟨actualMem.1, actualMem.2.trans time.2.2⟩).1)
      (fun actual actualMem wave _waveMem =>
        (stage.physical actual
          ⟨actualMem.1, actualMem.2.trans time.2.2⟩).2.2.1 wave)
      (fun actual actualMem wave _waveMem =>
        (stage.physical actual
          ⟨actualMem.1, actualMem.2.trans time.2.2⟩).2.2.2 wave)
  rw [intervalIntegral.integral_const_mul] at kineticBalance
  have prefixEq :
      wholePrefixVorticityMass time
          (wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact) stage.trajectory
            (HasDerivAt.continuousOn fun actual actualMem =>
              (stage.physical actual actualMem).1)) =
        ∫ actual in (0 : ℝ)..time.1,
          finiteStateVorticityMass modes (stage.trajectory actual) := by
    rw [
      wholePrefixVorticityMass_wholeTrajectorySpaceTimePath_eq_intervalIntegral]
    apply intervalIntegral.integral_congr
    intro actual actualMem
    have actualMemIcc : actual ∈ Icc (0 : ℝ) time.1 := by
      simpa [uIcc_of_le time.2.1] using actualMem
    change
      wholeVorticityEuclideanMass (stage.trajectory actual) =
        finiteStateVorticityMass modes (stage.trajectory actual)
    rw [wholeVorticityEuclideanMass_eq_finite_of_supported
      modes (stage.trajectory actual)
      ((stage.physical actual
        ⟨actualMemIcc.1, actualMemIcc.2.trans time.2.2⟩).2.1)]
    unfold finiteStateVorticityCoefficientEnstrophy
      finiteStateVorticityMass
    simp_rw [
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have terminalKineticEq :
      puncturedWholeVorticityKineticMass (stage.trajectory time.1) =
        2 * finiteStateVorticityKineticEnergy modes
          (stage.trajectory time.1) :=
    puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy
      modes zeroNotMem (stage.trajectory time.1)
      ((stage.physical time.1 time.2).2.1)
      (fun wave waveMem =>
        (stage.physical time.1 time.2).2.2.1 wave)
  have initialKineticEq :
      puncturedWholeVorticityKineticMass
          (wholeRestartInitialState contact radius) =
        2 * finiteStateVorticityKineticEnergy modes
          (stage.trajectory 0) := by
    rw [stage.initial]
    exact puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy
      modes zeroNotMem (wholeRestartInitialState contact radius)
      (wholeRestartInitialState_supported contact radius)
      (wholeRestartInitialState_transverse contact radius)
  rw [terminalKineticEq, prefixEq, initialKineticEq]
  linarith

/-- The same canonical prefix carries the terminal-mass rectangle generated
by the source-owned barrier.  This is a quantitative clock valuation, not a
regularity conclusion: the terminal mass still comes from the actual finite
trajectory. -/
theorem canonicalStage_terminalMass_sub_one_mul_time_le_prefix
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness.WholeContinuousMildSerrinReceipt
        nu initialState requestedTime}
    {contact :
      ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
        receipt}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    time.1 *
        (wholeVorticityEuclideanMass (stage.trajectory time.1) - 1) ≤
      wholePrefixVorticityMass time
        (wholeTrajectorySpaceTimePath
          (wholeRestartDuration contact) stage.trajectory
          (HasDerivAt.continuousOn fun actual actualMem ↦
            (stage.physical actual actualMem).1)) := by
  let modes := wholeRestartModes radius
  have finitePayment :=
    stage.terminal_sub_one_mul_time_le_integral time
  have terminalMassEq :
      wholeVorticityEuclideanMass (stage.trajectory time.1) =
        finiteStateVorticityCoefficientEnstrophy
          modes (stage.trajectory time.1) := by
    exact wholeVorticityEuclideanMass_eq_finite_of_supported
      modes (stage.trajectory time.1) (stage.physical time.1 time.2).2.1
  have prefixEq :
      wholePrefixVorticityMass time
          (wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact) stage.trajectory
            (HasDerivAt.continuousOn fun actual actualMem ↦
              (stage.physical actual actualMem).1)) =
        ∫ actual in (0 : ℝ)..time.1,
          finiteStateVorticityCoefficientEnstrophy
            modes (stage.trajectory actual) := by
    rw [
      wholePrefixVorticityMass_wholeTrajectorySpaceTimePath_eq_intervalIntegral]
    apply intervalIntegral.integral_congr
    intro actual actualMem
    have actualMemIcc : actual ∈ Icc (0 : ℝ) time.1 := by
      simpa [uIcc_of_le time.2.1] using actualMem
    change
      wholeVorticityEuclideanMass (stage.trajectory actual) =
        finiteStateVorticityCoefficientEnstrophy
          modes (stage.trajectory actual)
    exact wholeVorticityEuclideanMass_eq_finite_of_supported
      modes (stage.trajectory actual)
      ((stage.physical actual
        ⟨actualMemIcc.1, actualMemIcc.2.trans time.2.2⟩).2.1)
  rw [terminalMassEq, prefixEq]
  exact finitePayment

/-! ## Exact whole-carrier limit -/

/-- Strong space-time convergence, pointwise strong convergence on the same
subsequence, and strong convergence of the projected initial states preserve
the complete finite equality almost everywhere. -/
theorem criticalClosure_kineticDissipation_ae_eq
    {nu : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed nu Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      puncturedWholeVorticityKineticMass
            (closure.weakClosure.stateLimit time) +
          2 * nu.coeff *
            wholePrefixVorticityMass time
              closure.weakClosure.stateLimit =
        puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact) := by
  let weakClosure := closure.weakClosure
  let stateSequence :
      ℕ → SpaceTimeState (wholeRestartDuration contact) := fun index =>
    wholeTrajectorySpaceTimePath
      (wholeRestartDuration contact)
      (replay.current (weakClosure.subsequence index)).trajectory
      (HasDerivAt.continuousOn fun actual actualMem =>
        ((replay.current (weakClosure.subsequence index)).physical
          actual actualMem).1)
  have stateTendsto :
      Tendsto stateSequence atTop
        (𝓝 weakClosure.stateLimit) := by
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
  obtain
      ⟨pointwiseSubsequence, pointwiseSubsequenceMono,
        pointwiseTendsto⟩ :=
    (tendstoInMeasure_of_tendsto_Lp stateTendsto).exists_seq_tendsto_ae
  have approximantPathEq :
      ∀ index : ℕ,
        ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
          stateSequence (pointwiseSubsequence index) time =
            (replay.current
              (weakClosure.subsequence
                (pointwiseSubsequence index))).trajectory time.1 := by
    intro index
    let stage := replay.current
      (weakClosure.subsequence (pointwiseSubsequence index))
    have pathAE :=
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact) stage.trajectory
          (HasDerivAt.continuousOn fun actual actualMem =>
            (stage.physical actual actualMem).1))
    filter_upwards [pathAE] with time timeEq
    change
      (((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact) stage.trajectory
          (HasDerivAt.continuousOn fun actual actualMem =>
            (stage.physical actual actualMem).1))) time) =
        stage.trajectory time.1
    exact timeEq
  have allApproximantPathEq :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
        ∀ index : ℕ,
          stateSequence (pointwiseSubsequence index) time =
            (replay.current
              (weakClosure.subsequence
                (pointwiseSubsequence index))).trajectory time.1 :=
    eventually_countable_forall.2 approximantPathEq
  filter_upwards [pointwiseTendsto, allApproximantPathEq] with
      time timeTendsto pathEq
  have prefixTendsto :
      Tendsto
        (fun index =>
          wholePrefixVorticityMass time
            (stateSequence (pointwiseSubsequence index)))
        atTop
        (𝓝 (wholePrefixVorticityMass time weakClosure.stateLimit)) :=
    tendsto_wholePrefixVorticityMass time
      (stateTendsto.comp pointwiseSubsequenceMono.tendsto_atTop)
  have kineticTendsto :
      Tendsto
        (fun index =>
          puncturedWholeVorticityKineticMass
            (stateSequence (pointwiseSubsequence index) time))
        atTop
        (𝓝 (puncturedWholeVorticityKineticMass
          (weakClosure.stateLimit time))) :=
    Filter.Tendsto.comp
      continuous_puncturedWholeVorticityKineticMass.continuousAt
      timeTendsto
  have paymentTendsto :
      Tendsto
        (fun index =>
          puncturedWholeVorticityKineticMass
              (stateSequence (pointwiseSubsequence index) time) +
            2 * nu.coeff *
              wholePrefixVorticityMass time
                (stateSequence (pointwiseSubsequence index)))
        atTop
        (𝓝
          (puncturedWholeVorticityKineticMass
              (weakClosure.stateLimit time) +
            2 * nu.coeff *
              wholePrefixVorticityMass time weakClosure.stateLimit)) :=
    kineticTendsto.add (tendsto_const_nhds.mul prefixTendsto)
  have initialStateTendsto :
      Tendsto
        (fun index =>
          (replay.current
            (weakClosure.subsequence
              (pointwiseSubsequence index))).trajectory 0)
        atTop
        (𝓝 (wholeRestartPhysicalState contact)) :=
    replay.initial_tendsto.comp
      ((weakClosure.subsequence_strictMono.comp
        pointwiseSubsequenceMono).tendsto_atTop)
  have initialKineticTendsto :
      Tendsto
        (fun index =>
          puncturedWholeVorticityKineticMass
            ((replay.current
              (weakClosure.subsequence
                (pointwiseSubsequence index))).trajectory 0))
        atTop
        (𝓝 (puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact))) :=
    continuous_puncturedWholeVorticityKineticMass.continuousAt.tendsto.comp
      initialStateTendsto
  have paymentTendstoInitial :
      Tendsto
        (fun index =>
          puncturedWholeVorticityKineticMass
              (stateSequence (pointwiseSubsequence index) time) +
            2 * nu.coeff *
              wholePrefixVorticityMass time
                (stateSequence (pointwiseSubsequence index)))
        atTop
        (𝓝 (puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact))) := by
    apply initialKineticTendsto.congr'
    exact Filter.Eventually.of_forall fun index => by
      let stage := replay.current
        (weakClosure.subsequence (pointwiseSubsequence index))
      change
        puncturedWholeVorticityKineticMass (stage.trajectory 0) =
          puncturedWholeVorticityKineticMass
              (stateSequence (pointwiseSubsequence index) time) +
            2 * nu.coeff *
              wholePrefixVorticityMass time
                (stateSequence (pointwiseSubsequence index))
      rw [stage.initial, pathEq index]
      change
        puncturedWholeVorticityKineticMass
            (wholeRestartInitialState contact
              (weakClosure.subsequence (pointwiseSubsequence index))) =
          puncturedWholeVorticityKineticMass (stage.trajectory time.1) +
            2 * nu.coeff *
              wholePrefixVorticityMass time
                (wholeTrajectorySpaceTimePath
                  (wholeRestartDuration contact) stage.trajectory
                  (HasDerivAt.continuousOn fun actual actualMem =>
                    (stage.physical actual actualMem).1))
      exact
        (canonicalStage_kineticDissipation_eq_projected
          stage time).symm
  exact tendsto_nhds_unique paymentTendsto paymentTendstoInitial

/-- Strong pointwise convergence at the same almost-everywhere occurrence
and strong space-time convergence preserve the finite terminal-mass
rectangle.  Both sides remain indexed by one physical time of one closure. -/
theorem criticalClosure_terminalMass_sub_one_mul_time_le_prefix_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness.WholeContinuousMildSerrinReceipt
        nu initialState requestedTime}
    {contact :
      ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
        receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      time.1 *
          (wholeVorticityEuclideanMass
              (closure.weakClosure.stateLimit time) - 1) ≤
        wholePrefixVorticityMass time closure.weakClosure.stateLimit := by
  let weakClosure := closure.weakClosure
  let stateSequence :
      ℕ → SpaceTimeState (wholeRestartDuration contact) := fun index ↦
    wholeTrajectorySpaceTimePath
      (wholeRestartDuration contact)
      (replay.current (weakClosure.subsequence index)).trajectory
      (HasDerivAt.continuousOn fun actual actualMem ↦
        ((replay.current (weakClosure.subsequence index)).physical
          actual actualMem).1)
  have stateTendsto :
      Tendsto stateSequence atTop (𝓝 weakClosure.stateLimit) := by
    have pathEq :
        stateSequence =
          (fun index ↦
            wholeRestartSpaceTimePath replay
              (weakClosure.subsequence index)) := by
      funext index
      exact
        (wholeRestartSpaceTimePath_eq_wholeTrajectory
          replay (weakClosure.subsequence index)).symm
    rw [pathEq]
    exact weakClosure.state_tendsto
  obtain
      ⟨pointwiseSubsequence, pointwiseSubsequenceMono,
        pointwiseTendsto⟩ :=
    (tendstoInMeasure_of_tendsto_Lp stateTendsto).exists_seq_tendsto_ae
  have approximantPathEq :
      ∀ index : ℕ,
        ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
          stateSequence (pointwiseSubsequence index) time =
            (replay.current
              (weakClosure.subsequence
                (pointwiseSubsequence index))).trajectory time.1 := by
    intro index
    let stage := replay.current
      (weakClosure.subsequence (pointwiseSubsequence index))
    have pathAE :=
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact) stage.trajectory
          (HasDerivAt.continuousOn fun actual actualMem ↦
            (stage.physical actual actualMem).1))
    filter_upwards [pathAE] with time timeEq
    change
      (((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact) stage.trajectory
          (HasDerivAt.continuousOn fun actual actualMem ↦
            (stage.physical actual actualMem).1))) time) =
        stage.trajectory time.1
    exact timeEq
  have allApproximantPathEq :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
        ∀ index : ℕ,
          stateSequence (pointwiseSubsequence index) time =
            (replay.current
              (weakClosure.subsequence
                (pointwiseSubsequence index))).trajectory time.1 :=
    eventually_countable_forall.2 approximantPathEq
  filter_upwards [pointwiseTendsto, allApproximantPathEq] with
      time timeTendsto pathEq
  have prefixTendsto :
      Tendsto
        (fun index ↦
          wholePrefixVorticityMass time
            (stateSequence (pointwiseSubsequence index)))
        atTop
        (𝓝 (wholePrefixVorticityMass time weakClosure.stateLimit)) :=
    tendsto_wholePrefixVorticityMass time
      (stateTendsto.comp pointwiseSubsequenceMono.tendsto_atTop)
  have massTendsto :
      Tendsto
        (fun index ↦
          wholeVorticityEuclideanMass
            (stateSequence (pointwiseSubsequence index) time))
        atTop
        (𝓝 (wholeVorticityEuclideanMass
          (weakClosure.stateLimit time))) :=
    tendsto_wholeVorticityEuclideanMass timeTendsto
  have valuedTendsto :
      Tendsto
        (fun index ↦
          time.1 *
            (wholeVorticityEuclideanMass
                (stateSequence (pointwiseSubsequence index) time) - 1))
        atTop
        (𝓝 (time.1 *
          (wholeVorticityEuclideanMass
              (weakClosure.stateLimit time) - 1))) :=
    tendsto_const_nhds.mul (massTendsto.sub_const 1)
  apply le_of_tendsto_of_tendsto' valuedTendsto prefixTendsto
  intro index
  let stage := replay.current
    (weakClosure.subsequence (pointwiseSubsequence index))
  rw [pathEq index]
  change
    time.1 *
        (wholeVorticityEuclideanMass (stage.trajectory time.1) - 1) ≤
      wholePrefixVorticityMass time
        (wholeTrajectorySpaceTimePath
          (wholeRestartDuration contact) stage.trajectory
          (HasDerivAt.continuousOn fun actual actualMem ↦
            (stage.physical actual actualMem).1))
  exact canonicalStage_terminalMass_sub_one_mul_time_le_prefix
    stage time

/-! ## Every physical time of the generated receipt -/

/-- The generated receipt reads the exact whole-carrier balance on its
continuous physical path almost everywhere. -/
theorem
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_ae_eq
    {nu : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed nu Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      puncturedWholeVorticityKineticMass
            ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
              time) +
          2 * nu.coeff *
            wholePrefixVorticityMass time
              (generatedWholeRestartWholeContinuousMildSerrinReceipt
                replay).stateLimit =
        puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact) := by
  let closure := generatedWholeRestartCriticalClosure replay
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  have ledgerAE := criticalClosure_kineticDissipation_ae_eq closure
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      nextReceipt.wholePath
  filter_upwards [ledgerAE, pathAE] with time ledgerEq pathEq
  have pathEqState :
      nextReceipt.wholePath time = nextReceipt.stateLimit time := by
    rw [← nextReceipt.wholePath_toLp_eq_stateLimit]
    exact pathEq.symm
  change
    puncturedWholeVorticityKineticMass (nextReceipt.stateLimit time) +
          2 * nu.coeff *
            wholePrefixVorticityMass time nextReceipt.stateLimit =
        puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact) at ledgerEq
  rw [← pathEqState] at ledgerEq
  exact ledgerEq

/-- The generated whole receipt inherits the terminal-mass rectangle almost
everywhere on its physical path. -/
theorem
    generatedWholeRestartWholeContinuousMildSerrinReceipt_terminalMass_sub_one_mul_time_le_prefix_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness.WholeContinuousMildSerrinReceipt
        nu initialState requestedTime}
    {contact :
      ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
        receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      time.1 *
          (wholeVorticityEuclideanMass
              ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
                ).wholePath time) - 1) ≤
        wholePrefixVorticityMass time
          (generatedWholeRestartWholeContinuousMildSerrinReceipt
            replay).stateLimit := by
  let closure := generatedWholeRestartCriticalClosure replay
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  have rectangleAE :=
    criticalClosure_terminalMass_sub_one_mul_time_le_prefix_ae closure
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      nextReceipt.wholePath
  filter_upwards [rectangleAE, pathAE] with time rectangle pathEq
  have pathEqState :
      nextReceipt.wholePath time = nextReceipt.stateLimit time := by
    rw [← nextReceipt.wholePath_toLp_eq_stateLimit]
    exact pathEq.symm
  change
    time.1 *
        (wholeVorticityEuclideanMass
            (closure.weakClosure.stateLimit time) - 1) ≤
      wholePrefixVorticityMass time closure.weakClosure.stateLimit at rectangle
  change
    time.1 *
        (wholeVorticityEuclideanMass (nextReceipt.wholePath time) - 1) ≤
      wholePrefixVorticityMass time nextReceipt.stateLimit
  rw [pathEqState]
  exact rectangle

private theorem commonTimeMeasure_eq_comap_volume_exactKinetic
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

/-- Continuity removes the almost-everywhere presentation of the
terminal-mass rectangle.  It therefore applies to the already selected
contact without refining or replacing that contact. -/
theorem
    generatedWholeRestartWholeContinuousMildSerrinReceipt_terminalMass_sub_one_mul_time_le_prefix
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness.WholeContinuousMildSerrinReceipt
        nu initialState requestedTime}
    {contact :
      ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
        receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    time.1 *
        (wholeVorticityEuclideanMass
            ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
              ).wholePath time) - 1) ≤
      wholePrefixVorticityMass time
        (generatedWholeRestartWholeContinuousMildSerrinReceipt
          replay).stateLimit := by
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  let trajectory : ℝ → ComplexVorticityHilbertState :=
    wholeRestartReceiptPhysicalTrajectory nextReceipt
  let massIntegrand : ℝ → ℝ := fun actual ↦
    wholeVorticityEuclideanMass (trajectory actual)
  let left : ℝ → ℝ := fun actual ↦
    actual * (massIntegrand actual - 1)
  let right : ℝ → ℝ := fun actual ↦
    ∫ earlier in (0 : ℝ)..actual, massIntegrand earlier
  have trajectoryContinuous : Continuous trajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous nextReceipt
  have massIntegrandContinuous : Continuous massIntegrand := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact tendsto_wholeVorticityEuclideanMass
      trajectoryContinuous.continuousAt
  have massIntegrandIntegrable :
      IntegrableOn massIntegrand
        (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
    massIntegrandContinuous.continuousOn.integrableOn_Icc
  have rightContinuous :
      ContinuousOn right
        (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
    have onUnordered :
        ContinuousOn
          (fun actual ↦
            ∫ earlier in (0 : ℝ)..actual, massIntegrand earlier)
          (uIcc (0 : ℝ) (wholeRestartDuration contact)) :=
      intervalIntegral.continuousOn_primitive_interval
        (by
          simpa [uIcc_of_le (wholeRestartDuration_pos contact).le] using
            massIntegrandIntegrable)
    simpa [right, uIcc_of_le (wholeRestartDuration_pos contact).le] using
      onUnordered
  have leftContinuous :
      ContinuousOn left
        (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
    exact (continuous_id.mul
      (massIntegrandContinuous.sub continuous_const)).continuousOn
  have maxContinuous :
      ContinuousOn (fun actual ↦ max (left actual) (right actual))
        (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
    continuous_max.comp_continuousOn
      (leftContinuous.prodMk rightContinuous)
  have subtypeAE :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_terminalMass_sub_one_mul_time_le_prefix_ae
      replay
  rw [commonTimeMeasure_eq_comap_volume_exactKinetic] at subtypeAE
  have maxAE :
      (fun actual ↦ max (left actual) (right actual)) =ᵐ[
        volume.restrict
          (Icc (0 : ℝ) (wholeRestartDuration contact))]
        right := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [subtypeAE] with currentTime rectangle
    have trajectoryEq :
        trajectory currentTime.1 = nextReceipt.wholePath currentTime := by
      dsimp only [trajectory]
      rw [wholeRestartReceiptPhysicalTrajectory,
        projIcc_of_mem nextReceipt.requestedTimePos.le currentTime.property]
    have prefixEq :=
      wholePrefixVorticityMass_receipt_eq_intervalIntegral
        nextReceipt currentTime
    have valued : left currentTime.1 ≤ right currentTime.1 := by
      dsimp only [left, right, massIntegrand]
      rw [trajectoryEq]
      rw [← prefixEq]
      exact rectangle
    exact max_eq_right valued
  have maxOn :=
    Measure.eqOn_Icc_of_ae_eq
      (μ := volume)
      (wholeRestartDuration_pos contact).ne
      maxAE maxContinuous rightContinuous
  have atTime := maxOn time.property
  have valued : left time.1 ≤ right time.1 := by
    calc
      left time.1 ≤ max (left time.1) (right time.1) := le_max_left _ _
      _ = right time.1 := atTime
  have trajectoryEq : trajectory time.1 = nextReceipt.wholePath time := by
    dsimp only [trajectory]
    rw [wholeRestartReceiptPhysicalTrajectory,
      projIcc_of_mem nextReceipt.requestedTimePos.le time.property]
  have prefixEq :=
    wholePrefixVorticityMass_receipt_eq_intervalIntegral nextReceipt time
  change
    time.1 *
        (wholeVorticityEuclideanMass (nextReceipt.wholePath time) - 1) ≤
      wholePrefixVorticityMass time nextReceipt.stateLimit
  rw [prefixEq]
  simpa only [left, right, massIntegrand, trajectoryEq] using valued

/-- Continuity of the generated whole path and of its cumulative physical
payment upgrades the almost-everywhere equality to every actual physical
time.  In particular it applies to the contact selected by the source
producer without changing that producer's choice. -/
theorem
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_eq
    {nu : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed nu Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    puncturedWholeVorticityKineticMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
            time) +
        2 * nu.coeff *
          wholePrefixVorticityMass time
            (generatedWholeRestartWholeContinuousMildSerrinReceipt
              replay).stateLimit =
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState contact) := by
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  let trajectory : ℝ → ComplexVorticityHilbertState :=
    wholeRestartReceiptPhysicalTrajectory nextReceipt
  let massIntegrand : ℝ → ℝ :=
    fun actual =>
      wholeVorticityEuclideanMass (trajectory actual)
  let ledger : ℝ → ℝ :=
    fun actual =>
      puncturedWholeVorticityKineticMass (trajectory actual) +
        2 * nu.coeff *
          (∫ earlier in (0 : ℝ)..actual, massIntegrand earlier)
  have trajectoryContinuous : Continuous trajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous nextReceipt
  have massIntegrandContinuous : Continuous massIntegrand := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact tendsto_wholeVorticityEuclideanMass
      trajectoryContinuous.continuousAt
  have massIntegrandIntegrable :
      IntegrableOn massIntegrand
        (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
    massIntegrandContinuous.continuousOn.integrableOn_Icc
  have primitiveContinuous :
      ContinuousOn
        (fun actual =>
          ∫ earlier in (0 : ℝ)..actual, massIntegrand earlier)
        (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
    have onUnordered :
        ContinuousOn
          (fun actual =>
            ∫ earlier in (0 : ℝ)..actual, massIntegrand earlier)
          (uIcc (0 : ℝ) (wholeRestartDuration contact)) :=
      intervalIntegral.continuousOn_primitive_interval
        (by
          simpa [uIcc_of_le (wholeRestartDuration_pos contact).le] using
            massIntegrandIntegrable)
    simpa [uIcc_of_le (wholeRestartDuration_pos contact).le] using
      onUnordered
  have ledgerContinuous :
      ContinuousOn ledger
        (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
    exact
      (continuous_puncturedWholeVorticityKineticMass.comp
        trajectoryContinuous).continuousOn.add
          (continuousOn_const.mul primitiveContinuous)
  have exactSubtypeAE :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_ae_eq
      replay
  rw [commonTimeMeasure_eq_comap_volume_exactKinetic] at exactSubtypeAE
  have ledgerAE :
      ledger =ᵐ[
        volume.restrict
          (Icc (0 : ℝ) (wholeRestartDuration contact))]
        fun _ =>
          puncturedWholeVorticityKineticMass
            (wholeRestartPhysicalState contact) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [exactSubtypeAE] with currentTime ledgerEq
    have trajectoryEq :
        trajectory currentTime.1 = nextReceipt.wholePath currentTime := by
      dsimp only [trajectory]
      rw [wholeRestartReceiptPhysicalTrajectory,
        projIcc_of_mem nextReceipt.requestedTimePos.le
          currentTime.property]
    have prefixEq :=
      wholePrefixVorticityMass_receipt_eq_intervalIntegral
        nextReceipt currentTime
    change
      ledger currentTime.1 =
        puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact)
    dsimp only [ledger]
    rw [trajectoryEq]
    change
      puncturedWholeVorticityKineticMass
            (nextReceipt.wholePath currentTime) +
          2 * nu.coeff *
            (∫ earlier in (0 : ℝ)..currentTime.1,
              wholeVorticityEuclideanMass
                (wholeRestartReceiptPhysicalTrajectory
                  nextReceipt earlier)) =
        puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState contact)
    rw [← prefixEq]
    exact ledgerEq
  have ledgerOn :=
    Measure.eqOn_Icc_of_ae_eq
      (μ := volume)
      (wholeRestartDuration_pos contact).ne
      ledgerAE ledgerContinuous continuousOn_const
  have atTime := ledgerOn time.property
  have trajectoryEq :
      trajectory time.1 = nextReceipt.wholePath time := by
    dsimp only [trajectory]
    rw [wholeRestartReceiptPhysicalTrajectory,
      projIcc_of_mem nextReceipt.requestedTimePos.le time.property]
  have prefixEq :=
    wholePrefixVorticityMass_receipt_eq_intervalIntegral
      nextReceipt time
  change
    puncturedWholeVorticityKineticMass
          (nextReceipt.wholePath time) +
        2 * nu.coeff *
          wholePrefixVorticityMass time nextReceipt.stateLimit =
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState contact)
  rw [prefixEq]
  change
    puncturedWholeVorticityKineticMass
          (nextReceipt.wholePath time) +
        2 * nu.coeff *
          (∫ earlier in (0 : ℝ)..time.1,
            massIntegrand earlier) =
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState contact)
  simpa only [ledger, trajectoryEq] using atTime

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
end NavierStokes
end SaturationMonoid

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-! ## Exact source-native update -/

/-- The source-selected next contact pays the exact kinetic decrease of the
same unforced receipt.  The contact time remains the one already generated
by `nextContact`; no refined chooser or energy certificate is introduced. -/
theorem GeneratedWholeRestartCurrent.nextContact_kineticDissipation_eq
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    puncturedWholeVorticityKineticMass
          current.nextContact.physicalState +
        2 * ν.coeff *
          wholePrefixVorticityMass current.nextContact.time
            current.nextReceipt.stateLimit =
      puncturedWholeVorticityKineticMass
        current.contact.physicalState := by
  let replay := generatedWholeRestartCanonicalReplay current.contact
  have exactLedger :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_eq
      replay current.nextContact.time
  change
    puncturedWholeVorticityKineticMass
          (current.nextReceipt.wholePath current.nextContact.time) +
        2 * ν.coeff *
          wholePrefixVorticityMass current.nextContact.time
            current.nextReceipt.stateLimit =
      puncturedWholeVorticityKineticMass
        current.contact.physicalState
  simpa only [GeneratedWholeRestartCurrent.nextReceipt,
    GeneratedWholeRestartCurrent.nextContact,
    wholeRestartPhysicalState_generatedPositiveWholeRestartContact,
    replay] using exactLedger

/-- The selected endpoint mass, physical clock and kinetic density are
valuations of the same generated edge. -/
theorem GeneratedWholeRestartCurrent.nextContact_terminalMass_sub_one_mul_time_le_prefix
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.nextContact.time.1 *
        (wholeVorticityEuclideanMass
            current.nextContact.physicalState - 1) ≤
      wholePrefixVorticityMass current.nextContact.time
        current.nextReceipt.stateLimit := by
  let replay := generatedWholeRestartCanonicalReplay current.contact
  have rectangle :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_terminalMass_sub_one_mul_time_le_prefix
      replay current.nextContact.time
  change
    current.nextContact.time.1 *
        (wholeVorticityEuclideanMass
            (current.nextReceipt.wholePath current.nextContact.time) - 1) ≤
      wholePrefixVorticityMass current.nextContact.time
        current.nextReceipt.stateLimit
  simpa only [GeneratedWholeRestartCurrent.nextReceipt,
    GeneratedWholeRestartCurrent.nextContact,
    replay] using rectangle

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
end NavierStokes
end SaturationMonoid

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-- Every actual source-native edge satisfies the exact kinetic balance. -/
theorem run_contact_kineticDissipation_succ_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    puncturedWholeVorticityKineticMass
          (run initial (index + 1)).contact.physicalState +
        wholeRestartNextKineticDissipationPayment initial index =
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState := by
  rw [run_succ]
  change
    puncturedWholeVorticityKineticMass
          (run initial index).nextContact.physicalState +
        2 * ν.coeff *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit =
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState
  exact (run initial index).nextContact_kineticDissipation_eq

/-! ## Source-generated entropy/defect rigidity -/

/-- Kinetic entropy read directly from one source-generated whole-restart
current. -/
def wholeRestartKineticEntropy
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  puncturedWholeVorticityKineticMass
    (run initial index).contact.physicalState

/-- Actual viscous defect paid by the same native successor edge. -/
def wholeRestartKineticDefect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  wholeRestartNextKineticDissipationPayment initial index

/-- Canonical zero-defect state on the exact time prefix generated by the
successor occurrence. -/
def WholeRestartKineticCanonicalAt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : Prop :=
  restrictCommonTimeLpCLM
      (Tsmall := (run initial index).nextContact.time.1)
      (run initial index).nextContact.time.2.2
      (run initial index).nextReceipt.stateLimit = 0

/-- Perelman-shaped material certificate on one actual whole-restart edge.
The dynamics generates the entropy, exact dissipative balance, and its
zero-defect normal form together; no target state or entropy witness is an
input. -/
structure SourceGeneratedWholeRestartKineticEntropyDefectAt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : Prop where
  private mk ::
  balance :
    wholeRestartKineticEntropy initial (index + 1) +
        wholeRestartKineticDefect initial index =
      wholeRestartKineticEntropy initial index
  defect_nonneg : 0 ≤ wholeRestartKineticDefect initial index
  defect_zero_iff_canonical :
    wholeRestartKineticDefect initial index = 0 ↔
      WholeRestartKineticCanonicalAt initial index

/-- Canonical material revelation generated by the native restart run. -/
theorem sourceGeneratedWholeRestartKineticEntropyDefect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    SourceGeneratedWholeRestartKineticEntropyDefectAt initial index :=
  ⟨by
      simpa only [wholeRestartKineticEntropy, wholeRestartKineticDefect] using
        run_contact_kineticDissipation_succ_eq initial index,
    by
      simpa only [wholeRestartKineticDefect] using
        wholeRestartNextKineticDissipationPayment_nonneg initial index,
    by
      simpa only [wholeRestartKineticDefect,
        WholeRestartKineticCanonicalAt] using
        wholeRestartNextKineticDissipationPayment_eq_zero_iff initial index⟩

/-- Entropy is stationary on one actual edge exactly at the generated
canonical prefix.  This is the rigidity half of material revelation. -/
theorem wholeRestartKineticEntropy_succ_eq_iff_canonical
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartKineticEntropy initial (index + 1) =
        wholeRestartKineticEntropy initial index ↔
      WholeRestartKineticCanonicalAt initial index := by
  let generated :=
    sourceGeneratedWholeRestartKineticEntropyDefect initial index
  constructor
  · intro entropyEq
    apply generated.defect_zero_iff_canonical.mp
    linarith [generated.balance]
  · intro canonical
    have defectZero := generated.defect_zero_iff_canonical.mpr canonical
    linarith [generated.balance]

/-- Away from the generated canonical prefix, the actual kinetic entropy
strictly decreases. -/
theorem wholeRestartKineticEntropy_succ_lt_of_not_canonical
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (noncanonical : ¬ WholeRestartKineticCanonicalAt initial index) :
    wholeRestartKineticEntropy initial (index + 1) <
      wholeRestartKineticEntropy initial index := by
  let generated :=
    sourceGeneratedWholeRestartKineticEntropyDefect initial index
  have defectNe : wholeRestartKineticDefect initial index ≠ 0 :=
    fun defectZero => noncanonical
      (generated.defect_zero_iff_canonical.mp defectZero)
  have defectPos : 0 < wholeRestartKineticDefect initial index :=
    lt_of_le_of_ne generated.defect_nonneg (Ne.symm defectNe)
  linarith [generated.balance]

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
end NavierStokes
end SaturationMonoid

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators Topology

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

noncomputable section

/-! ## Exact consecutive blocks -/

/-- The complete physical payment on every consecutive source-native block
is an equality. -/
theorem run_contact_kineticMass_add_intervalDissipation_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start : ℕ) :
    ∀ steps : ℕ,
      puncturedWholeVorticityKineticMass
            (run initial (start + steps)).contact.physicalState +
          wholeRestartIntervalKineticDissipationPayment
            initial start steps =
        puncturedWholeVorticityKineticMass
          (run initial start).contact.physicalState
  | 0 => by
      simp [wholeRestartIntervalKineticDissipationPayment]
  | Nat.succ steps => by
      have finalStep :=
        run_contact_kineticDissipation_succ_eq
          initial (start + steps)
      have prefixEq :=
        run_contact_kineticMass_add_intervalDissipation_eq
          initial start steps
      unfold wholeRestartIntervalKineticDissipationPayment at prefixEq ⊢
      rw [Finset.sum_range_succ]
      calc
        puncturedWholeVorticityKineticMass
              (run initial (start + (steps + 1))).contact.physicalState +
            ((∑ offset ∈ Finset.range steps,
                wholeRestartNextKineticDissipationPayment
                  initial (start + offset)) +
              wholeRestartNextKineticDissipationPayment
                initial (start + steps)) =
            (puncturedWholeVorticityKineticMass
                (run initial ((start + steps) + 1)).contact.physicalState +
              wholeRestartNextKineticDissipationPayment
                initial (start + steps)) +
              ∑ offset ∈ Finset.range steps,
                wholeRestartNextKineticDissipationPayment
                  initial (start + offset) := by
          rw [← Nat.add_assoc start steps 1]
          ring
        _ =
            puncturedWholeVorticityKineticMass
                (run initial (start + steps)).contact.physicalState +
              ∑ offset ∈ Finset.range steps,
                wholeRestartNextKineticDissipationPayment
                  initial (start + offset) := by
          rw [finalStep]
        _ =
            puncturedWholeVorticityKineticMass
              (run initial start).contact.physicalState :=
          prefixEq

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-! ## Exact whole action -/

/-- One adjacent source-generated scale block pays exactly its physical
kinetic decrease on the authoritative global path. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.globalPathKineticDissipation_eq
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence (node + 1)))‖ ^ 2 +
        action.blockKineticDissipationPayment node =
      ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence node))‖ ^ 2 := by
  rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
    lineage.globalAbsoluteVelocityTrajectory_actualContact,
    wholeRestartContactVelocityState_norm_sq,
    wholeRestartContactVelocityState_norm_sq]
  have paid :=
    run_contact_kineticMass_add_intervalDissipation_eq
      (lineage.current stage)
      (action.scale.absoluteOccurrence node)
      (action.scale.nextScaleGap node)
  rw [action.scale.absoluteOccurrence_add_nextScaleGap node] at paid
  simpa only [
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPayment]
    using paid

/-- The native block write-square and its actual viscous payment are exactly
the negative of twice the incoming physical work. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.nativeSquare_add_dissipation_eq_neg_two_work
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    action.scale.wholeBlockNativeVelocitySquare node +
        action.blockKineticDissipationPayment node =
      -2 * action.scale.wholeBlockIncomingVelocityWork node := by
  have paid := action.globalPathKineticDissipation_eq node
  have boundary := action.kinetic_boundary node
  linarith

/-- The complete pre-quotient component boundary and the actual viscous
payment of the same block cancel exactly. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.componentBoundary_add_dissipation_eq_zero
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (node : ℕ) :
    action.scale.wholeBlockComponentKineticBoundary node +
        action.blockKineticDissipationPayment node = 0 := by
  have paid := action.globalPathKineticDissipation_eq node
  have boundary := action.component_boundary node
  linarith

/-- Every finite whole-action prefix is settled exactly, before any endpoint
completion quotient. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.componentBoundaryPrefix_add_dissipation_eq_zero
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (length : ℕ) :
    (∑ node ∈ Finset.range length,
        action.scale.wholeBlockComponentKineticBoundary node) +
        action.blockKineticDissipationPrefix length = 0 := by
  have settled :=
    Finset.sum_congr rfl fun node
      (_nodeMem : node ∈ Finset.range length) =>
        action.componentBoundary_add_dissipation_eq_zero node
  rw [Finset.sum_add_distrib] at settled
  simpa only [
    WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix,
    Finset.sum_const_zero] using settled

/-- Exact finite-prefix kinetic ledger on the single global path. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.globalPathEnergy_add_dissipationPrefix_eq_initial
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage)
    (length : ℕ) :
    ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence length))‖ ^ 2 +
        action.blockKineticDissipationPrefix length =
      ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence 0))‖ ^ 2 := by
  have settled :=
    action.componentBoundaryPrefix_add_dissipation_eq_zero length
  rw [action.componentBoundaryPrefix_eq_globalPathEnergyGap length]
    at settled
  linarith

/-- Passing the exact finite prefix ledger to the source-generated kinetic
mass limit leaves no hidden loss inside the old-run action. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.massLimit_add_totalBlockDissipation_eq_initial
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    wholeRestartKineticMassLimit (lineage.current stage) +
        ∑' node : ℕ, action.blockKineticDissipationPayment node =
      ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence 0))‖ ^ 2 := by
  have energyTendsto :=
    action.globalPathContactNormSq_tendsto_massLimit
  have paymentTendsto :
      Tendsto
        (fun length =>
          action.blockKineticDissipationPrefix length)
        atTop
        (𝓝 (∑' node : ℕ,
          action.blockKineticDissipationPayment node)) := by
    simpa only [
      WholeRestartReducedCoreGlobalWholeBlockAction.blockKineticDissipationPrefix]
      using
        action.summable_blockKineticDissipationPayment.hasSum.tendsto_sum_nat
  have exactTendsto :
      Tendsto
        (fun length =>
          ‖lineage.globalAbsoluteVelocityTrajectory
              (lineage.actualContactGlobalTime
                stage (action.scale.absoluteOccurrence length))‖ ^ 2 +
            action.blockKineticDissipationPrefix length)
        atTop
        (𝓝
          (wholeRestartKineticMassLimit (lineage.current stage) +
            ∑' node : ℕ,
              action.blockKineticDissipationPayment node)) :=
    energyTendsto.add paymentTendsto
  have constantTendsto :
      Tendsto
        (fun _ : ℕ =>
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence 0))‖ ^ 2)
        atTop
        (𝓝
          (‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence 0))‖ ^ 2)) :=
    tendsto_const_nhds
  have exactTendstoInitial :
      Tendsto
        (fun length =>
          ‖lineage.globalAbsoluteVelocityTrajectory
              (lineage.actualContactGlobalTime
                stage (action.scale.absoluteOccurrence length))‖ ^ 2 +
            action.blockKineticDissipationPrefix length)
        atTop
        (𝓝
          (‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (action.scale.absoluteOccurrence 0))‖ ^ 2)) := by
    apply constantTendsto.congr'
    exact Filter.Eventually.of_forall fun length =>
      (action.globalPathEnergy_add_dissipationPrefix_eq_initial
        length).symm
  exact tendsto_nhds_unique exactTendsto exactTendstoInitial

/-- Exact endpoint residual conservation for the entire source-generated
scale action.  All finite-block kinetic loss has been paid by the actual
viscous ledger; the only remaining responsibility is the already generated
kinetic completion atom at the accumulation interface. -/
theorem
    WholeRestartReducedCoreGlobalWholeBlockAction.endpointEnergy_add_stageDefect_add_totalBlockDissipation_eq_initial
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (action :
      WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) :
    ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.globalStageAccumulationTime stage)‖ ^ 2 +
          infiniteEndpointMacroStageKineticDefect lineage stage +
        ∑' node : ℕ, action.blockKineticDissipationPayment node =
      ‖lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime
          stage (action.scale.absoluteOccurrence 0))‖ ^ 2 := by
  have exactTail :=
    action.massLimit_add_totalBlockDissipation_eq_initial
  have interfaceEq :
      lineage.globalAbsoluteVelocityTrajectory
          (lineage.globalStageAccumulationTime stage) =
        (lineage.step stage).physicalStage
          (lineage.step stage).physicalStageAccumulation := by
    rw [globalStageAccumulationTime]
    change
      lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock stage +
            (((lineage.step stage).physicalStageAccumulation :
              Icc (0 : ℝ) (lineage.step stage).clockAdvance) : ℝ)) =
        (lineage.step stage).physicalStage
          (lineage.step stage).physicalStageAccumulation
    exact lineage.globalAbsoluteVelocityTrajectory_eq_stage
      stage (lineage.step stage).physicalStageAccumulation
  have defectEq :
      infiniteEndpointMacroStageKineticDefect lineage stage =
        wholeRestartKineticMassLimit (lineage.current stage) -
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.globalStageAccumulationTime stage)‖ ^ 2 := by
    rw [infiniteEndpointMacroStageKineticDefect,
      ← (lineage.step stage).physicalStageKineticEnergyAtom_eq_defect,
      GeneratedWholeRestartEndpointMacroStep.physicalStageKineticEnergyAtom,
      interfaceEq]
  linarith

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
