import H0mework.NavierStokes.KineticRestart.KineticDissipationLedger
import H0mework.NavierStokes.Galerkin.CriticalSerrinBudget
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeGradientLowerSemicontinuity

/-!
# Critical gradient-dissipation ledger of the generated whole restart

The actual canonical Galerkin stages start from sharp projections of one
source-owned whole state.  Whenever that whole state lies below the fixed
half-critical threshold, the ordinary finite-dimensional enstrophy identity
therefore yields a cutoff-independent payment on every actual prefix:

```text
terminal whole enstrophy
  + 2 * half-critical absorption * prefix whole gradient mass
  ≤ initial whole enstrophy.
```

This module keeps the endpoint and gradient terms in the same ledger while
passing to the already generated strong whole-carrier closure.  The factor
`2` is retained: it is the exact conversion from half-enstrophy to the full
coefficient mass, not a disposable constant optimization.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger

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
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalSerrinBudget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap

noncomputable section

private theorem ae_ne_zero_volume :
    ∀ᵐ time : ℝ ∂volume, time ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp [MeasureTheory.NullSingletonClass.measure_singleton
    (μ := (volume : Measure ℝ)) (0 : ℝ)]

private theorem commonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

/-- The initial endpoint is null for the common physical-time measure; an
almost-everywhere positive-time ledger is therefore a complete receipt
ledger rather than a loss of one physical event. -/
theorem commonTimeMeasure_ae_time_pos
    (requestedTime : ℝ) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime), 0 < time.1 := by
  rw [commonTimeMeasure_eq_comap_volume]
  apply (ae_restrict_iff_subtype measurableSet_Icc).1
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae ae_ne_zero_volume] with time timeMem timeNe
  exact lt_of_le_of_ne timeMem.1 timeNe.symm

/-- The complete whole-lattice vorticity-gradient payment accumulated before
one actual time of a larger whole receipt. -/
def wholePrefixVorticityGradientMass
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    (state : SpaceTimeState requestedTime) : ℝ :=
  wholeSpaceTimeVorticityGradientMass time.1
    (restrictCommonTimeLpCLM time.2.2 state)

theorem wholePrefixVorticityGradientMass_nonneg
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    (state : SpaceTimeState requestedTime) :
    0 ≤ wholePrefixVorticityGradientMass time state := by
  unfold wholePrefixVorticityGradientMass
    wholeSpaceTimeVorticityGradientMass
  exact tsum_nonneg fun wave =>
    wholeSpaceTimeVorticityGradientDensity_nonneg
      time.1 (restrictCommonTimeLpCLM time.2.2 state) wave

/-! ## Exact finite replay payment -/

/-- Below the fixed half-critical threshold, every canonical unforced stage
pays any finite portion of its prefix gradient mass together with the actual
terminal coefficient mass.  The wave inventory queried by the conclusion is
not a source parameter: the estimate holds for every finite partial sum of
the already generated whole-gradient carrier. -/
theorem canonicalStage_halfCriticalGradientFinsetDissipation_le
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
    (wholeMargin :
      criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass contact.physicalState ≤
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact))
    (timePos : 0 < time.1)
    (waves : Finset IntegerWavevector) :
    wholeVorticityEuclideanMass (stage.trajectory time.1) +
        2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
          (∑ wave ∈ waves,
            wholeSpaceTimeVorticityGradientDensity time.1
              (restrictCommonTimeLpCLM time.2.2
                (wholeTrajectorySpaceTimePath
                  (wholeRestartDuration contact) stage.trajectory
                  (HasDerivAt.continuousOn fun actual actualMem =>
                    (stage.physical actual actualMem).1))) wave) ≤
      wholeVorticityEuclideanMass contact.physicalState := by
  let modes := wholeRestartModes radius
  have negClosed : FiniteModeNegClosed modes :=
    fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have initialMassLe :
      finiteStateVorticityCoefficientEnstrophy
          modes (stage.trajectory 0) ≤
        wholeVorticityEuclideanMass contact.physicalState := by
    rw [stage.initial]
    change
      finiteStateVorticityCoefficientEnstrophy modes
          (complexSharpSupportProjection modes contact.physicalState) ≤
        wholeVorticityEuclideanMass contact.physicalState
    calc
      finiteStateVorticityCoefficientEnstrophy modes
          (complexSharpSupportProjection modes contact.physicalState) =
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection modes contact.physicalState) := by
        symm
        exact wholeVorticityEuclideanMass_eq_finite_of_supported
          modes (complexSharpSupportProjection modes contact.physicalState)
          (complexSharpSupportProjection_supported modes
            contact.physicalState)
      _ ≤ wholeVorticityEuclideanMass contact.physicalState :=
        wholeVorticityEuclideanMass_sharpSupportProjection_le
          modes contact.physicalState
  have initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (stage.trajectory 0) ≤
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    (mul_le_mul_of_nonneg_left initialMassLe
      criticalEnstrophyLatticeConstant_nonneg).trans wholeMargin
  have criticalBudget :=
    finiteStateVorticity_criticalSerrinBudget_on_Icc
      modes negClosed nu (1 / 2 : ℝ) (by norm_num)
      stage.trajectory 0 time.1 time.2.1
      (fun actual actualMem =>
        (stage.physical actual
          ⟨actualMem.1, actualMem.2.trans time.2.2⟩).1)
      (fun actual actualMem =>
        (stage.physical actual
          ⟨actualMem.1, actualMem.2.trans time.2.2⟩).2.2.2)
      (fun actual actualMem wave _waveMem =>
        (stage.physical actual
          ⟨actualMem.1, actualMem.2.trans time.2.2⟩).2.2.1 wave)
      initialMargin
  have gradientFiniteLe :
      (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity time.1
            (restrictCommonTimeLpCLM time.2.2
              (wholeTrajectorySpaceTimePath
                (wholeRestartDuration contact) stage.trajectory
                (HasDerivAt.continuousOn fun actual actualMem =>
                  (stage.physical actual actualMem).1))) wave) ≤
        ∫ actual in (0 : ℝ)..time.1,
          finiteStateVorticityEnstrophyMass
            modes (stage.trajectory actual) := by
    rw [restrictCommonTimeLpCLM_apply]
    rw [restrictCommonTimeLp_wholeTrajectorySpaceTimePath
      time.2.2 stage.trajectory
      (HasDerivAt.continuousOn fun actual actualMem =>
        (stage.physical actual actualMem).1)]
    exact
      wholeTrajectory_gradientDensity_finsetSum_le_enstrophyIntegral
        time.1 timePos modes waves nu.coeff stage.trajectory
        (fun actual actualMem =>
          (stage.physical actual
            ⟨actualMem.1, actualMem.2.trans time.2.2⟩).1)
        (fun actual actualMem wave waveNotMem =>
          (stage.physical actual
            ⟨actualMem.1, actualMem.2.trans time.2.2⟩).2.1
              wave waveNotMem)
  have absorptionPos :
      0 < criticalEnstrophyAbsorptionCoefficient (1 / 2) nu :=
    criticalEnstrophyAbsorptionCoefficient_pos
      (1 / 2 : ℝ) (by norm_num) nu
  have scaledGradientLe :=
    mul_le_mul_of_nonneg_left gradientFiniteLe absorptionPos.le
  have integratedAbsorption := criticalBudget.2.1
  have terminalHalfEq :
      finiteStateVorticityHalfEnstrophy
          modes (stage.trajectory time.1) =
        (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass (stage.trajectory time.1) := by
    unfold finiteStateVorticityHalfEnstrophy
    rw [wholeVorticityEuclideanMass_eq_finite_of_supported
      modes (stage.trajectory time.1)
      ((stage.physical time.1 time.2).2.1)]
  have initialHalfLe :
      finiteStateVorticityHalfEnstrophy
          modes (stage.trajectory 0) ≤
        (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass contact.physicalState := by
    unfold finiteStateVorticityHalfEnstrophy
    nlinarith
  rw [terminalHalfEq] at integratedAbsorption
  nlinarith

/-! ## Coupled transport to the actual whole replay -/

/-- The strong whole-carrier closure retains the coupled endpoint and full
gradient payment at every positive time outside one null set.  Finite
partial sums are transported before the lattice `tsum` is formed, so the
endpoint term cannot be detached from its dissipation responsibility. -/
theorem criticalClosure_halfCriticalGradientDissipation_ae_le
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
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wholeMargin :
      criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass contact.physicalState ≤
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      0 < time.1 →
        wholeVorticityEuclideanMass
              (closure.weakClosure.stateLimit time) +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
              wholePrefixVorticityGradientMass time
                closure.weakClosure.stateLimit ≤
          wholeVorticityEuclideanMass contact.physicalState := by
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
  intro timePos
  let prefixStateSequence : ℕ → SpaceTimeState time.1 := fun index =>
    restrictCommonTimeLpCLM time.2.2
      (stateSequence (pointwiseSubsequence index))
  let prefixStateLimit : SpaceTimeState time.1 :=
    restrictCommonTimeLpCLM time.2.2 weakClosure.stateLimit
  have prefixStateTendsto :
      Tendsto prefixStateSequence atTop (𝓝 prefixStateLimit) := by
    exact
      ((restrictCommonTimeLpCLM time.2.2).continuous.tendsto
          weakClosure.stateLimit).comp
        (stateTendsto.comp pointwiseSubsequenceMono.tendsto_atTop)
  have endpointMassTendsto :
      Tendsto
        (fun index =>
          wholeVorticityEuclideanMass
            (stateSequence (pointwiseSubsequence index) time))
        atTop
        (𝓝 (wholeVorticityEuclideanMass
          (weakClosure.stateLimit time))) :=
    tendsto_wholeVorticityEuclideanMass timeTendsto
  have finitePayment :
      ∀ waves : Finset IntegerWavevector,
        wholeVorticityEuclideanMass
              (weakClosure.stateLimit time) +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
              (∑ wave ∈ waves,
                wholeSpaceTimeVorticityGradientDensity time.1
                  prefixStateLimit wave) ≤
          wholeVorticityEuclideanMass contact.physicalState := by
    intro waves
    have gradientTendsto :
        Tendsto
          (fun index =>
            ∑ wave ∈ waves,
              wholeSpaceTimeVorticityGradientDensity time.1
                (prefixStateSequence index) wave)
          atTop
          (𝓝
            (∑ wave ∈ waves,
              wholeSpaceTimeVorticityGradientDensity time.1
                prefixStateLimit wave)) := by
      apply tendsto_finsetSum
      intro wave waveMem
      exact
        tendsto_wholeSpaceTimeVorticityGradientDensity
          time.1 prefixStateSequence prefixStateLimit
          prefixStateTendsto wave
    have paymentTendsto :
        Tendsto
          (fun index =>
            wholeVorticityEuclideanMass
                (stateSequence (pointwiseSubsequence index) time) +
              2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
                (∑ wave ∈ waves,
                  wholeSpaceTimeVorticityGradientDensity time.1
                    (prefixStateSequence index) wave))
          atTop
          (𝓝
            (wholeVorticityEuclideanMass
                (weakClosure.stateLimit time) +
              2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
                (∑ wave ∈ waves,
                  wholeSpaceTimeVorticityGradientDensity time.1
                    prefixStateLimit wave))) :=
      endpointMassTendsto.add
        (tendsto_const_nhds.mul gradientTendsto)
    apply le_of_tendsto paymentTendsto
    exact Filter.Eventually.of_forall fun index => by
      let stage := replay.current
        (weakClosure.subsequence (pointwiseSubsequence index))
      change
        wholeVorticityEuclideanMass
              (stateSequence (pointwiseSubsequence index) time) +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
              (∑ wave ∈ waves,
                wholeSpaceTimeVorticityGradientDensity time.1
                  (restrictCommonTimeLpCLM time.2.2
                    (stateSequence (pointwiseSubsequence index))) wave) ≤
          wholeVorticityEuclideanMass contact.physicalState
      rw [pathEq index]
      exact
        canonicalStage_halfCriticalGradientFinsetDissipation_le
          stage wholeMargin time timePos waves
  have prefixGradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity time.1
          prefixStateLimit wave := by
    change
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity time.1
          (restrictCommonTimeLp time.2.2 weakClosure.stateLimit) wave
    exact
      wholeSpaceTimeVorticityGradientDensity_restrict_summable
        time.2.2 weakClosure.stateLimit closure.gradient_summable
  have fullPaymentTendsto :
      Tendsto
        (fun waves : Finset IntegerWavevector =>
          wholeVorticityEuclideanMass (weakClosure.stateLimit time) +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
              ∑ wave ∈ waves,
                wholeSpaceTimeVorticityGradientDensity time.1
                  prefixStateLimit wave)
        atTop
        (𝓝
          (wholeVorticityEuclideanMass (weakClosure.stateLimit time) +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
              ∑' wave : IntegerWavevector,
                wholeSpaceTimeVorticityGradientDensity time.1
                  prefixStateLimit wave)) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.mul prefixGradientSummable.hasSum)
  unfold wholePrefixVorticityGradientMass
    wholeSpaceTimeVorticityGradientMass
  exact le_of_tendsto fullPaymentTendsto
    (Filter.Eventually.of_forall finitePayment)

/-- On the subcritical side, the coupled ledger itself supplies the actual
whole coefficient ceiling needed by the nonlinear `H⁻¹` consumer. -/
theorem criticalClosure_coefficientMass_ae_le_of_halfCritical
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
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wholeMargin :
      criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass contact.physicalState ≤
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      wholeVorticityEuclideanMass
          (closure.weakClosure.stateLimit time) ≤
        wholeVorticityEuclideanMass contact.physicalState := by
  filter_upwards [
    criticalClosure_halfCriticalGradientDissipation_ae_le
      closure wholeMargin,
    commonTimeMeasure_ae_time_pos (wholeRestartDuration contact)] with
      time payment timePos
  have gradientNonneg :=
    wholePrefixVorticityGradientMass_nonneg
      time closure.weakClosure.stateLimit
  have absorptionPos :=
    criticalEnstrophyAbsorptionCoefficient_pos
      (1 / 2 : ℝ) (by norm_num) nu
  have paid := payment timePos
  nlinarith

/-- The half-critical crossing is decided internally from the actual whole
contact.  If it has not occurred, the same actual closure carries the full
gradient payment.  No caller supplies a branch, cutoff, or margin witness. -/
theorem criticalClosure_halfCriticalAbsorption_disposition_ae
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
      0 < time.1 →
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 <
            criticalEnstrophyLatticeConstant *
              wholeVorticityEuclideanMass contact.physicalState ∨
          wholeVorticityEuclideanMass
                (closure.weakClosure.stateLimit time) +
              2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
                wholePrefixVorticityGradientMass time
                  closure.weakClosure.stateLimit ≤
            wholeVorticityEuclideanMass contact.physicalState := by
  by_cases crossed :
      (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass contact.physicalState
  · exact Filter.Eventually.of_forall fun _time _timePos => Or.inl crossed
  · have wholeMargin :
        criticalEnstrophyLatticeConstant *
            wholeVorticityEuclideanMass contact.physicalState ≤
          (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
      le_of_not_gt crossed
    filter_upwards [
      criticalClosure_halfCriticalGradientDissipation_ae_le
        closure wholeMargin] with time payment
    intro timePos
    exact Or.inr (payment timePos)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
end NavierStokes
end SaturationMonoid
