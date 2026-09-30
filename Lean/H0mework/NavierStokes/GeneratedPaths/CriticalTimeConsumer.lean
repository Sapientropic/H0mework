import H0mework.NavierStokes.GeneratedPaths.ViscousEnstrophyCost

/-!
# Critical time consumer for an arbitrary generated shell path

An actual `GeneratedIntegerShellReachable` already generates one common
positive-time Galerkin trajectory on which every historical receipt remains
visible and pays its exact shell-weighted trace cost.  This module integrates
the cutoff-independent critical envelope on that same trajectory.

The resulting source-owned receipt simultaneously carries

* the original finite Galerkin update and rowwise transversality;
* source-generated Fourier reality on the same trajectory;
* an `L²_t` bound for the complete path Fourier velocity majorant;
* the same `L²_t` bound for every pointwise real-part velocity field;
* the previously generated lower cost of the cumulative weighted trace.

No time, trajectory, cutoff, path length, amplitude decay, dissipation
budget, or continuation target is accepted as a premise.  The path readout
and the complete endpoint Galerkin carrier are both estimated, so the exact
source trace lower cost and the classical critical-norm upper bound live on
one reality-preserving trajectory.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer

open scoped BigOperators Matrix Topology ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalEnvelope
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathViscousEnstrophyCost
open ThreeDimensionalIntegerLatticeCriticalKernel

noncomputable section

private theorem continuousAt_finset_sum'
    {α E : Type}
    [DecidableEq α]
    [TopologicalSpace E]
    [AddCommMonoid E]
    [ContinuousAdd E]
    (indices : Finset α)
    (summand : α → ℝ → E)
    (t : ℝ)
    (continuousSummand :
      ∀ index ∈ indices, ContinuousAt (summand index) t) :
    ContinuousAt (fun time => ∑ index ∈ indices, summand index time) t := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : E)) t)
  | @insert index indices indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      exact
        (continuousSummand index (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuousSummand later (by simp [laterMem]))

private theorem continuousAt_list_map_sum'
    {α E : Type}
    [TopologicalSpace E]
    [AddMonoid E]
    [ContinuousAdd E]
    (entries : List α)
    (summand : α → ℝ → E)
    (t : ℝ)
    (continuousSummand :
      ∀ entry ∈ entries, ContinuousAt (summand entry) t) :
    ContinuousAt
      (fun time => (entries.map fun entry => summand entry time).sum) t := by
  induction entries with
  | nil =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : E)) t)
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact
        (continuousSummand head (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuousSummand later (by simp [laterMem]))

/-! ## Pointwise global critical envelope -/

/-- The complete Fourier majorant of an arbitrary actual path has the same
cutoff-independent critical envelope as its pointwise real-part field. -/
theorem generatedIntegerShellReachableStateVelocityMajorant_sq_le_global
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : IntegerWavevector → ComplexCoordinateVector) :
    generatedIntegerShellReachableStateVelocityMajorant arrival state ^ 2 ≤
      biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
        pathWholeShellEnstrophyMass arrival state := by
  calc
    generatedIntegerShellReachableStateVelocityMajorant arrival state ^ 2 ≤
        biotSavartSerrinConstant *
          generatedIntegerShellReachableCriticalKernelWeight arrival *
          pathWholeShellEnstrophyMass arrival state :=
      generatedIntegerShellReachableStateVelocityMajorant_sq_le_critical
        arrival state
    _ ≤
        biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
          pathWholeShellEnstrophyMass arrival state := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (generatedIntegerShellReachableCriticalKernelWeight_le_global
            arrival)
          biotSavartSerrinConstant_nonneg)
        (pathWholeShellEnstrophyMass_nonneg arrival state)

/-! ## Continuity of the three finite path ledgers -/

private theorem biotSavartVelocityCoefficient_continuousAt_of_hasDerivAt
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        biotSavartVelocityCoefficient wave (trajectory time wave)) t := by
  have waveContinuous :
      ContinuousAt (fun time => trajectory time wave) t :=
    (complexVorticityTrajectoryWave_hasDerivAt
      trajectory t tangent wave evolves).continuousAt
  have coordinateContinuous :
      ∀ coordinate : Coordinate,
        ContinuousAt (fun time => trajectory time wave coordinate) t :=
    fun coordinate =>
      (continuous_apply coordinate).continuousAt.comp waveContinuous
  by_cases waveZero : wave = 0
  · subst wave
    simpa using
      (continuousAt_const :
        ContinuousAt
          (fun _ : ℝ => (0 : ComplexCoordinateVector)) t)
  · rw [continuousAt_pi]
    intro coordinate
    have c0 := coordinateContinuous (0 : Coordinate)
    have c1 := coordinateContinuous (1 : Coordinate)
    have c2 := coordinateContinuous (2 : Coordinate)
    fin_cases coordinate <;>
      simp only [biotSavartVelocityCoefficient, if_neg waveZero,
        Pi.smul_apply, cross_apply] <;>
      fun_prop

/-- One Fourier-row amplitude square is continuous along every
differentiable coefficient trajectory. -/
theorem complexCoordinateAmplitudeSq_continuousAt_of_hasDerivAt
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        complexCoordinateAmplitudeSq (trajectory time wave)) t := by
  have waveContinuous :
      ContinuousAt (fun time => trajectory time wave) t :=
    (complexVorticityTrajectoryWave_hasDerivAt
      trajectory t tangent wave evolves).continuousAt
  unfold complexCoordinateAmplitudeSq
  exact continuousAt_finset_sum' Finset.univ
    (fun coordinate time =>
      Complex.normSq (trajectory time wave coordinate)) t
    (fun coordinate _ =>
      Complex.continuous_normSq.continuousAt.comp
        ((continuous_apply coordinate).continuousAt.comp waveContinuous))

private theorem
    complexCoordinateAmplitudeSq_biotSavart_continuousAt_of_hasDerivAt
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave
            (trajectory time wave))) t := by
  have velocityContinuous :=
    biotSavartVelocityCoefficient_continuousAt_of_hasDerivAt
      trajectory t tangent wave evolves
  unfold complexCoordinateAmplitudeSq
  exact continuousAt_finset_sum' Finset.univ
    (fun coordinate time =>
      Complex.normSq
        (biotSavartVelocityCoefficient wave
          (trajectory time wave) coordinate)) t
    (fun coordinate _ =>
      Complex.continuous_normSq.continuousAt.comp
        ((continuous_apply coordinate).continuousAt.comp
          velocityContinuous))

private theorem
    generatedIntegerShellReceiptStateVelocityMajorant_continuousAt
    (receipt : GeneratedIntegerShellReceipt)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        generatedIntegerShellReceiptStateVelocityMajorant
          receipt (fun wave => trajectory time wave)) t := by
  unfold generatedIntegerShellReceiptStateVelocityMajorant
    finiteVelocityFourierMajorant
  exact continuousAt_finset_sum' receipt.wholeShellModes
    (fun wave time =>
      Real.sqrt
        (complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave
            (trajectory time wave)))) t
    (fun wave _ =>
      Real.continuous_sqrt.continuousAt.comp
        (complexCoordinateAmplitudeSq_biotSavart_continuousAt_of_hasDerivAt
          trajectory t tangent wave evolves))

private theorem
    generatedIntegerShellReachableStateVelocityMajorant_continuousAt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        generatedIntegerShellReachableStateVelocityMajorant
          arrival (fun wave => trajectory time wave)) t := by
  unfold generatedIntegerShellReachableStateVelocityMajorant
  exact continuousAt_list_map_sum'
    (generatedIntegerShellReachableReceipts arrival)
    (fun receipt time =>
      generatedIntegerShellReceiptStateVelocityMajorant
        receipt (fun wave => trajectory time wave)) t
    (fun receipt _ =>
      generatedIntegerShellReceiptStateVelocityMajorant_continuousAt
        receipt trajectory t tangent evolves)

/-- The complete finite-state Fourier velocity majorant is continuous along
every differentiable coefficient trajectory. -/
theorem finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        finiteStateVelocityMajorant modes (trajectory time)) t := by
  unfold finiteStateVelocityMajorant finiteStateVelocityCoefficient
    finiteVelocityFourierMajorant
  exact continuousAt_finset_sum' modes
    (fun wave time =>
      Real.sqrt
        (complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave
            (trajectory time wave)))) t
    (fun wave _ =>
      Real.continuous_sqrt.continuousAt.comp
        (complexCoordinateAmplitudeSq_biotSavart_continuousAt_of_hasDerivAt
          trajectory t tangent wave evolves))

private theorem coefficientReal_continuousAt_comp
    (coefficient : ℝ → ComplexCoordinateVector)
    (t : ℝ)
    (coefficientContinuous : ContinuousAt coefficient t) :
    ContinuousAt (fun time => coefficientReal (coefficient time)) t := by
  unfold coefficientReal
  exact
    (PiLp.continuous_toLp
      (p := 2) (β := fun _ : Coordinate => ℝ)).continuousAt.comp
    (continuousAt_pi.mpr fun coordinate =>
      Complex.continuous_re.continuousAt.comp
        ((continuous_apply coordinate).continuousAt.comp
          coefficientContinuous))

private theorem coefficientImag_continuousAt_comp
    (coefficient : ℝ → ComplexCoordinateVector)
    (t : ℝ)
    (coefficientContinuous : ContinuousAt coefficient t) :
    ContinuousAt (fun time => coefficientImag (coefficient time)) t := by
  unfold coefficientImag
  exact
    (PiLp.continuous_toLp
      (p := 2) (β := fun _ : Coordinate => ℝ)).continuousAt.comp
    (continuousAt_pi.mpr fun coordinate =>
      Complex.continuous_im.continuousAt.comp
        ((continuous_apply coordinate).continuousAt.comp
          coefficientContinuous))

private theorem realComplexFourierMode_continuousAt_coefficient
    (wave : IntegerWavevector)
    (coefficient : ℝ → ComplexCoordinateVector)
    (x : PhysicalSpace)
    (t : ℝ)
    (coefficientContinuous : ContinuousAt coefficient t) :
    ContinuousAt
      (fun time => realComplexFourierMode wave (coefficient time) x) t := by
  unfold realComplexFourierMode
  exact
    (coefficientReal_continuousAt_comp
        coefficient t coefficientContinuous
      |>.const_smul (integerCosine wave x)).sub
      (coefficientImag_continuousAt_comp
          coefficient t coefficientContinuous
        |>.const_smul (integerSine wave x))

private theorem generatedIntegerShellReceiptEnstrophyMass_continuousAt
    (receipt : GeneratedIntegerShellReceipt)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        generatedIntegerShellReceiptEnstrophyMass
          receipt (fun wave => trajectory time wave)) t := by
  unfold generatedIntegerShellReceiptEnstrophyMass
    generatedIntegerShellReceiptWholeShellVorticityMass
  apply ContinuousAt.const_mul
  exact continuousAt_finset_sum' receipt.wholeShellModes
    (fun wave time =>
      complexCoordinateAmplitudeSq (trajectory time wave)) t
    (fun wave _ =>
      complexCoordinateAmplitudeSq_continuousAt_of_hasDerivAt
        trajectory t tangent wave evolves)

private theorem pathWholeShellEnstrophyMass_continuousAt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        pathWholeShellEnstrophyMass
          arrival (fun wave => trajectory time wave)) t := by
  unfold pathWholeShellEnstrophyMass
  exact continuousAt_list_map_sum'
    (generatedIntegerShellReachableReceipts arrival)
    (fun receipt time =>
      generatedIntegerShellReceiptEnstrophyMass
        receipt (fun wave => trajectory time wave)) t
    (fun receipt _ =>
      generatedIntegerShellReceiptEnstrophyMass_continuousAt
        receipt trajectory t tangent evolves)

private theorem
    generatedIntegerShellReceiptStatePhysicalVelocityField_continuousAt
    (receipt : GeneratedIntegerShellReceipt)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (x : PhysicalSpace)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        generatedIntegerShellReceiptStatePhysicalVelocityField
          receipt (fun wave => trajectory time wave) x) t := by
  unfold generatedIntegerShellReceiptStatePhysicalVelocityField
    finiteRealComplexFourierField
  exact
    continuousAt_finset_sum' receipt.wholeShellModes
      (fun wave time =>
        realComplexFourierMode wave
          (biotSavartVelocityCoefficient wave
            (trajectory time wave)) x) t
      (fun wave _ => by
        have velocityContinuous :=
          biotSavartVelocityCoefficient_continuousAt_of_hasDerivAt
            trajectory t tangent wave evolves
        exact
          realComplexFourierMode_continuousAt_coefficient
            wave
            (fun time =>
              biotSavartVelocityCoefficient wave
                (trajectory time wave))
            x t velocityContinuous)

private theorem finiteStateVelocityRealPartField_continuousAt_of_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (x : PhysicalSpace)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        finiteStateVelocityRealPartField modes (trajectory time) x) t := by
  unfold finiteStateVelocityRealPartField
    finiteRealComplexFourierField finiteStateVelocityCoefficient
  exact
    continuousAt_finset_sum' modes
      (fun wave time =>
        realComplexFourierMode wave
          (biotSavartVelocityCoefficient wave
            (trajectory time wave)) x) t
      (fun wave _ => by
        have velocityContinuous :=
          biotSavartVelocityCoefficient_continuousAt_of_hasDerivAt
            trajectory t tangent wave evolves
        exact
          realComplexFourierMode_continuousAt_coefficient
            wave
            (fun time =>
              biotSavartVelocityCoefficient wave
                (trajectory time wave))
            x t velocityContinuous)

private theorem realPartVelocityField_continuousAt_of_hasDerivAt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (x : PhysicalSpace)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        generatedIntegerShellReachableStatePhysicalVelocityField
          arrival (fun wave => trajectory time wave) x) t := by
  induction arrival with
  | initial =>
      simpa [generatedIntegerShellReachableStatePhysicalVelocityField,
        generatedIntegerShellReachableReceipts] using
        (continuousAt_const :
          ContinuousAt (fun _ : ℝ => (0 : PhysicalSpace)) t)
  | @step prior arrival response generated inductionHypothesis =>
      let receipt : GeneratedIntegerShellReceipt :=
        ⟨prior, response, generated⟩
      have receiptContinuous :=
        generatedIntegerShellReceiptStatePhysicalVelocityField_continuousAt
          receipt trajectory x t tangent evolves
      have sumContinuous :=
        inductionHypothesis.add receiptContinuous
      change
        ContinuousAt
          (fun time =>
            ((generatedIntegerShellReachableReceipts arrival).map
                (fun oldReceipt =>
                  generatedIntegerShellReceiptStatePhysicalVelocityField
                    oldReceipt
                    (fun wave => trajectory time wave))).sum x +
              generatedIntegerShellReceiptStatePhysicalVelocityField
                receipt (fun wave => trajectory time wave) x) t
        at sumContinuous
      simpa [generatedIntegerShellReachableStatePhysicalVelocityField,
        generatedIntegerShellReachableReceipts,
        List.concat_eq_append, receipt] using
          sumContinuous

/-! ## Same-trajectory time integration -/

/-- Every finite source-generated path produces one positive-time
transverse, Fourier-real Galerkin trajectory on which the cutoff-independent
critical velocity envelope and the cumulative shell-weighted trace cost hold
simultaneously.

The two path clauses retain the exact generated-shell readout requested by
the source grammar.  The following two clauses put the full endpoint
Galerkin velocity and enstrophy on the same trajectory, which is the carrier
consumed by a classical critical-norm continuation argument. -/
theorem
    generatedIntegerShellReachable_drives_transverseRealityCriticalTimeConsumer
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (occupancyTime : ℝ),
      0 < occupancyTime ∧
        trajectory 0 =
          generatedComplexVorticityState current
            (generatedSupport current) ∧
        (∀ t ∈ Icc (0 : ℝ) occupancyTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport current) ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport current →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t)) ∧
        (∫ t in (0 : ℝ)..occupancyTime,
            generatedIntegerShellReachableStateVelocityMajorant
                arrival (fun wave => trajectory t wave) ^ 2) ≤
          biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave) *
            ∫ t in (0 : ℝ)..occupancyTime,
              pathWholeShellEnstrophyMass
                arrival (fun wave => trajectory t wave) ∧
        (∀ x : PhysicalSpace,
          (∫ t in (0 : ℝ)..occupancyTime,
              ‖generatedIntegerShellReachableStatePhysicalVelocityField
                  arrival (fun wave => trajectory t wave) x‖ ^ 2) ≤
            biotSavartSerrinConstant *
                (∑' wave : IntegerWavevector,
                  integerWaveCriticalKernel wave) *
              ∫ t in (0 : ℝ)..occupancyTime,
                pathWholeShellEnstrophyMass
                  arrival (fun wave => trajectory t wave)) ∧
        (∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVelocityMajorant
                (generatedSupport current) (trajectory t) ^ 2) ≤
          biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave) *
            ∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass
                (generatedSupport current) (trajectory t) ∧
        (∀ x : PhysicalSpace,
          (∫ t in (0 : ℝ)..occupancyTime,
              ‖finiteStateVelocityRealPartField
                  (generatedSupport current) (trajectory t) x‖ ^ 2) ≤
            biotSavartSerrinConstant *
                (∑' wave : IntegerWavevector,
                  integerWaveCriticalKernel wave) *
              ∫ t in (0 : ℝ)..occupancyTime,
                finiteStateVorticityEnstrophyMass
                  (generatedSupport current) (trajectory t)) ∧
        occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2) ≤
          ∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityEnstrophyMass
              (generatedSupport current) (trajectory t) := by
  obtain
      ⟨trajectory, occupancyTime, occupancyTimePos, initial,
        physicalProperties, cumulativeTraceLower⟩ :=
    generatedIntegerShellReachable_drives_transverseRealityIntegratedEndpointEnstrophyCost
      arrival ν
  have majorantContinuousOn :
      ContinuousOn
        (fun t =>
          generatedIntegerShellReachableStateVelocityMajorant
              arrival (fun wave => trajectory t wave) ^ 2)
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (generatedIntegerShellReachableStateVelocityMajorant_continuousAt
        arrival trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (physicalProperties t timeMem).1).pow 2
        |>.continuousWithinAt
  have wholeShellContinuousOn :
      ContinuousOn
        (fun t =>
          pathWholeShellEnstrophyMass
            arrival (fun wave => trajectory t wave))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (pathWholeShellEnstrophyMass_continuousAt
        arrival trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (physicalProperties t timeMem).1).continuousWithinAt
  have endpointEnstrophyContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass
            (generatedSupport current) (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        (generatedSupport current) trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (physicalProperties t timeMem).1).continuousWithinAt
  have majorantIntegrable :
      IntervalIntegrable
        (fun t =>
          generatedIntegerShellReachableStateVelocityMajorant
              arrival (fun wave => trajectory t wave) ^ 2)
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le majorantContinuousOn
  have wholeShellIntegrable :
      IntervalIntegrable
        (fun t =>
          pathWholeShellEnstrophyMass
            arrival (fun wave => trajectory t wave))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le wholeShellContinuousOn
  have endpointEnstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass
            (generatedSupport current) (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le endpointEnstrophyContinuousOn
  have criticalRightIntegrable :
      IntervalIntegrable
        (fun t =>
          biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            pathWholeShellEnstrophyMass
              arrival (fun wave => trajectory t wave))
        volume 0 occupancyTime :=
    (wholeShellIntegrable.const_mul
      (biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector,
          integerWaveCriticalKernel wave)))
  have majorantIntegralUpper :
      (∫ t in (0 : ℝ)..occupancyTime,
          generatedIntegerShellReachableStateVelocityMajorant
              arrival (fun wave => trajectory t wave) ^ 2) ≤
        biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
          ∫ t in (0 : ℝ)..occupancyTime,
            pathWholeShellEnstrophyMass
              arrival (fun wave => trajectory t wave) := by
    have integrated :=
      intervalIntegral.integral_mono_on
        occupancyTimePos.le majorantIntegrable criticalRightIntegrable
        (fun t timeMem =>
          generatedIntegerShellReachableStateVelocityMajorant_sq_le_global
            arrival (fun wave => trajectory t wave))
    simpa only [intervalIntegral.integral_const_mul] using integrated
  have pointwiseFieldIntegralUpper :
      ∀ x : PhysicalSpace,
        (∫ t in (0 : ℝ)..occupancyTime,
            ‖generatedIntegerShellReachableStatePhysicalVelocityField
                arrival (fun wave => trajectory t wave) x‖ ^ 2) ≤
          biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave) *
            ∫ t in (0 : ℝ)..occupancyTime,
              pathWholeShellEnstrophyMass
                arrival (fun wave => trajectory t wave) := by
    intro x
    have fieldContinuousOn :
        ContinuousOn
          (fun t =>
            ‖generatedIntegerShellReachableStatePhysicalVelocityField
                arrival (fun wave => trajectory t wave) x‖ ^ 2)
          (Icc (0 : ℝ) occupancyTime) := by
      intro t timeMem
      exact
        ((realPartVelocityField_continuousAt_of_hasDerivAt
          arrival trajectory x t
          (finiteStateVorticityGenerator
            (generatedSupport current) ν (trajectory t))
          (physicalProperties t timeMem).1).norm.pow 2).continuousWithinAt
    have fieldIntegrable :
        IntervalIntegrable
          (fun t =>
            ‖generatedIntegerShellReachableStatePhysicalVelocityField
                arrival (fun wave => trajectory t wave) x‖ ^ 2)
          volume 0 occupancyTime :=
      ContinuousOn.intervalIntegrable_of_Icc
        occupancyTimePos.le fieldContinuousOn
    have integrated :=
      intervalIntegral.integral_mono_on
        occupancyTimePos.le fieldIntegrable criticalRightIntegrable
        (fun t timeMem =>
          generatedIntegerShellReachable_wholeShellStateCriticalEnvelope_global
            arrival (fun wave => trajectory t wave) x)
    simpa only [intervalIntegral.integral_const_mul] using integrated
  have endpointCriticalRightIntegrable :
      IntervalIntegrable
        (fun t =>
          biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            finiteStateVorticityEnstrophyMass
              (generatedSupport current) (trajectory t))
        volume 0 occupancyTime :=
    endpointEnstrophyIntegrable.const_mul
      (biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector,
          integerWaveCriticalKernel wave))
  have endpointMajorantContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVelocityMajorant
              (generatedSupport current) (trajectory t) ^ 2)
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
        (generatedSupport current) trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (physicalProperties t timeMem).1).pow 2).continuousWithinAt
  have endpointMajorantIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVelocityMajorant
              (generatedSupport current) (trajectory t) ^ 2)
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le endpointMajorantContinuousOn
  have endpointMajorantIntegralUpper :
      (∫ t in (0 : ℝ)..occupancyTime,
          finiteStateVelocityMajorant
              (generatedSupport current) (trajectory t) ^ 2) ≤
        biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
          ∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityEnstrophyMass
              (generatedSupport current) (trajectory t) := by
    have integrated :=
      intervalIntegral.integral_mono_on
        occupancyTimePos.le endpointMajorantIntegrable
          endpointCriticalRightIntegrable
        (fun t timeMem =>
          finiteStateVelocityMajorant_sq_le_criticalGlobal
            (generatedSupport current) (trajectory t))
    simpa only [intervalIntegral.integral_const_mul] using integrated
  have endpointFieldIntegralUpper :
      ∀ x : PhysicalSpace,
        (∫ t in (0 : ℝ)..occupancyTime,
            ‖finiteStateVelocityRealPartField
                (generatedSupport current) (trajectory t) x‖ ^ 2) ≤
          biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave) *
            ∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass
                (generatedSupport current) (trajectory t) := by
    intro x
    have fieldContinuousOn :
        ContinuousOn
          (fun t =>
            ‖finiteStateVelocityRealPartField
                (generatedSupport current) (trajectory t) x‖ ^ 2)
          (Icc (0 : ℝ) occupancyTime) := by
      intro t timeMem
      exact
        ((finiteStateVelocityRealPartField_continuousAt_of_hasDerivAt
          (generatedSupport current) trajectory x t
          (finiteStateVorticityGenerator
            (generatedSupport current) ν (trajectory t))
          (physicalProperties t timeMem).1).norm.pow 2).continuousWithinAt
    have fieldIntegrable :
        IntervalIntegrable
          (fun t =>
            ‖finiteStateVelocityRealPartField
                (generatedSupport current) (trajectory t) x‖ ^ 2)
          volume 0 occupancyTime :=
      ContinuousOn.intervalIntegrable_of_Icc
        occupancyTimePos.le fieldContinuousOn
    have integrated :=
      intervalIntegral.integral_mono_on
        occupancyTimePos.le fieldIntegrable endpointCriticalRightIntegrable
        (fun t timeMem =>
          finiteStateVelocityRealPartField_norm_sq_le_criticalGlobal
            (generatedSupport current) (trajectory t) x)
    simpa only [intervalIntegral.integral_const_mul] using integrated
  exact
    ⟨trajectory, occupancyTime, occupancyTimePos, initial,
      physicalProperties, majorantIntegralUpper,
      pointwiseFieldIntegralUpper, endpointMajorantIntegralUpper,
      endpointFieldIntegralUpper, cumulativeTraceLower⟩

end

end ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
end NavierStokes
end SaturationMonoid
