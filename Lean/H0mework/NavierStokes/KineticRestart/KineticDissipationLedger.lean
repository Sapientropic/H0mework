import H0mework.NavierStokes.Restart.CriticalClosure
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinOverlap

/-!
# Whole kinetic-dissipation ledger of the generated restart

The canonical finite Galerkin replay already carries the exact kinetic
energy identity.  This module transports its unweighted vorticity payment
through the same strong whole-carrier limit and through an actual physical
time prefix.  The transported payment is a continuous quadratic functional
of the existing `L²_t(ℓ²_k)` carrier; no occurrence norm, cutoff, target
trajectory, or caller-selected energy certificate is introduced.
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
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap

noncomputable section

/-- One physical coordinate of every Fourier row, retained over the actual
common-time `L²` carrier. -/
def wholeSpaceTimeEuclideanCoordinateSlice
    (requestedTime : ℝ)
    (coordinate : Coordinate) :
    SpaceTimeState requestedTime →L[ℂ]
      MeasureTheory.Lp
        (lp (fun _ : IntegerWavevector => ℂ) 2) 2
        (commonTimeMeasure requestedTime) :=
  (pointwiseMassCoordinateSliceCLM coordinate).compLpL 2
    (commonTimeMeasure requestedTime)

/-- Exact unweighted whole-vorticity payment on one physical time carrier.
It is the finite sum of the squared time-`L²` norms of the three Euclidean
coordinate slices. -/
def wholeSpaceTimeEuclideanMass
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) : ℝ :=
  ∑ coordinate : Coordinate,
    ‖wholeSpaceTimeEuclideanCoordinateSlice
      requestedTime coordinate state‖ ^ 2

theorem wholeSpaceTimeEuclideanMass_nonneg
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    0 ≤ wholeSpaceTimeEuclideanMass requestedTime state := by
  unfold wholeSpaceTimeEuclideanMass
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The three generated coordinate slices jointly separate the complete
space-time state.  Hence the quadratic carrier payment vanishes exactly at
the zero state; no observer-facing norm or terminal predicate is supplied. -/
theorem wholeSpaceTimeEuclideanMass_eq_zero_iff
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    wholeSpaceTimeEuclideanMass requestedTime state = 0 ↔ state = 0 := by
  constructor
  · intro massZero
    have sliceNormSqZero : ∀ coordinate : Coordinate,
        ‖wholeSpaceTimeEuclideanCoordinateSlice
          requestedTime coordinate state‖ ^ 2 = 0 := by
      intro coordinate
      exact congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg fun index =>
          sq_nonneg
            ‖wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime index state‖).mp massZero)
        coordinate
    have sliceZero : ∀ coordinate : Coordinate,
        wholeSpaceTimeEuclideanCoordinateSlice
          requestedTime coordinate state = 0 := by
      intro coordinate
      exact norm_eq_zero.mp
        ((sq_eq_zero_iff).mp (sliceNormSqZero coordinate))
    have sliceStateEqZeroState : ∀ coordinate : Coordinate,
        wholeSpaceTimeEuclideanCoordinateSlice
            requestedTime coordinate state =
          wholeSpaceTimeEuclideanCoordinateSlice
            requestedTime coordinate 0 := by
      intro coordinate
      rw [map_zero]
      exact sliceZero coordinate
    have sliceAE : ∀ coordinate : Coordinate,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate state time =
            pointwiseMassCoordinateSliceCLM coordinate (state time) := by
      intro coordinate
      exact
        (pointwiseMassCoordinateSliceCLM coordinate).coeFn_compLpL state
    have zeroSliceAE : ∀ coordinate : Coordinate,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate 0 time =
            pointwiseMassCoordinateSliceCLM coordinate
              ((0 : SpaceTimeState requestedTime) time) := by
      intro coordinate
      exact
        (pointwiseMassCoordinateSliceCLM coordinate).coeFn_compLpL
          (0 : SpaceTimeState requestedTime)
    have allSliceAE :
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          ∀ coordinate : Coordinate,
            wholeSpaceTimeEuclideanCoordinateSlice
                requestedTime coordinate state time =
              pointwiseMassCoordinateSliceCLM coordinate (state time) :=
      eventually_countable_forall.2 sliceAE
    have allZeroSliceAE :
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          ∀ coordinate : Coordinate,
            wholeSpaceTimeEuclideanCoordinateSlice
                requestedTime coordinate 0 time =
              pointwiseMassCoordinateSliceCLM coordinate
                ((0 : SpaceTimeState requestedTime) time) :=
      eventually_countable_forall.2 zeroSliceAE
    apply MeasureTheory.Lp.ext
    filter_upwards [allSliceAE, allZeroSliceAE] with time timeEq zeroTimeEq
    apply lp.ext
    funext wave
    funext coordinate
    have sliceAtTimeEq :
        wholeSpaceTimeEuclideanCoordinateSlice
            requestedTime coordinate state time =
          wholeSpaceTimeEuclideanCoordinateSlice
            requestedTime coordinate 0 time :=
      congrArg (fun value => value time)
        (sliceStateEqZeroState coordinate)
    rw [timeEq coordinate, zeroTimeEq coordinate] at sliceAtTimeEq
    have coordinateValueEq :=
      congrArg (fun value => value wave) sliceAtTimeEq
    simpa only [pointwiseMassCoordinateSliceCLM_apply] using coordinateValueEq
  · rintro rfl
    unfold wholeSpaceTimeEuclideanMass
    simp

private theorem coordinateSpaceTimeState_norm_sq_eq_integral
    (requestedTime : ℝ)
    (state :
      MeasureTheory.Lp
        (lp (fun _ : IntegerWavevector => ℂ) 2) 2
        (commonTimeMeasure requestedTime)) :
    ‖state‖ ^ 2 =
      ∫ time,
        ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) := by
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  norm_num
  have powerIdentity :
      ((∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime)) ^
            ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  convert powerIdentity using 1
  all_goals norm_num

/-- The quadratic whole-carrier payment is exactly the time integral of the
pointwise Euclidean Fourier mass. -/
theorem wholeSpaceTimeEuclideanMass_eq_integral
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    wholeSpaceTimeEuclideanMass requestedTime state =
      ∫ time,
        wholeVorticityEuclideanMass (state time)
          ∂(commonTimeMeasure requestedTime) := by
  have sliceIntegrable :
      ∀ coordinate : Coordinate,
        Integrable
          (fun time =>
            ‖wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate state time‖ ^ 2)
          (commonTimeMeasure requestedTime) := by
    intro coordinate
    exact
      (MeasureTheory.Lp.memLp
        (wholeSpaceTimeEuclideanCoordinateSlice
          requestedTime coordinate state)).integrable_norm_pow
        (by norm_num)
  have sliceAE :
      ∀ coordinate : Coordinate,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate state time =
            pointwiseMassCoordinateSliceCLM coordinate (state time) := by
    intro coordinate
    have mapAE :=
      (pointwiseMassCoordinateSliceCLM coordinate).coeFn_compLpL state
    filter_upwards [mapAE] with time timeEq
    exact timeEq
  have allSliceAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ coordinate : Coordinate,
          wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate state time =
            pointwiseMassCoordinateSliceCLM coordinate (state time) :=
    eventually_countable_forall.2 sliceAE
  unfold wholeSpaceTimeEuclideanMass
  calc
    (∑ coordinate : Coordinate,
        ‖wholeSpaceTimeEuclideanCoordinateSlice
          requestedTime coordinate state‖ ^ 2) =
        ∑ coordinate : Coordinate,
          ∫ time,
            ‖wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate state time‖ ^ 2
              ∂(commonTimeMeasure requestedTime) := by
      apply Finset.sum_congr rfl
      intro coordinate _coordinateMem
      exact coordinateSpaceTimeState_norm_sq_eq_integral
        requestedTime
        (wholeSpaceTimeEuclideanCoordinateSlice
          requestedTime coordinate state)
    _ =
        ∫ time,
          ∑ coordinate : Coordinate,
            ‖wholeSpaceTimeEuclideanCoordinateSlice
              requestedTime coordinate state time‖ ^ 2
          ∂(commonTimeMeasure requestedTime) := by
      symm
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun coordinate _coordinateMem => sliceIntegrable coordinate)
    _ =
        ∫ time,
          wholeVorticityEuclideanMass (state time)
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [allSliceAE] with time timeEq
      rw [
        wholeVorticityEuclideanMass_eq_pointwiseMassCoordinateSlices]
      apply Finset.sum_congr rfl
      intro coordinate _coordinateMem
      rw [timeEq coordinate]

/-- On an actual continuous whole trajectory the carrier payment is the
literal physical-time integral of its Euclidean Fourier mass. -/
theorem
    wholeSpaceTimeEuclideanMass_wholeTrajectorySpaceTimePath_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime)) :
    wholeSpaceTimeEuclideanMass requestedTime
        (wholeTrajectorySpaceTimePath requestedTime trajectory
          trajectoryContinuous) =
      ∫ time in (0 : ℝ)..requestedTime,
        wholeVorticityEuclideanMass (trajectory time) := by
  rw [wholeSpaceTimeEuclideanMass_eq_integral]
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (wholeTrajectoryBoundedPath requestedTime trajectory
        trajectoryContinuous)
  calc
    (∫ time,
        wholeVorticityEuclideanMass
          (wholeTrajectorySpaceTimePath requestedTime trajectory
            trajectoryContinuous time)
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          wholeVorticityEuclideanMass (trajectory time.1)
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [pathAE] with time timeEq
      change
        wholeVorticityEuclideanMass
            (((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ)
              (wholeTrajectoryBoundedPath requestedTime trajectory
                trajectoryContinuous)) time) =
          wholeVorticityEuclideanMass (trajectory time.1)
      rw [timeEq]
      rfl
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          wholeVorticityEuclideanMass (trajectory time) :=
      commonTime_integral_eq_intervalIntegral
        requestedTime requestedTimeNonneg
        (fun time => wholeVorticityEuclideanMass (trajectory time))

/-- Strong convergence in the existing whole space-time carrier preserves
the complete Euclidean vorticity payment. -/
theorem tendsto_wholeSpaceTimeEuclideanMass
    {requestedTime : ℝ}
    {states : ℕ → SpaceTimeState requestedTime}
    {limit : SpaceTimeState requestedTime}
    (statesTendsto : Tendsto states atTop (𝓝 limit)) :
    Tendsto
      (fun index =>
        wholeSpaceTimeEuclideanMass requestedTime (states index))
      atTop
      (𝓝 (wholeSpaceTimeEuclideanMass requestedTime limit)) := by
  unfold wholeSpaceTimeEuclideanMass
  apply tendsto_finsetSum Finset.univ
  intro coordinate _coordinateMem
  exact
    (((wholeSpaceTimeEuclideanCoordinateSlice
      requestedTime coordinate).continuous.tendsto limit).comp
        statesTendsto).norm.pow 2

private theorem ae_comp_commonTimeInclusion
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    {predicate : Icc (0 : ℝ) Tbig → Prop}
    (eventuallyBig :
      ∀ᵐ time ∂(commonTimeMeasure Tbig), predicate time) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      predicate (commonTimeInclusion timeLe time) := by
  have onImage :
      ∀ᵐ time ∂
          (commonTimeMeasure Tbig).restrict
            (Set.range (commonTimeInclusion timeLe)),
        predicate time :=
    MeasureTheory.ae_restrict_le eventuallyBig
  exact
    (commonTimeInclusion_measurePreserving timeLe
      |>.quasiMeasurePreserving.tendsto_ae) onImage

/-- Restriction to an actual shorter physical-time carrier, promoted to a
continuous linear map.  Its operator norm is at most one because the target
measure is literally the restricted source measure. -/
noncomputable def restrictCommonTimeLpCLM
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig) :
    MeasureTheory.Lp E p (commonTimeMeasure Tbig) →L[ℂ]
      MeasureTheory.Lp E p (commonTimeMeasure Tsmall) :=
  LinearMap.mkContinuous
    { toFun := restrictCommonTimeLp timeLe
      map_add' := by
        intro left right
        apply MeasureTheory.Lp.ext
        filter_upwards [
          restrictCommonTimeLp_apply_ae timeLe (left + right),
          restrictCommonTimeLp_apply_ae timeLe left,
          restrictCommonTimeLp_apply_ae timeLe right,
          MeasureTheory.Lp.coeFn_add
            (restrictCommonTimeLp timeLe left)
            (restrictCommonTimeLp timeLe right),
          ae_comp_commonTimeInclusion timeLe
            (MeasureTheory.Lp.coeFn_add left right)] with
            time sumEq leftEq rightEq restrictedAddEq sourceAddEq
        rw [sumEq, sourceAddEq, restrictedAddEq]
        simp only [Pi.add_apply]
        rw [leftEq, rightEq]
      map_smul' := by
        intro coefficient value
        apply MeasureTheory.Lp.ext
        filter_upwards [
          restrictCommonTimeLp_apply_ae timeLe (coefficient • value),
          restrictCommonTimeLp_apply_ae timeLe value,
          MeasureTheory.Lp.coeFn_smul ((RingHom.id ℂ) coefficient)
            (restrictCommonTimeLp timeLe value),
          ae_comp_commonTimeInclusion timeLe
            (MeasureTheory.Lp.coeFn_smul coefficient value)] with
            time smulEq valueEq restrictedSmulEq sourceSmulEq
        rw [smulEq, sourceSmulEq, restrictedSmulEq]
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [valueEq] }
    1
    (fun value => by
      change
        ‖restrictCommonTimeLp timeLe value‖ ≤ 1 * ‖value‖
      simpa only [one_mul] using
        restrictCommonTimeLp_norm_le timeLe value)

@[simp] theorem restrictCommonTimeLpCLM_apply
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (value : MeasureTheory.Lp E p (commonTimeMeasure Tbig)) :
    restrictCommonTimeLpCLM timeLe value =
      restrictCommonTimeLp timeLe value :=
  rfl

/-- Restricting the `L²` representative of a continuous whole trajectory
is exactly the representative of the same trajectory on the shorter actual
time carrier. -/
theorem restrictCommonTimeLp_wholeTrajectorySpaceTimePath
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) Tbig)) :
    restrictCommonTimeLp timeLe
        (wholeTrajectorySpaceTimePath Tbig trajectory
          trajectoryContinuous) =
      wholeTrajectorySpaceTimePath Tsmall trajectory
        (trajectoryContinuous.mono fun _time timeMem =>
          ⟨timeMem.1, timeMem.2.trans timeLe⟩) := by
  let smallContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) Tsmall) :=
    trajectoryContinuous.mono fun time timeMem =>
      ⟨timeMem.1, timeMem.2.trans timeLe⟩
  have boundedPathEq :
      (wholeTrajectoryBoundedPath Tbig trajectory trajectoryContinuous
          |>.compContinuous (commonTimeInclusion timeLe)) =
        wholeTrajectoryBoundedPath Tsmall trajectory smallContinuous := by
    apply BoundedContinuousFunction.ext
    intro time
    rfl
  unfold wholeTrajectorySpaceTimePath
  rw [← boundedContinuousFunction_toLp_compContinuous timeLe
    (wholeTrajectoryBoundedPath Tbig trajectory trajectoryContinuous)]
  congr 1


/-- The complete Euclidean payment accumulated before one actual time in a
larger whole receipt. -/
def wholePrefixVorticityMass
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    (state : SpaceTimeState requestedTime) : ℝ :=
  wholeSpaceTimeEuclideanMass time.1
    (restrictCommonTimeLpCLM time.2.2 state)

theorem wholePrefixVorticityMass_nonneg
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    (state : SpaceTimeState requestedTime) :
    0 ≤ wholePrefixVorticityMass time state :=
  wholeSpaceTimeEuclideanMass_nonneg time.1
    (restrictCommonTimeLpCLM time.2.2 state)

/-- A prefix payment is zero exactly when its actual restricted space-time
state is zero.  This is the zero-defect rigidity face of the native kinetic
ledger, not a definition of a synthetic terminal state. -/
theorem wholePrefixVorticityMass_eq_zero_iff
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    (state : SpaceTimeState requestedTime) :
    wholePrefixVorticityMass time state = 0 ↔
      restrictCommonTimeLpCLM time.2.2 state = 0 := by
  unfold wholePrefixVorticityMass
  exact wholeSpaceTimeEuclideanMass_eq_zero_iff _ _

/-- Strong whole-carrier convergence remains strong after the actual prefix
restriction and therefore preserves its complete Euclidean payment. -/
theorem tendsto_wholePrefixVorticityMass
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    {states : ℕ → SpaceTimeState requestedTime}
    {limit : SpaceTimeState requestedTime}
    (statesTendsto : Tendsto states atTop (𝓝 limit)) :
    Tendsto
      (fun index => wholePrefixVorticityMass time (states index))
      atTop
      (𝓝 (wholePrefixVorticityMass time limit)) := by
  apply tendsto_wholeSpaceTimeEuclideanMass
  exact
    ((restrictCommonTimeLpCLM time.2.2).continuous.tendsto limit).comp
      statesTendsto

/-- The source-independent prefix functional agrees exactly with the
physical interval integral on every actual continuous whole trajectory. -/
theorem wholePrefixVorticityMass_wholeTrajectorySpaceTimePath_eq_intervalIntegral
    {requestedTime : ℝ}
    (time : Icc (0 : ℝ) requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime)) :
    wholePrefixVorticityMass time
        (wholeTrajectorySpaceTimePath requestedTime trajectory
          trajectoryContinuous) =
      ∫ actual in (0 : ℝ)..time.1,
        wholeVorticityEuclideanMass (trajectory actual) := by
  unfold wholePrefixVorticityMass
  rw [restrictCommonTimeLpCLM_apply]
  rw [restrictCommonTimeLp_wholeTrajectorySpaceTimePath
    time.2.2 trajectory trajectoryContinuous]
  exact
    wholeSpaceTimeEuclideanMass_wholeTrajectorySpaceTimePath_eq_intervalIntegral
      time.1 time.2.1 trajectory
      (trajectoryContinuous.mono fun actual actualMem =>
        ⟨actualMem.1, actualMem.2.trans time.2.2⟩)

/-! ## Exact finite replay payment -/

/-- Every canonical unforced Galerkin replay pays its kinetic decrease and
its complete unweighted vorticity integral on the same actual prefix.  The
right side is the exact whole restart state from which this stage was
generated. -/
theorem canonicalStage_kineticDissipation_le
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
    puncturedWholeVorticityKineticMass (stage.trajectory time.1) +
        2 * nu.coeff *
          wholePrefixVorticityMass time
            (wholeTrajectorySpaceTimePath
              (wholeRestartDuration contact) stage.trajectory
              (HasDerivAt.continuousOn fun actual actualMem =>
                (stage.physical actual actualMem).1)) ≤
      puncturedWholeVorticityKineticMass contact.physicalState := by
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
  have initialKineticLe :
      2 * finiteStateVorticityKineticEnergy modes
          (stage.trajectory 0) ≤
        puncturedWholeVorticityKineticMass contact.physicalState := by
    calc
      2 * finiteStateVorticityKineticEnergy modes
            (stage.trajectory 0) =
          2 * finiteStateVorticityKineticEnergy modes
            (wholeRestartInitialState contact radius) := by
        rw [stage.initial]
      _ ≤ puncturedWholeVorticityKineticMass
            (wholeRestartInitialState contact radius) :=
        two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
          modes zeroNotMem (wholeRestartInitialState contact radius)
          (wholeRestartInitialState_transverse contact radius)
      _ ≤ puncturedWholeVorticityKineticMass contact.physicalState :=
        puncturedWholeVorticityKineticMass_sharpSupportProjection_le
          modes zeroNotMem contact.physicalState
  rw [terminalKineticEq, prefixEq]
  linarith

/-! ## Transport to the actual whole replay -/

/-- The strong whole-carrier closure retains the complete kinetic payment
at almost every physical contact time.  Pointwise kinetic mass and the
prefix `L²_t` payment are transported along the same source-generated
subsequence. -/
theorem criticalClosure_kineticDissipation_ae_le
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
      puncturedWholeVorticityKineticMass
            (closure.weakClosure.stateLimit time) +
          2 * nu.coeff *
            wholePrefixVorticityMass time
              closure.weakClosure.stateLimit ≤
        puncturedWholeVorticityKineticMass contact.physicalState := by
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
  apply le_of_tendsto paymentTendsto
  exact Filter.Eventually.of_forall fun index => by
    let stage := replay.current
      (weakClosure.subsequence (pointwiseSubsequence index))
    rw [pathEq index]
    exact canonicalStage_kineticDissipation_le stage time

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
end NavierStokes
end SaturationMonoid
