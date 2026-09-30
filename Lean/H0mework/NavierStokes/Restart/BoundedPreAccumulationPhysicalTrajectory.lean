import H0mework.NavierStokes.Restart.GlobalPhysicalTrajectory
import H0mework.NavierStokes.Restart.VelocityWeakEndpoint
import H0mework.NavierStokes.KineticRestart.KineticDefectZeroVelocityCompletion

/-!
# The actual bounded pre-accumulation whole trajectory

When the generated elapsed times are bounded, every physical time strictly
below their supremum is still covered by an actual finite native prefix.
The finite-prefix paths form a literal direct system, so their value at such
a time is independent of which later covering prefix is used.

This module takes that stabilized value on `[0, T)`.  It is the bounded-time
counterpart of the existing unbounded global physical trajectory: every
finite prefix and every source-owned receipt chart remains literal.  No
target path, continuation, cutoff, covering sequence, or compatibility
certificate is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory

open scoped ENNReal

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion

noncomputable section

/-! ## Every finite endpoint lies strictly before the accumulation time -/

/-- Strict native time advance prevents any finite prefix from attaining the
bounded supremum of the complete generated run. -/
theorem elapsedTime_lt_wholeRestartVelocityAccumulationTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    elapsedTime initial index <
      wholeRestartVelocityAccumulationTime initial := by
  change
    elapsedTime initial index <
      ⨆ later : ℕ, elapsedTime initial later
  exact
    (elapsedTime_strictMono initial (Nat.lt_succ_self index)).trans_le
      (le_ciSup elapsedBounded (index + 1))

/-! ## Canonical stabilization below the bounded supremum -/

/-- A source-generated finite prefix whose endpoint lies strictly after one
time in `[0, T)`. -/
noncomputable def wholeRestartPreAccumulationCoverIndex
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (_elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) : ℕ :=
  Classical.choose (by
    change ∃ length : ℕ, time.1 < elapsedTime initial length
    exact exists_lt_of_lt_ciSup time.2.2)

theorem wholeRestartPreAccumulationCoverIndex_spec
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :
    time.1 <
      elapsedTime initial
        (wholeRestartPreAccumulationCoverIndex
          initial elapsedBounded time) :=
  Classical.choose_spec (by
    change ∃ length : ℕ, time.1 < elapsedTime initial length
    exact exists_lt_of_lt_ciSup time.2.2)

/-- The unique stabilized value of the actual finite-prefix system on the
bounded pre-accumulation interval. -/
noncomputable def wholeRestartBoundedPreAccumulationPhysicalTrajectory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :
    ComplexVorticityHilbertState :=
  wholeRestartPrefixPhysicalTrajectory initial
    (wholeRestartPreAccumulationCoverIndex
      initial elapsedBounded time) time.1

/-- Any actual finite prefix covering the requested time computes the same
stabilized value. -/
theorem wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial))
    (length : ℕ)
    (timeLe : time.1 ≤ elapsedTime initial length) :
    wholeRestartBoundedPreAccumulationPhysicalTrajectory
        initial elapsedBounded time =
      wholeRestartPrefixPhysicalTrajectory initial length time.1 := by
  let cover :=
    wholeRestartPreAccumulationCoverIndex initial elapsedBounded time
  let upper := max cover length
  have timeLeCover : time.1 ≤ elapsedTime initial cover :=
    (wholeRestartPreAccumulationCoverIndex_spec
      initial elapsedBounded time).le
  calc
    wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time =
        wholeRestartPrefixPhysicalTrajectory initial cover time.1 :=
      rfl
    _ = wholeRestartPrefixPhysicalTrajectory initial upper time.1 :=
      (wholeRestartPrefixPhysicalTrajectory_eq_of_le
        initial (Nat.le_max_left cover length) timeLeCover).symm
    _ = wholeRestartPrefixPhysicalTrajectory initial length time.1 :=
      wholeRestartPrefixPhysicalTrajectory_eq_of_le
        initial (Nat.le_max_right cover length) timeLe

/-! ## Literal finite-prefix charts -/

/-- Embed one completed finite physical interval into the source-generated
pre-accumulation interval. -/
def wholeRestartFinitePrefixPreAccumulationTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ)
    (time : Icc (0 : ℝ) (elapsedTime initial length)) :
    Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial) :=
  ⟨time.1, ⟨time.2.1,
    time.2.2.trans_lt
      (elapsedTime_lt_wholeRestartVelocityAccumulationTime
        initial elapsedBounded length)⟩⟩

@[simp] theorem wholeRestartFinitePrefixPreAccumulationTime_value
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ)
    (time : Icc (0 : ℝ) (elapsedTime initial length)) :
    (wholeRestartFinitePrefixPreAccumulationTime
      initial elapsedBounded length time).1 = time.1 :=
  rfl

/-- The bounded stabilized path restricts literally to every generated
finite-prefix trajectory. -/
theorem wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefixTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ)
    (time : Icc (0 : ℝ) (elapsedTime initial length)) :
    wholeRestartBoundedPreAccumulationPhysicalTrajectory
        initial elapsedBounded
        (wholeRestartFinitePrefixPreAccumulationTime
          initial elapsedBounded length time) =
      wholeRestartPrefixPhysicalTrajectory initial length time.1 :=
  wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
    initial elapsedBounded _ length time.2.2

/-- Every completed finite restriction of the stabilized bounded path is
continuous, because it is literally the corresponding actual prefix. -/
theorem wholeRestartBoundedPreAccumulationPhysicalTrajectory_continuous_prefix
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    Continuous fun time : Icc (0 : ℝ) (elapsedTime initial length) =>
      wholeRestartBoundedPreAccumulationPhysicalTrajectory
        initial elapsedBounded
        (wholeRestartFinitePrefixPreAccumulationTime
          initial elapsedBounded length time) := by
  have prefixContinuous :=
    wholeRestartPrefixPhysicalTrajectory_continuousOn initial length
  rw [continuousOn_iff_continuous_restrict] at prefixContinuous
  apply prefixContinuous.congr
  intro time
  exact
    wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefixTime
      initial elapsedBounded length time |>.symm

/-- The entire stabilized trajectory is continuous on its native half-open
domain.  Continuity is local: each point selects one actual covering prefix,
and direct-system stabilization identifies the generated path with that
prefix on a neighborhood of the point. -/
theorem wholeRestartBoundedPreAccumulationPhysicalTrajectory_continuous
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Continuous
      (wholeRestartBoundedPreAccumulationPhysicalTrajectory
        initial elapsedBounded) := by
  rw [continuous_iff_continuousAt]
  intro time
  let cover :=
    wholeRestartPreAccumulationCoverIndex initial elapsedBounded time
  have timeLtCover : time.1 < elapsedTime initial cover :=
    wholeRestartPreAccumulationCoverIndex_spec
      initial elapsedBounded time
  have timeMem : time.1 ∈ Icc 0 (elapsedTime initial cover) :=
    ⟨time.2.1, timeLtCover.le⟩
  have eventuallyUpper :
      ∀ᶠ later :
          Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)
        in nhds time,
        later.1 ≤ elapsedTime initial cover :=
    continuousAt_subtype_val.eventually
      (eventually_le_nhds timeLtCover)
  have valueTendstoWithin :
      Tendsto
        (fun later :
          Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial) =>
            later.1)
        (nhds time)
        (nhdsWithin time.1 (Icc 0 (elapsedTime initial cover))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨continuousAt_subtype_val,
        eventuallyUpper.mono fun later laterLe =>
          ⟨later.2.1, laterLe⟩⟩
  have prefixContinuousAt :
      ContinuousAt
        (fun later :
          Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial) =>
            wholeRestartPrefixPhysicalTrajectory
              initial cover later.1)
        time :=
    Filter.Tendsto.comp
      (wholeRestartPrefixPhysicalTrajectory_continuousOn
        initial cover time.1 timeMem)
      valueTendstoWithin
  have eventuallyPrefix :
      wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded =ᶠ[nhds time]
        fun later =>
          wholeRestartPrefixPhysicalTrajectory initial cover later.1 :=
    eventuallyUpper.mono fun later laterLe =>
      wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
        initial elapsedBounded later cover laterLe
  exact prefixContinuousAt.congr_of_eventuallyEq eventuallyPrefix

/-! ## Exact actual-receipt charts -/

theorem elapsedTime_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    0 ≤ elapsedTime initial index := by
  calc
    0 = elapsedTime initial 0 := (elapsedTime_zero initial).symm
    _ ≤ elapsedTime initial index :=
      (elapsedTime_strictMono initial).monotone (Nat.zero_le index)

/-- Place one local receipt time on the bounded run's absolute physical
clock.  Its image remains strictly before the accumulation endpoint. -/
def wholeRestartReceiptPreAccumulationTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (localTime :
      Icc (0 : ℝ) (run initial index).contact.time.1) :
    Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial) :=
  ⟨elapsedTime initial index + localTime.1, by
    constructor
    · exact add_nonneg (elapsedTime_nonneg initial index) localTime.2.1
    · calc
        elapsedTime initial index + localTime.1 ≤
            elapsedTime initial (index + 1) := by
          rw [elapsedTime_succ]
          linarith [localTime.2.2]
        _ < wholeRestartVelocityAccumulationTime initial :=
          elapsedTime_lt_wholeRestartVelocityAccumulationTime
            initial elapsedBounded (index + 1)⟩

@[simp] theorem wholeRestartReceiptPreAccumulationTime_value
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (localTime :
      Icc (0 : ℝ) (run initial index).contact.time.1) :
    (wholeRestartReceiptPreAccumulationTime
      initial elapsedBounded index localTime).1 =
        elapsedTime initial index + localTime.1 :=
  rfl

/-- Every closed local-time chart of every actual native receipt is retained
literally by the bounded stabilized path. -/
theorem
    wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_receipt_chart
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (localTime :
      Icc (0 : ℝ) (run initial index).contact.time.1) :
    wholeRestartBoundedPreAccumulationPhysicalTrajectory
        initial elapsedBounded
        (wholeRestartReceiptPreAccumulationTime
          initial elapsedBounded index localTime) =
      (run initial index).contact.prefixReceipt.wholePath localTime := by
  by_cases localTimeZero : localTime.1 = 0
  · have absoluteTimeLe :
        (wholeRestartReceiptPreAccumulationTime
          initial elapsedBounded index localTime).1 ≤
            elapsedTime initial index := by
      change elapsedTime initial index + localTime.1 ≤
        elapsedTime initial index
      rw [localTimeZero, add_zero]
    calc
      wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded
          (wholeRestartReceiptPreAccumulationTime
            initial elapsedBounded index localTime) =
          wholeRestartPrefixPhysicalTrajectory initial index
            (wholeRestartReceiptPreAccumulationTime
              initial elapsedBounded index localTime).1 :=
        wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
          initial elapsedBounded _ index absoluteTimeLe
      _ = wholeRestartPrefixPhysicalTrajectory initial index
            (elapsedTime initial index) := by
        rw [wholeRestartReceiptPreAccumulationTime_value,
          localTimeZero, add_zero]
      _ = (run initial index).initialState :=
        wholeRestartPrefixPhysicalTrajectory_endpoint initial index
      _ = (run initial index).contact.prefixReceipt.wholePath localTime := by
        let zeroTime :
            Icc (0 : ℝ) (run initial index).contact.time.1 :=
          ⟨0, ⟨le_rfl, (run initial index).contact.time_pos.le⟩⟩
        calc
          (run initial index).initialState =
              (run initial index).contact.prefixReceipt.wholePath zeroTime :=
            (run initial index).contact.prefixReceipt.wholePath_initial.symm
          _ = (run initial index).contact.prefixReceipt.wholePath localTime :=
            congrArg
              (run initial index).contact.prefixReceipt.wholePath
              (Subtype.ext localTimeZero.symm)
  · have localTimePos : 0 < localTime.1 :=
      lt_of_le_of_ne localTime.2.1 (Ne.symm localTimeZero)
    have absoluteTimeMem :
        elapsedTime initial index + localTime.1 ∈
          wholeRestartPhysicalWindow initial index := by
      constructor
      · linarith
      · rw [elapsedTime_succ]
        linarith [localTime.2.2]
    rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
      initial elapsedBounded _ (index + 1) absoluteTimeMem.2]
    change
      wholeRestartPrefixPhysicalTrajectory initial (index + 1)
          (elapsedTime initial index + localTime.1) =
        (run initial index).contact.prefixReceipt.wholePath localTime
    have chart :=
      wholeRestartPrefixPhysicalTrajectory_eq_receipt
        initial (Nat.lt_succ_self index) absoluteTimeMem
    calc
      wholeRestartPrefixPhysicalTrajectory initial (index + 1)
          (elapsedTime initial index + localTime.1) =
          wholeRestartReceiptPhysicalTrajectory
            (run initial index).contact.prefixReceipt localTime.1 := by
        simpa only [add_sub_cancel_left] using chart
      _ = (run initial index).contact.prefixReceipt.wholePath localTime := by
        unfold wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem
          (run initial index).contact.prefixReceipt.requestedTimePos.le
          localTime.2]

/-! ## Physical velocity on the same pre-quotient path -/

/-- Biot--Savart readout of the actual bounded pre-accumulation trajectory.
The source-owned vorticity path remains the authoritative producer. -/
noncomputable def wholeRestartBoundedPreAccumulationVelocityTrajectory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :
    WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState
    (wholeRestartBoundedPreAccumulationPhysicalTrajectory
      initial elapsedBounded time)

/-- Biot--Savart is bounded from the complete whole-vorticity Hilbert
carrier to the punctured physical-velocity carrier.  This is a genuine
whole-carrier estimate; no transverse premise or cutoff is needed. -/
theorem puncturedWholeVelocityEuclideanState_norm_sq_le_kineticMass
    (state : ComplexVorticityHilbertState) :
    ‖puncturedWholeVelocityEuclideanState state‖ ^ 2 ≤
      puncturedWholeVorticityKineticMass state := by
  rw [show
      ‖puncturedWholeVelocityEuclideanState state‖ ^ 2 =
        ∑' wave : NonzeroIntegerWavevector,
          ‖puncturedWholeVelocityEuclideanState state wave‖ ^ 2 by
    convert
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (puncturedWholeVelocityEuclideanState state)) using 1 <;>
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]]
  unfold puncturedWholeVorticityKineticMass
  exact
    Summable.tsum_le_tsum
      (fun wave => by
        change
          ‖euclideanCoordinateRow
              (biotSavartVelocityCoefficient wave.1 (state wave.1))‖ ^ 2 ≤
            complexCoordinateAmplitudeSq (state wave.1) /
              integerWaveViscousMultiplier wave.1
        rw [euclideanCoordinateRow_norm_sq]
        simp only [
          complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
        simpa only [integerWaveViscousMultiplier] using
          biotSavartVelocityCoefficient_normSq_le
            wave.1 (state wave.1) wave.2)
      (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          Memℓp.summable (by norm_num)
            (puncturedWholeVelocityEuclideanState state).2)
      (summable_puncturedWholeVorticityKineticMass state)

/-- The whole Biot--Savart readout is continuous before any endpoint
quotient is taken. -/
theorem continuous_puncturedWholeVelocityEuclideanState :
    Continuous puncturedWholeVelocityEuclideanState := by
  rw [continuous_iff_continuousAt]
  intro state
  rw [Metric.continuousAt_iff']
  intro epsilon epsilonPos
  have differenceTendsto :
      Tendsto
        (fun current : ComplexVorticityHilbertState => current - state)
        (nhds state) (nhds 0) := by
    have differenceContinuous :
        Continuous
          (fun current : ComplexVorticityHilbertState => current - state) := by
      fun_prop
    have atState :
        ContinuousAt
          (fun current : ComplexVorticityHilbertState => current - state)
          state :=
      differenceContinuous.continuousAt
    change
      Tendsto
        (fun current : ComplexVorticityHilbertState => current - state)
        (nhds state)
        (nhds ((fun current : ComplexVorticityHilbertState =>
          current - state) state)) at atState
    simpa only [sub_self] using atState
  have massTendsto :
      Tendsto
        (fun current : ComplexVorticityHilbertState =>
          puncturedWholeVorticityKineticMass (current - state))
        (nhds state) (nhds 0) := by
    have composed :
        Tendsto
          (fun current : ComplexVorticityHilbertState =>
            puncturedWholeVorticityKineticMass (current - state))
          (nhds state)
          (nhds (puncturedWholeVorticityKineticMass 0)) :=
      Filter.Tendsto.comp
        continuous_puncturedWholeVorticityKineticMass.continuousAt
        differenceTendsto
    have massZero :
        puncturedWholeVorticityKineticMass
          (0 : ComplexVorticityHilbertState) = 0 := by
      unfold puncturedWholeVorticityKineticMass
      simp [complexCoordinateAmplitudeSq]
    simpa only [massZero] using composed
  have eventuallyMass :=
    (Metric.tendsto_nhds.mp massTendsto)
      (epsilon ^ 2) (sq_pos_of_pos epsilonPos)
  filter_upwards [eventuallyMass] with current currentClose
  rw [dist_eq_norm, ← puncturedWholeVelocityEuclideanState_sub]
  have squareLe :=
    puncturedWholeVelocityEuclideanState_norm_sq_le_kineticMass
      (current - state)
  have massNonneg :=
    puncturedWholeVorticityKineticMass_nonneg (current - state)
  have massLt :
      puncturedWholeVorticityKineticMass (current - state) <
        epsilon ^ 2 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg massNonneg] using currentClose
  nlinarith [norm_nonneg
    (puncturedWholeVelocityEuclideanState (current - state))]

/-- Consequently the physical-velocity readout of the actual bounded
pre-accumulation path is continuous on its complete half-open domain. -/
theorem wholeRestartBoundedPreAccumulationVelocityTrajectory_continuous
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Continuous
      (wholeRestartBoundedPreAccumulationVelocityTrajectory
        initial elapsedBounded) :=
  continuous_puncturedWholeVelocityEuclideanState.comp
    (wholeRestartBoundedPreAccumulationPhysicalTrajectory_continuous
      initial elapsedBounded)

/-- The absolute endpoint time of one actual contact, as a point strictly
below the bounded accumulation endpoint. -/
def wholeRestartContactEndpointPreAccumulationTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial) :=
  ⟨elapsedTime initial (index + 1),
    ⟨elapsedTime_nonneg initial (index + 1),
      elapsedTime_lt_wholeRestartVelocityAccumulationTime
        initial elapsedBounded (index + 1)⟩⟩

/-- The actual contact endpoints are cofinal in the bounded
pre-accumulation interval. -/
theorem wholeRestartContactEndpointPreAccumulationTime_tendsto_atTop
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (wholeRestartContactEndpointPreAccumulationTime
        initial elapsedBounded)
      atTop atTop := by
  rw [tendsto_atTop]
  intro threshold
  let cover :=
    wholeRestartPreAccumulationCoverIndex
      initial elapsedBounded threshold
  filter_upwards [eventually_ge_atTop cover] with index indexGe
  apply Subtype.coe_le_coe.mp
  change threshold.1 ≤ elapsedTime initial (index + 1)
  exact
    (wholeRestartPreAccumulationCoverIndex_spec
        initial elapsedBounded threshold).le.trans
      ((elapsedTime_strictMono initial).monotone (by omega))

/-- At every actual contact endpoint, the stabilized velocity path is
literally the velocity state generated by that same contact occurrence. -/
theorem wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartBoundedPreAccumulationVelocityTrajectory
        initial elapsedBounded
        (wholeRestartContactEndpointPreAccumulationTime
          initial elapsedBounded index) =
      wholeRestartContactVelocityState initial index := by
  unfold wholeRestartBoundedPreAccumulationVelocityTrajectory
  unfold wholeRestartContactVelocityState
  congr 1
  rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
      initial elapsedBounded _ (index + 1) le_rfl]
  change
    wholeRestartPrefixPhysicalTrajectory initial (index + 1)
        (elapsedTime initial (index + 1)) =
      (run initial index).contact.physicalState
  rw [wholeRestartPrefixPhysicalTrajectory_endpoint,
    run_succ_initialState]

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
end NavierStokes
end SaturationMonoid
