import H0mework.NavierStokes.InitialData.FiniteSupportComplexTrajectory
import H0mework.NavierStokes.ShellSources.TraceCumulative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# One actual trajectory carrying an arbitrary generated integer-shell path

An arbitrary `GeneratedIntegerShellReachable` path already writes its
pairwise-disjoint shell traces into one endpoint coefficient carrier.  This
module starts the actual finite Galerkin equation at that endpoint.  It does
not concatenate the unrelated local trajectories attached to the individual
edges.

The main result generates one common positive physical time window on which
every receipt trace from the complete path retains more than half of its
initial squared coefficient mass.  Thus all source-written shells coexist on
one actual trajectory, with exact path provenance and no silent shell loss.

This is the first pathwise amplitude/time bridge.  It does not assert that
the trajectory visits the symbolic intermediate source states, and it does
not yet supply a scale-uniform lower bound for the generated time window.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory

open scoped BigOperators Topology ENNReal

open Set
open Filter
open MeasureTheory
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory

noncomputable section

/-! ## Every historical shell survives in the endpoint coefficient table -/

/-- A row written by any receipt on a generated path is preserved literally
in the endpoint source. -/
theorem generatedIntegerShellReachable_endpoint_coefficient_eq_receipt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ receipt.wholeShellModes) :
    generatedVorticityCoefficient current wave =
      generatedVorticityNonlinearCoefficientAt receipt.current wave := by
  induction arrival generalizing receipt wave with
  | initial =>
      simp [generatedIntegerShellReachableReceipts] at receiptMem
  | @step prior arrival response generated inductionHypothesis =>
      rw [generatedIntegerShellReachableReceipts_step,
        List.concat_eq_append] at receiptMem
      simp only [List.mem_append, List.mem_singleton] at receiptMem
      rcases receiptMem with priorMem | lastReceiptEq
      · have priorCoefficient :=
          inductionHypothesis priorMem waveMem
        have nonlinearNonzero :
            generatedVorticityNonlinearCoefficientAt
                receipt.current wave ≠
              0 :=
          generatedVorticityNonlinearCoefficientAt_ne_zero_of_mem_outerShell
            receipt.current receipt.selectedShellSq waveMem
        have priorCoefficientNonzero :
            generatedVorticityCoefficient prior wave ≠ 0 := by
          rw [priorCoefficient]
          exact nonlinearNonzero
        have priorSupportMem : wave ∈ generatedSupport prior := by
          by_contra notMem
          exact priorCoefficientNonzero
            (generatedVorticityCoefficient_eq_zero_of_not_mem
              prior notMem)
        have priorLive : wave ∈ generatedLiveVorticityModes prior :=
          (mem_generatedLiveVorticityModes_iff prior wave).mpr
            ⟨priorSupportMem, priorCoefficientNonzero⟩
        let lastReceipt : GeneratedIntegerShellReceipt :=
          ⟨prior, response, generated⟩
        change
          generatedVorticityCoefficient lastReceipt.next wave =
            generatedVorticityNonlinearCoefficientAt
              receipt.current wave
        rw [lastReceipt.next_eq_extension,
          extendByGeneratedNonlinearShell_preserves_live_coefficient
            prior lastReceipt.selectedShellSq priorLive]
        exact priorCoefficient
      · subst receipt
        let lastReceipt : GeneratedIntegerShellReceipt :=
          ⟨prior, response, generated⟩
        change
          generatedVorticityCoefficient lastReceipt.next wave =
            generatedVorticityNonlinearCoefficientAt
              lastReceipt.current wave
        rw [lastReceipt.next_eq_extension]
        exact
          extendByGeneratedNonlinearShell_newShell_coefficient
            lastReceipt.current lastReceipt.selectedShellSq waveMem

/-- Every flattened coordinate in a historical receipt support belongs to
the generated support of the endpoint source. -/
theorem generatedIntegerShellReachable_receipt_support_subset_endpoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival) :
    (generatedIntegerShellReceiptTrace receipt).support.image Prod.fst ⊆
      generatedSupport current := by
  intro wave waveMem
  rcases Finset.mem_image.mp waveMem with
    ⟨index, indexMem, indexWave⟩
  subst wave
  have receiptWaveMem :
      index.1 ∈ receipt.wholeShellModes :=
    (mem_generatedIntegerShellTrace_support_iff
      receipt.current receipt.selectedShellSq index).mp indexMem |>.1
  have endpointCoefficient :=
    generatedIntegerShellReachable_endpoint_coefficient_eq_receipt
      arrival receiptMem receiptWaveMem
  have traceCoordinateNonzero :
      generatedVorticityNonlinearCoefficientAt
          receipt.current index.1 index.2 ≠
        0 :=
    (mem_generatedIntegerShellTrace_support_iff
      receipt.current receipt.selectedShellSq index).mp indexMem |>.2
  by_contra endpointNotMem
  have endpointZero :=
    generatedVorticityCoefficient_eq_zero_of_not_mem
      current endpointNotMem
  have coordinateZero :
      generatedVorticityCoefficient current index.1 index.2 = 0 := by
    rw [endpointZero]
    rfl
  rw [endpointCoefficient] at coordinateZero
  exact traceCoordinateNonzero coordinateZero

/-! ## Receipt energy on one common physical state -/

/-- Squared coefficient mass of one exact receipt support, evaluated on a
common vorticity state. -/
def receiptSupportEnergy
    (receipt : GeneratedIntegerShellReceipt)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ index ∈ (generatedIntegerShellReceiptTrace receipt).support,
    Complex.normSq (state index.1 index.2)

theorem receiptSupportEnergy_nonneg
    (receipt : GeneratedIntegerShellReceipt)
    (state : ComplexVorticityHilbertState) :
    0 ≤ receiptSupportEnergy receipt state := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- On the endpoint initial state, every historical receipt has exactly its
source-written squared coefficient mass. -/
theorem receiptSupportEnergy_generatedEndpoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival) :
    receiptSupportEnergy receipt
        (generatedComplexVorticityState current
          (generatedSupport current)) =
      coefficientCarrierNormSq
        (generatedIntegerShellReceiptTrace receipt) := by
  classical
  rw [receiptSupportEnergy, coefficientCarrierNormSq]
  apply Finset.sum_congr rfl
  intro index indexMem
  have receiptWaveMem :
      index.1 ∈ receipt.wholeShellModes :=
    (mem_generatedIntegerShellTrace_support_iff
      receipt.current receipt.selectedShellSq index).mp indexMem |>.1
  have endpointWaveMem : index.1 ∈ generatedSupport current :=
    generatedIntegerShellReachable_receipt_support_subset_endpoint
      arrival receiptMem
      (Finset.mem_image.mpr ⟨index, indexMem, rfl⟩)
  rw [generatedComplexVorticityState_apply, if_pos endpointWaveMem,
    generatedIntegerShellReachable_endpoint_coefficient_eq_receipt
      arrival receiptMem receiptWaveMem,
    generatedIntegerShellReceiptTrace_apply, if_pos receiptWaveMem]

/-- Total receipt-supported coefficient mass carried by a complete generated
path on one common state. -/
def pathReceiptSupportEnergy
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ((generatedIntegerShellReachableReceipts arrival).map
    fun receipt => receiptSupportEnergy receipt state).sum

/-- At the endpoint initial state, total receipt-supported mass is exactly
the Pythagorean cumulative trace mass. -/
theorem pathReceiptSupportEnergy_generatedEndpoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    pathReceiptSupportEnergy arrival
        (generatedComplexVorticityState current
          (generatedSupport current)) =
      coefficientCarrierNormSq
        (generatedIntegerShellCumulativeTrace arrival) := by
  rw [pathReceiptSupportEnergy]
  have mapsEqual :
      (generatedIntegerShellReachableReceipts arrival).map
          (fun receipt =>
            receiptSupportEnergy receipt
              (generatedComplexVorticityState current
                (generatedSupport current))) =
        (generatedIntegerShellReachableReceipts arrival).map
          (fun receipt =>
            coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt)) := by
    apply List.map_congr_left
    intro receipt receiptMem
    exact receiptSupportEnergy_generatedEndpoint arrival receiptMem
  rw [mapsEqual,
    generatedIntegerShellCumulativeTrace_normSq]

/-- Per-receipt half-mass bounds sum to a cumulative path half-mass bound.
This is a finite algebraic consumer of the exact Pythagorean ledger. -/
theorem cumulativeTrace_half_le_pathReceiptSupportEnergy
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState)
    (receiptBounds :
      ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
        coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            2 ≤
          receiptSupportEnergy receipt state) :
    coefficientCarrierNormSq
          (generatedIntegerShellCumulativeTrace arrival) /
        2 ≤
      pathReceiptSupportEnergy arrival state := by
  let receipts := generatedIntegerShellReachableReceipts arrival
  have sumBounds :
      ((receipts.map fun receipt =>
        coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt) /
          2).sum) ≤
        ((receipts.map fun receipt =>
          receiptSupportEnergy receipt state).sum) := by
    have finiteSumBounds :
        ∀ rows : List GeneratedIntegerShellReceipt,
          (∀ receipt ∈ rows,
            coefficientCarrierNormSq
                  (generatedIntegerShellReceiptTrace receipt) /
                2 ≤
              receiptSupportEnergy receipt state) →
          ((rows.map fun receipt =>
            coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
              2).sum) ≤
            ((rows.map fun receipt =>
              receiptSupportEnergy receipt state).sum) := by
      intro rows bounds
      induction rows with
      | nil =>
          simp
      | cons head tail inductionHypothesis =>
          simp only [List.map_cons, List.sum_cons]
          exact add_le_add
            (bounds head (by simp))
            (inductionHypothesis fun receipt receiptMem =>
              bounds receipt (by simp [receiptMem]))
    exact finiteSumBounds receipts fun receipt receiptMem =>
      receiptBounds receipt (by simpa [receipts] using receiptMem)
  have halfSum :
      ((receipts.map fun receipt =>
        coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt)).sum) /
          2 =
        ((receipts.map fun receipt =>
          coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            2).sum) := by
    induction receipts with
    | nil =>
        simp
    | cons head tail inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons]
        rw [← inductionHypothesis]
        ring
  rw [generatedIntegerShellCumulativeTrace_normSq,
    pathReceiptSupportEnergy]
  change
    ((receipts.map fun receipt =>
      coefficientCarrierNormSq
        (generatedIntegerShellReceiptTrace receipt)).sum) /
        2 ≤
      ((receipts.map fun receipt =>
        receiptSupportEnergy receipt state).sum)
  rw [halfSum]
  exact sumBounds

/-- Receipt energy is continuous along any differentiable common carrier
trajectory. -/
theorem receiptSupportEnergy_continuousAt_of_hasDerivAt
    (receipt : GeneratedIntegerShellReceipt)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time => receiptSupportEnergy receipt (trajectory time)) t := by
  classical
  unfold receiptSupportEnergy
  let support := (generatedIntegerShellReceiptTrace receipt).support
  change
    ContinuousAt
      (fun time =>
        ∑ index ∈ support,
          Complex.normSq (trajectory time index.1 index.2)) t
  induction support using Finset.induction_on with
  | empty =>
      simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | @insert index support indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      have waveContinuous :
          ContinuousAt (fun time => trajectory time index.1) t :=
        (complexVorticityTrajectoryWave_hasDerivAt
          trajectory t tangent index.1 evolves).continuousAt
      have coordinateContinuous :
          ContinuousAt (fun time => trajectory time index.1 index.2) t :=
        (continuous_apply index.2).continuousAt.comp waveContinuous
      have normSqContinuous :
          ContinuousAt
            (fun time =>
              Complex.normSq (trajectory time index.1 index.2)) t :=
        Complex.continuous_normSq.continuousAt.comp coordinateContinuous
      exact normSqContinuous.add inductionHypothesis

/-- The total receipt-supported path energy is continuous at every time at
which the common trajectory solves the finite Galerkin equation. -/
theorem pathReceiptSupportEnergy_continuousAt_of_hasDerivAt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time => pathReceiptSupportEnergy arrival (trajectory time)) t := by
  unfold pathReceiptSupportEnergy
  let receipts := generatedIntegerShellReachableReceipts arrival
  change
    ContinuousAt
      (fun time =>
        ((receipts.map fun receipt =>
          receiptSupportEnergy receipt (trajectory time)).sum)) t
  induction receipts with
  | nil =>
      simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact
        (receiptSupportEnergy_continuousAt_of_hasDerivAt
          head trajectory t tangent evolves).add inductionHypothesis

theorem eventually_every_receipt_keeps_half_energy
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (ν : ℝ)
    (initial :
      trajectory 0 =
        generatedComplexVorticityState current
          (generatedSupport current))
    (evolvesAtZero :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory 0)) 0) :
    ∀ᶠ time in 𝓝 (0 : ℝ),
      ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
        coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            2 <
          receiptSupportEnergy receipt (trajectory time) := by
  have eachReceipt :
      ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
        ∀ᶠ time in 𝓝 (0 : ℝ),
          coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
              2 <
            receiptSupportEnergy receipt (trajectory time) := by
    intro receipt receiptMem
    have traceNormPos :=
      generatedIntegerShellReceiptTrace_normSq_pos receipt
    have atZero :
        coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            2 <
          receiptSupportEnergy receipt (trajectory 0) := by
      rw [initial,
        receiptSupportEnergy_generatedEndpoint
          arrival receiptMem]
      linarith
    exact
      (receiptSupportEnergy_continuousAt_of_hasDerivAt
        receipt trajectory 0
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory 0))
        evolvesAtZero).eventually
          (eventually_gt_nhds atZero)
  have finiteIntersection :
      ∀ receipts : List GeneratedIntegerShellReceipt,
        (∀ receipt ∈ receipts,
          ∀ᶠ time in 𝓝 (0 : ℝ),
            coefficientCarrierNormSq
                  (generatedIntegerShellReceiptTrace receipt) /
                2 <
              receiptSupportEnergy receipt (trajectory time)) →
        ∀ᶠ time in 𝓝 (0 : ℝ),
          ∀ receipt ∈ receipts,
            coefficientCarrierNormSq
                  (generatedIntegerShellReceiptTrace receipt) /
                2 <
              receiptSupportEnergy receipt (trajectory time) := by
    intro receipts receiptEventually
    induction receipts with
    | nil =>
        simp
    | cons head tail inductionHypothesis =>
        have headEventually :=
          receiptEventually head (by simp)
        have tailEventually :=
          inductionHypothesis fun receipt receiptMem =>
            receiptEventually receipt (by simp [receiptMem])
        filter_upwards [headEventually, tailEventually] with
          time headBound tailBound
        intro receipt receiptMem
        simp only [List.mem_cons] at receiptMem
        rcases receiptMem with receiptEq | receiptMem
        · subst receipt
          exact headBound
        · exact tailBound receipt receiptMem
  exact
    finiteIntersection
      (generatedIntegerShellReachableReceipts arrival)
      eachReceipt

/-! ## Arbitrary-path physical occupancy producer -/

/-- Every finite source-generated shell path writes all of its receipt traces
into one endpoint state, and that endpoint generates one actual Galerkin
trajectory with a common positive window on which no historical shell loses
half of its written coefficient mass.

The theorem has no path list, amplitude, time, coverage, or nonzero premise.
The generated path itself supplies every receipt and every positive trace
mass. -/
theorem generatedIntegerShellReachable_drives_actualPathOccupancy
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (radius occupancyTime : ℝ),
      0 < occupancyTime ∧
        occupancyTime < radius ∧
        trajectory 0 =
          generatedComplexVorticityState current
            (generatedSupport current) ∧
        (∀ t ∈ Ioo (-radius) radius,
          HasDerivAt trajectory
            (finiteStateVorticityGenerator
              (generatedSupport current) ν (trajectory t)) t) ∧
        (∀ t ∈ Ioc (0 : ℝ) occupancyTime,
          ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
            coefficientCarrierNormSq
                  (generatedIntegerShellReceiptTrace receipt) /
                2 <
              receiptSupportEnergy receipt (trajectory t)) ∧
        ∀ t ∈ Ioc (0 : ℝ) occupancyTime,
          coefficientCarrierNormSq
                (generatedIntegerShellCumulativeTrace arrival) /
              2 ≤
            pathReceiptSupportEnergy arrival (trajectory t) := by
  obtain ⟨trajectory, initial, radius, radiusPos, evolves⟩ :=
    exists_finiteStateVorticity_localTrajectory
      (generatedSupport current) ν
      (generatedComplexVorticityState current
        (generatedSupport current))
  have zeroInRadius : (0 : ℝ) ∈ Ioo (-radius) radius := by
    constructor <;> linarith
  have evolvesAtZero := evolves 0 zeroInRadius
  have eventuallyOccupied :=
    eventually_every_receipt_keeps_half_energy
      arrival trajectory ν initial evolvesAtZero
  obtain ⟨liveRadius, liveRadiusPos, liveWithin⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyOccupied
  let occupancyTime := min radius liveRadius / 2
  have commonRadiusPos : 0 < min radius liveRadius :=
    lt_min radiusPos liveRadiusPos
  have occupancyTimePos : 0 < occupancyTime := by
    dsimp [occupancyTime]
    linarith
  have occupancyTimeLtCommon :
      occupancyTime < min radius liveRadius := by
    dsimp [occupancyTime]
    linarith
  have occupancyTimeLtRadius : occupancyTime < radius :=
    lt_of_lt_of_le occupancyTimeLtCommon (min_le_left _ _)
  have occupancyTimeLtLiveRadius : occupancyTime < liveRadius :=
    lt_of_lt_of_le occupancyTimeLtCommon (min_le_right _ _)
  refine
    ⟨trajectory, radius, occupancyTime,
      occupancyTimePos, occupancyTimeLtRadius, initial, evolves, ?_, ?_⟩
  · intro t timeMem receipt receiptMem
    have tPos : 0 < t := timeMem.1
    exact
      liveWithin
        (by
          rw [Real.dist_eq, sub_zero, abs_of_pos tPos]
          exact
            lt_of_le_of_lt timeMem.2 occupancyTimeLtLiveRadius)
        receipt receiptMem
  · intro t timeMem
    apply cumulativeTrace_half_le_pathReceiptSupportEnergy
    intro receipt receiptMem
    exact le_of_lt
      (liveWithin
        (by
          rw [Real.dist_eq, sub_zero, abs_of_pos timeMem.1]
          exact
            lt_of_le_of_lt timeMem.2 occupancyTimeLtLiveRadius)
        receipt receiptMem)

/-- The common pathwise occupancy window has a genuine time-integrated
coefficient cost.  The lower bound couples the generated physical duration
to the exact Pythagorean cumulative trace mass of the arbitrary finite path.

This remains a coefficient-space Galerkin statement.  Identifying its
integrand with physical energy dissipation requires the separate
reality/transversality and Parseval bridge. -/
theorem generatedIntegerShellReachable_drives_integratedCumulativeOccupancy
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (radius occupancyTime : ℝ),
      0 < occupancyTime ∧
        occupancyTime < radius ∧
        trajectory 0 =
          generatedComplexVorticityState current
            (generatedSupport current) ∧
        (∀ t ∈ Ioo (-radius) radius,
          HasDerivAt trajectory
            (finiteStateVorticityGenerator
              (generatedSupport current) ν (trajectory t)) t) ∧
        occupancyTime *
              (coefficientCarrierNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2) ≤
          ∫ t in (0 : ℝ)..occupancyTime,
            pathReceiptSupportEnergy arrival (trajectory t) := by
  obtain
      ⟨trajectory, radius, occupancyTime,
        occupancyTimePos, occupancyTimeLtRadius, initial, evolves,
        _, cumulativeLowerBound⟩ :=
    generatedIntegerShellReachable_drives_actualPathOccupancy
      arrival ν
  have radiusPos : 0 < radius :=
    lt_trans occupancyTimePos occupancyTimeLtRadius
  have pathEnergyContinuousOn :
      ContinuousOn
        (fun t => pathReceiptSupportEnergy arrival (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    have timeInRadius : t ∈ Ioo (-radius) radius := by
      constructor
      · linarith [timeMem.1]
      · exact lt_of_le_of_lt timeMem.2 occupancyTimeLtRadius
    exact
      (pathReceiptSupportEnergy_continuousAt_of_hasDerivAt
        arrival trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (evolves t timeInRadius)).continuousWithinAt
  have pathEnergyIntegrable :
      IntervalIntegrable
        (fun t => pathReceiptSupportEnergy arrival (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le pathEnergyContinuousOn
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ =>
          coefficientCarrierNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2)
        volume 0 occupancyTime :=
    continuous_const.intervalIntegrable 0 occupancyTime
  have pointwiseLowerBound :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        coefficientCarrierNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2 ≤
          pathReceiptSupportEnergy arrival (trajectory t) := by
    intro t timeMem
    by_cases timeZero : t = 0
    · subst t
      rw [initial,
        pathReceiptSupportEnergy_generatedEndpoint]
      linarith [
        coefficientCarrierNormSq_nonneg
          (generatedIntegerShellCumulativeTrace arrival)]
    · exact
        cumulativeLowerBound t
          ⟨lt_of_le_of_ne timeMem.1 (Ne.symm timeZero),
            timeMem.2⟩
  have integralLowerBound :=
    intervalIntegral.integral_mono_on
      occupancyTimePos.le constantIntegrable pathEnergyIntegrable
      pointwiseLowerBound
  refine
    ⟨trajectory, radius, occupancyTime,
      occupancyTimePos, occupancyTimeLtRadius, initial, evolves, ?_⟩
  have normalizedLowerBound :
      occupancyTime *
            coefficientCarrierNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
          2 ≤
        ∫ t in (0 : ℝ)..occupancyTime,
          pathReceiptSupportEnergy arrival (trajectory t) := by
    simpa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      integralLowerBound
  calc
    occupancyTime *
          (coefficientCarrierNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2) =
        occupancyTime *
            coefficientCarrierNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
          2 := by ring
    _ ≤ _ := normalizedLowerBound

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory
end NavierStokes
end SaturationMonoid
