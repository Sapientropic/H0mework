import H0mework.NavierStokes.GeneratedPaths.CriticalEnvelope
import H0mework.NavierStokes.InitialData.FiniteSupportRealityTrajectory
import H0mework.NavierStokes.InitialData.FiniteSupportCriticalSobolev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Viscous enstrophy cost of an arbitrary generated shell path

The source grammar writes pairwise-orthogonal receipt traces on strictly
increasing integer shells.  The common endpoint trajectory theorem shows
that every one of those historical traces remains live on one positive time
window.  Here the same receipts are weighted by their exact squared
frequency.  The resulting cumulative lower bound simultaneously records

```text
physical time * frequency * written amplitude^2.
```

After multiplication by `nu * (2*pi)^2`, this is exactly the normalization
of viscous vorticity-gradient dissipation.  The present module proves the
coefficient-space cost and its inclusion in the complete generated-shell
enstrophy mass.  The separate physical-invariance bridge must still identify
the common trajectory with a real transverse vorticity field before the
integrand is called physical dissipation.

No target shell, cutoff, path length, amplitude lower bound, occupancy time,
or dissipation budget is accepted as a premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathViscousEnstrophyCost

open scoped BigOperators Topology ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
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

noncomputable section

/-! ## Exact shell-weighted receipt support -/

/-- Exact `|k|^2`-weighted mass on the nonzero coordinate support written by
one actual receipt. -/
def receiptSupportEnstrophyMass
    (receipt : GeneratedIntegerShellReceipt)
    (state : ComplexVorticityHilbertState) : ℝ :=
  (receipt.selectedShellSq : ℝ) * receiptSupportEnergy receipt state

/-- Complete historical receipt-support enstrophy mass of an actual path. -/
def pathReceiptSupportEnstrophyMass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ((generatedIntegerShellReachableReceipts arrival).map
    fun receipt => receiptSupportEnstrophyMass receipt state).sum

theorem receiptSupportEnstrophyMass_nonneg
    (receipt : GeneratedIntegerShellReceipt)
    (state : ComplexVorticityHilbertState) :
    0 ≤ receiptSupportEnstrophyMass receipt state := by
  exact mul_nonneg
    (generatedIntegerShellReceipt_selectedShellSq_cast_pos receipt).le
    (receiptSupportEnergy_nonneg receipt state)

theorem pathReceiptSupportEnstrophyMass_nonneg
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState) :
    0 ≤ pathReceiptSupportEnstrophyMass arrival state := by
  exact List.sum_nonneg fun mass massMem => by
    rcases List.mem_map.mp massMem with ⟨receipt, _, rfl⟩
    exact receiptSupportEnstrophyMass_nonneg receipt state

/-- At the generated endpoint, the historical support mass is exactly the
integer-shell moment of the cumulative orthogonal trace. -/
theorem pathReceiptSupportEnstrophyMass_generatedEndpoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    pathReceiptSupportEnstrophyMass arrival
        (generatedComplexVorticityState current (generatedSupport current)) =
      integerShellWeightedNormSq
        (generatedIntegerShellCumulativeTrace arrival) := by
  rw [pathReceiptSupportEnstrophyMass,
    generatedIntegerShellCumulativeTrace_integerShellWeightedNormSq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro receipt receiptMem
  unfold receiptSupportEnstrophyMass
  rw [receiptSupportEnergy_generatedEndpoint arrival receiptMem]

/-! ## No-silent shell-weighted accumulation -/

/-- Per-receipt occupancy bounds aggregate with their actual shell labels.
This is the frequency-weighted analogue of the unweighted path occupancy
ledger. -/
theorem cumulativeTrace_enstrophy_half_le_pathReceiptSupport
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState)
    (receiptBounds :
      ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
        coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            2 ≤
          receiptSupportEnergy receipt state) :
    integerShellWeightedNormSq
          (generatedIntegerShellCumulativeTrace arrival) /
        2 ≤
      pathReceiptSupportEnstrophyMass arrival state := by
  let receipts := generatedIntegerShellReachableReceipts arrival
  have weightedBounds :
      ∀ receipt ∈ receipts,
        (receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
            2 ≤
          receiptSupportEnstrophyMass receipt state := by
    intro receipt receiptMem
    unfold receiptSupportEnstrophyMass
    have bound := receiptBounds receipt (by simpa [receipts] using receiptMem)
    have shellNonneg : 0 ≤ (receipt.selectedShellSq : ℝ) :=
      (generatedIntegerShellReceipt_selectedShellSq_cast_pos receipt).le
    nlinarith [mul_le_mul_of_nonneg_left bound shellNonneg]
  have sumBounds :
      ((receipts.map fun receipt =>
        (receipt.selectedShellSq : ℝ) *
            coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
          2).sum) ≤
        ((receipts.map fun receipt =>
          receiptSupportEnstrophyMass receipt state).sum) := by
    apply List.sum_le_sum
    intro receipt receiptMem
    exact weightedBounds receipt receiptMem
  have halfSum :
      ((receipts.map fun receipt =>
        (receipt.selectedShellSq : ℝ) *
          coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt)).sum) /
          2 =
        ((receipts.map fun receipt =>
          (receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
            2).sum) := by
    induction receipts with
    | nil => simp
    | cons head tail inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons]
        rw [← inductionHypothesis]
        ring
  rw [generatedIntegerShellCumulativeTrace_integerShellWeightedNormSq,
    pathReceiptSupportEnstrophyMass]
  change
    ((receipts.map fun receipt =>
      (receipt.selectedShellSq : ℝ) *
        coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt)).sum) /
        2 ≤
      ((receipts.map fun receipt =>
        receiptSupportEnstrophyMass receipt state).sum)
  rw [halfSum]
  exact sumBounds

/-! ## Inclusion in the complete generated-shell mass -/

/-- The nonzero coordinate support written by a receipt is contained in its
complete whole-shell carrier, so its observed mass cannot exceed the full
shell mass at a later state. -/
theorem receiptSupportEnergy_le_wholeShellVorticityMass
    (receipt : GeneratedIntegerShellReceipt)
    (state : ComplexVorticityHilbertState) :
    receiptSupportEnergy receipt state ≤
      generatedIntegerShellReceiptWholeShellVorticityMass receipt state := by
  classical
  let coefficient : IntegerWavevector → ComplexCoordinateVector :=
    fun wave => state wave
  let value : IntegerWavevector × Coordinate → ℝ :=
    fun index => Complex.normSq (coefficient index.1 index.2)
  change
    (∑ index ∈ (generatedIntegerShellReceiptTrace receipt).support,
      value index) ≤
      ∑ wave ∈ receipt.wholeShellModes,
        ∑ coordinate : Coordinate, value (wave, coordinate)
  calc
    (∑ index ∈ (generatedIntegerShellReceiptTrace receipt).support,
        value index) ≤
        ∑ index ∈ receipt.wholeShellModes ×ˢ (Finset.univ : Finset Coordinate),
          value index := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro index indexMem
        exact Finset.mem_product.mpr
          ⟨(mem_generatedIntegerShellTrace_support_iff
            receipt.current receipt.selectedShellSq index).mp indexMem |>.1,
            Finset.mem_univ index.2⟩
      · intro index indexNotMem indexMem
        exact Complex.normSq_nonneg _
    _ =
        ∑ wave ∈ receipt.wholeShellModes,
          ∑ coordinate : Coordinate, value (wave, coordinate) := by
      rw [Finset.sum_product]

theorem receiptSupportEnstrophyMass_le_wholeShell
    (receipt : GeneratedIntegerShellReceipt)
    (state : ComplexVorticityHilbertState) :
    receiptSupportEnstrophyMass receipt state ≤
      generatedIntegerShellReceiptEnstrophyMass receipt state := by
  exact mul_le_mul_of_nonneg_left
    (receiptSupportEnergy_le_wholeShellVorticityMass receipt state)
    (generatedIntegerShellReceipt_selectedShellSq_cast_pos receipt).le

/-- The exact historical trace cost is bounded by the complete
shell-weighted vorticity mass used in the critical velocity envelope. -/
theorem pathReceiptSupportEnstrophyMass_le_pathWholeShell
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState) :
    pathReceiptSupportEnstrophyMass arrival state ≤
      pathWholeShellEnstrophyMass arrival state := by
  let receipts := generatedIntegerShellReachableReceipts arrival
  unfold pathReceiptSupportEnstrophyMass pathWholeShellEnstrophyMass
  change
    ((receipts.map fun receipt =>
      receiptSupportEnstrophyMass receipt state).sum) ≤
      ((receipts.map fun receipt =>
        generatedIntegerShellReceiptEnstrophyMass receipt state).sum)
  induction receipts with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (receiptSupportEnstrophyMass_le_wholeShell head state)
        inductionHypothesis

/-- The complete generated-shell mass is a literal nonnegative sub-sum of
the endpoint Galerkin carrier's vorticity-gradient mass. -/
theorem pathWholeShellEnstrophyMass_le_endpointFiniteState
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState) :
    pathWholeShellEnstrophyMass arrival state ≤
      finiteStateVorticityEnstrophyMass
        (generatedSupport current) state := by
  rw [pathWholeShellEnstrophyMass_eq_finiteSum,
    finiteStateVorticityEnstrophyMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (generatedIntegerShellReachableWholeShellModes_subset_endpointSupport
      arrival)
  intro wave waveNotMem waveMem
  exact mul_nonneg (integerWaveNormSq_nonneg wave)
    (complexCoordinateAmplitudeSq_nonneg _)

/-- Historical receipt support, complete generated shells, and the full
endpoint carrier form one honest monotone enstrophy-cost chain. -/
theorem pathReceiptSupportEnstrophyMass_le_endpointFiniteState
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (state : ComplexVorticityHilbertState) :
    pathReceiptSupportEnstrophyMass arrival state ≤
      finiteStateVorticityEnstrophyMass
        (generatedSupport current) state :=
  (pathReceiptSupportEnstrophyMass_le_pathWholeShell arrival state).trans
    (pathWholeShellEnstrophyMass_le_endpointFiniteState arrival state)

/-! ## One actual trajectory pays the complete cumulative cost -/

private theorem pathReceiptSupportEnstrophyMass_continuousAt_of_hasDerivAt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        pathReceiptSupportEnstrophyMass arrival (trajectory time)) t := by
  unfold pathReceiptSupportEnstrophyMass
  let receipts := generatedIntegerShellReachableReceipts arrival
  change
    ContinuousAt
      (fun time =>
        ((receipts.map fun receipt =>
          receiptSupportEnstrophyMass receipt (trajectory time)).sum)) t
  induction receipts with
  | nil =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact
        ((receiptSupportEnergy_continuousAt_of_hasDerivAt
          head trajectory t tangent evolves).const_mul
            (head.selectedShellSq : ℝ)).add
          inductionHypothesis

private theorem integratedViscousEnstrophyCost_of_commonTrajectory
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (occupancyTime : ℝ)
    (occupancyTimePos : 0 < occupancyTime)
    (initial :
      trajectory 0 =
        generatedComplexVorticityState current
          (generatedSupport current))
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (generatedSupport current) ν (trajectory t)) t)
    (receiptBounds :
      ∀ t ∈ Ioc (0 : ℝ) occupancyTime,
        ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
          coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
              2 <
            receiptSupportEnergy receipt (trajectory t)) :
    occupancyTime *
          (integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2) ≤
      ∫ t in (0 : ℝ)..occupancyTime,
        pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
  have supportEnstrophyContinuousOn :
      ContinuousOn
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (pathReceiptSupportEnstrophyMass_continuousAt_of_hasDerivAt
        arrival trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (evolves t timeMem)).continuousWithinAt
  have supportEnstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le supportEnstrophyContinuousOn
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ =>
          integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2)
        volume 0 occupancyTime :=
    continuous_const.intervalIntegrable 0 occupancyTime
  have pointwiseLowerBound :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2 ≤
          pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
    intro t timeMem
    by_cases timeZero : t = 0
    · subst t
      rw [initial,
        pathReceiptSupportEnstrophyMass_generatedEndpoint]
      have weightedNonneg :
          0 ≤ integerShellWeightedNormSq
            (generatedIntegerShellCumulativeTrace arrival) := by
        unfold integerShellWeightedNormSq
        exact Finset.sum_nonneg fun index indexMem =>
          mul_nonneg
            (by exact_mod_cast integerWaveShellSq_nonneg index.1)
            (Complex.normSq_nonneg _)
      linarith
    · apply cumulativeTrace_enstrophy_half_le_pathReceiptSupport
      intro receipt receiptMem
      exact le_of_lt
        (receiptBounds t
          ⟨lt_of_le_of_ne timeMem.1 (Ne.symm timeZero), timeMem.2⟩
          receipt receiptMem)
  have integralLowerBound :=
    intervalIntegral.integral_mono_on
      occupancyTimePos.le constantIntegrable supportEnstrophyIntegrable
      pointwiseLowerBound
  have normalizedLowerBound :
      occupancyTime *
            integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
          2 ≤
        ∫ t in (0 : ℝ)..occupancyTime,
          pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
    simpa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      integralLowerBound
  calc
    occupancyTime *
          (integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2) =
        occupancyTime *
            integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
          2 := by ring
    _ ≤ _ := normalizedLowerBound

/-- The arbitrary generated path and the original Galerkin update now live
on one transverse physical carrier.  On a source-generated positive time
window, every historical shell remains non-silent and the same trajectory
pays the exact integrated frequency-amplitude cost.

The trajectory, time, support, transversality, and receipt lower bounds are
all generated in the conclusion. -/
theorem
    generatedIntegerShellReachable_drives_transverseRealityIntegratedViscousEnstrophyCost
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
        occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2) ≤
          ∫ t in (0 : ℝ)..occupancyTime,
            pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
  obtain
      ⟨trajectory, physicalTime, physicalTimePos, initial,
        physicalProperties⟩ :=
    generatedSource_transverseRealityLocalTrajectory current ν
  have zeroTimeMem : (0 : ℝ) ∈ Icc (0 : ℝ) physicalTime :=
    ⟨le_rfl, physicalTimePos.le⟩
  have evolvesAtZero := (physicalProperties 0 zeroTimeMem).1
  have eventuallyOccupied :=
    eventually_every_receipt_keeps_half_energy
      arrival trajectory ν initial evolvesAtZero
  obtain ⟨liveRadius, liveRadiusPos, liveWithin⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyOccupied
  let occupancyTime := min physicalTime liveRadius / 2
  have commonTimePos : 0 < min physicalTime liveRadius :=
    lt_min physicalTimePos liveRadiusPos
  have occupancyTimePos : 0 < occupancyTime := by
    dsimp [occupancyTime]
    linarith
  have occupancyTimeLtCommon :
      occupancyTime < min physicalTime liveRadius := by
    dsimp [occupancyTime]
    linarith
  have occupancyTimeLtPhysical : occupancyTime < physicalTime :=
    lt_of_lt_of_le occupancyTimeLtCommon (min_le_left _ _)
  have occupancyTimeLtLive : occupancyTime < liveRadius :=
    lt_of_lt_of_le occupancyTimeLtCommon (min_le_right _ _)
  have restrictedPhysicalProperties :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport current) ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport current →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t) := by
    intro t timeMem
    exact physicalProperties t
      ⟨timeMem.1,
        le_of_lt (lt_of_le_of_lt timeMem.2 occupancyTimeLtPhysical)⟩
  have receiptBounds :
      ∀ t ∈ Ioc (0 : ℝ) occupancyTime,
        ∀ receipt ∈ generatedIntegerShellReachableReceipts arrival,
          coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
              2 <
            receiptSupportEnergy receipt (trajectory t) := by
    intro t timeMem receipt receiptMem
    exact liveWithin
      (by
        rw [Real.dist_eq, sub_zero, abs_of_pos timeMem.1]
        exact lt_of_le_of_lt timeMem.2 occupancyTimeLtLive)
      receipt receiptMem
  refine
    ⟨trajectory, occupancyTime, occupancyTimePos, initial,
      restrictedPhysicalProperties, ?_⟩
  exact integratedViscousEnstrophyCost_of_commonTrajectory
    arrival ν trajectory occupancyTime occupancyTimePos initial
    (fun t timeMem => (restrictedPhysicalProperties t timeMem).1)
    receiptBounds

/-- Compatibility projection of the reality-preserving path theorem onto
the previously exposed transverse carrier.  The witness is still generated
by the stronger reality-preserving producer. -/
theorem
    generatedIntegerShellReachable_drives_transverseIntegratedViscousEnstrophyCost
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
            ∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
        occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2) ≤
          ∫ t in (0 : ℝ)..occupancyTime,
            pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
  obtain
      ⟨trajectory, occupancyTime, occupancyTimePos, initial,
        physicalProperties, receiptLowerBound⟩ :=
    generatedIntegerShellReachable_drives_transverseRealityIntegratedViscousEnstrophyCost
      arrival ν
  refine
    ⟨trajectory, occupancyTime, occupancyTimePos, initial, ?_,
      receiptLowerBound⟩
  intro t timeMem
  obtain ⟨actual, supported, transverse, reality⟩ :=
    physicalProperties t timeMem
  exact ⟨actual, supported, transverse⟩

/-- Every arbitrary generated shell path forces its exact cumulative
frequency-amplitude trace to be paid by the complete endpoint Galerkin
carrier on one source-generated positive time window.

Unlike the receipt-support lower bound, the right-hand side is now the full
finite-state vorticity-gradient mass consumed by the cutoff-independent
critical Sobolev estimate.  Thus no historical shell cost can disappear
between source write-back and the classical continuation carrier. -/
theorem
    generatedIntegerShellReachable_drives_transverseRealityIntegratedEndpointEnstrophyCost
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
        occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2) ≤
          ∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityEnstrophyMass
              (generatedSupport current) (trajectory t) := by
  obtain
      ⟨trajectory, occupancyTime, occupancyTimePos, initial,
        physicalProperties, receiptLowerBound⟩ :=
    generatedIntegerShellReachable_drives_transverseRealityIntegratedViscousEnstrophyCost
      arrival ν
  have receiptContinuousOn :
      ContinuousOn
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (pathReceiptSupportEnstrophyMass_continuousAt_of_hasDerivAt
        arrival trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (physicalProperties t timeMem).1).continuousWithinAt
  have endpointContinuousOn :
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
  have receiptIntegrable :
      IntervalIntegrable
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le receiptContinuousOn
  have endpointIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass
            (generatedSupport current) (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le endpointContinuousOn
  have integralMonotone :
      (∫ t in (0 : ℝ)..occupancyTime,
          pathReceiptSupportEnstrophyMass arrival (trajectory t)) ≤
        ∫ t in (0 : ℝ)..occupancyTime,
          finiteStateVorticityEnstrophyMass
            (generatedSupport current) (trajectory t) := by
    exact intervalIntegral.integral_mono_on
      occupancyTimePos.le receiptIntegrable endpointIntegrable
      (fun t timeMem =>
        pathReceiptSupportEnstrophyMass_le_endpointFiniteState
          arrival (trajectory t))
  exact
    ⟨trajectory, occupancyTime, occupancyTimePos, initial,
      physicalProperties, receiptLowerBound.trans integralMonotone⟩

/-- Every finite source-generated path produces one actual common Galerkin
trajectory whose time-integrated receipt support pays its exact cumulative
frequency-amplitude cost. -/
theorem generatedIntegerShellReachable_drives_integratedViscousEnstrophyCost
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
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2) ≤
          ∫ t in (0 : ℝ)..occupancyTime,
            pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
  obtain
      ⟨trajectory, radius, occupancyTime,
        occupancyTimePos, occupancyTimeLtRadius, initial, evolves,
        receiptBounds, _⟩ :=
    generatedIntegerShellReachable_drives_actualPathOccupancy arrival ν
  have radiusPos : 0 < radius :=
    lt_trans occupancyTimePos occupancyTimeLtRadius
  have supportEnstrophyContinuousOn :
      ContinuousOn
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    have timeInRadius : t ∈ Ioo (-radius) radius := by
      constructor
      · linarith [timeMem.1]
      · exact lt_of_le_of_lt timeMem.2 occupancyTimeLtRadius
    exact
      (pathReceiptSupportEnstrophyMass_continuousAt_of_hasDerivAt
        arrival trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν (trajectory t))
        (evolves t timeInRadius)).continuousWithinAt
  have supportEnstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le supportEnstrophyContinuousOn
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ =>
          integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2)
        volume 0 occupancyTime :=
    continuous_const.intervalIntegrable 0 occupancyTime
  have pointwiseLowerBound :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2 ≤
          pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
    intro t timeMem
    by_cases timeZero : t = 0
    · subst t
      rw [initial,
        pathReceiptSupportEnstrophyMass_generatedEndpoint]
      have weightedNonneg :
          0 ≤ integerShellWeightedNormSq
            (generatedIntegerShellCumulativeTrace arrival) := by
        unfold integerShellWeightedNormSq
        exact Finset.sum_nonneg fun index indexMem =>
          mul_nonneg
            (by exact_mod_cast integerWaveShellSq_nonneg index.1)
            (Complex.normSq_nonneg _)
      linarith
    · apply cumulativeTrace_enstrophy_half_le_pathReceiptSupport
      intro receipt receiptMem
      exact le_of_lt
        (receiptBounds t
          ⟨lt_of_le_of_ne timeMem.1 (Ne.symm timeZero), timeMem.2⟩
          receipt receiptMem)
  have integralLowerBound :=
    intervalIntegral.integral_mono_on
      occupancyTimePos.le constantIntegrable supportEnstrophyIntegrable
      pointwiseLowerBound
  refine
    ⟨trajectory, radius, occupancyTime,
      occupancyTimePos, occupancyTimeLtRadius, initial, evolves, ?_⟩
  have normalizedLowerBound :
      occupancyTime *
            integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
          2 ≤
        ∫ t in (0 : ℝ)..occupancyTime,
          pathReceiptSupportEnstrophyMass arrival (trajectory t) := by
    simpa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      integralLowerBound
  calc
    occupancyTime *
          (integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
            2) =
        occupancyTime *
            integerShellWeightedNormSq
              (generatedIntegerShellCumulativeTrace arrival) /
          2 := by ring
    _ ≤ _ := normalizedLowerBound

end

end ThreeDimensionalVorticityCoefficientGeneratedPathViscousEnstrophyCost
end NavierStokes
end SaturationMonoid
