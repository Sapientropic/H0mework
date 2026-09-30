import Mathlib.Topology.Algebra.InfiniteSum.Real
import H0mework.NavierStokes.GeneratedPaths.ReceiptSquareUniformBound

/-!
# Receipt-square control on an infinite generated shell lineage

This module tests the finite receipt-square estimate against the target
obstruction scenario of an infinite source-generated shell lineage.

An infinite lineage contains a sequence of source currents, a dependent
native step between each adjacent pair, and the equality saying that this
exact pair is the literal output of `generatedIntegerShellRespond`.  Its
response, exact receipt, positive receipt quantum, and every finite
reachability proof are extracted from that source equality; they are not
caller-selected theorem premises.

For every finite prefix, the existing generated-path square mass is exactly
the sum of the squares of the extracted receipt quanta.  If all prefix
endpoints remain in one strict critical regime, the cutoff-independent
finite-path theorem bounds every partial sum by one common constant.
Consequently the infinite receipt-square series is summable, the generated
quanta tend to zero, and receipts above any fixed positive macroscopic
threshold have a uniform prefix-cardinality bound.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare

open scoped BigOperators Topology

open Filter
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareCascadeBound
open ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareUniformBound

noncomputable section

/--
An infinite sequence of source currents whose every dependent adjacent step
is the literal successful response of `generatedIntegerShellRespond`.

The `generated` equality binds both the step and its endpoint to the
deterministic producer.  Neither can be supplied independently to any
downstream theorem.
-/
structure GeneratedIntegerShellInfiniteLineage where
  current : ℕ → RawVorticityFourierSource
  step :
    ∀ index : ℕ,
      GeneratedIntegerShellStep
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedIntegerShellRespond (current index) =
        some ⟨current (index + 1), step index⟩

namespace GeneratedIntegerShellInfiniteLineage

/-- The exact dependent response bound to the source producer. -/
def response
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    Response GeneratedIntegerShellStep (lineage.current index) :=
  ⟨lineage.current (index + 1), lineage.step index⟩

/-- Producer equality for the extracted response. -/
theorem response_generated
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    generatedIntegerShellRespond (lineage.current index) =
      some (lineage.response index) :=
  lineage.generated index

/-- The extracted response ends at the next lineage current. -/
theorem response_next
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    (lineage.response index).1 =
      lineage.current (index + 1) :=
  rfl

/-- Exact source-owned receipt at one lineage occurrence. -/
def receipt
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    GeneratedIntegerShellReceipt where
  current := lineage.current index
  response := lineage.response index
  generated := lineage.response_generated index

@[simp] theorem receipt_current
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    (lineage.receipt index).current = lineage.current index :=
  rfl

theorem receipt_next
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    (lineage.receipt index).next =
      lineage.current (index + 1) :=
  lineage.response_next index

/--
Proof-relevant reachability of every finite prefix, generated recursively
from the actual response equality at each occurrence.
-/
def prefixReachable
    (lineage : GeneratedIntegerShellInfiniteLineage) :
    ∀ length : ℕ,
      GeneratedIntegerShellReachable
        (lineage.current 0) (lineage.current length)
  | 0 => NativeReachable.initial
  | length + 1 =>
      NativeReachable.step
        (lineage.prefixReachable length)
        (lineage.response_generated length)

/-- The prefix contains exactly its first `length` generated occurrences. -/
@[simp] theorem prefixReachable_occurrence
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) :
    (lineage.prefixReachable length).occurrence = length := by
  induction length with
  | zero =>
      rfl
  | succ length inductionHypothesis =>
      simp [prefixReachable, NativeReachable.occurrence,
        inductionHypothesis]

/-- The prefix receipt list is the chronological list of extracted lineage
receipts. -/
theorem prefixReachable_receipts
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) :
    generatedIntegerShellReachableReceipts
        (lineage.prefixReachable length) =
      (List.range length).map lineage.receipt := by
  induction length with
  | zero =>
      rfl
  | succ length inductionHypothesis =>
      change
        (generatedIntegerShellReachableReceipts
            (lineage.prefixReachable length)).concat
              (lineage.receipt length) =
          (List.range (length + 1)).map lineage.receipt
      rw [inductionHypothesis, List.range_succ, List.map_append]
      simp only [List.concat_eq_append, List.map_singleton]

/-- Positive scalar quantum generated by one actual lineage receipt. -/
def receiptQuantum
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) : ℝ :=
  coefficientCarrierNormSq
    (generatedIntegerShellReceiptTrace (lineage.receipt index))

theorem receiptQuantum_pos
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    0 < lineage.receiptQuantum index :=
  generatedIntegerShellReceiptTrace_normSq_pos
    (lineage.receipt index)

theorem receiptQuantum_nonneg
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    0 ≤ lineage.receiptQuantum index :=
  (lineage.receiptQuantum_pos index).le

/-- Existing finite generated-path square mass of one lineage prefix. -/
def prefixReceiptTraceSquareMass
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) : ℝ :=
  generatedPathReceiptTraceSquareMass
    (lineage.prefixReachable length)

/--
Exact prefix ledger: the pre-existing path receipt-square mass is the sum of
the squares of precisely the first `length` source-generated quanta.
-/
theorem prefixReceiptTraceSquareMass_eq_sum_range
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) :
    lineage.prefixReceiptTraceSquareMass length =
      ∑ index ∈ Finset.range length,
        lineage.receiptQuantum index ^ 2 := by
  unfold prefixReceiptTraceSquareMass
    generatedPathReceiptTraceSquareMass
  rw [lineage.prefixReachable_receipts length]
  simp only [List.map_map]
  change
    ((List.range length).map
      (fun index => lineage.receiptQuantum index ^ 2)).sum =
        ∑ index ∈ Finset.range length,
          lineage.receiptQuantum index ^ 2
  simpa only [List.toFinset_range] using
    (List.sum_toFinset
      (fun index => lineage.receiptQuantum index ^ 2)
      (List.nodup_range (n := length))).symm

/--
One critical finite prefix inherits the already proved path-length and
frequency independent receipt-square ceiling.  Only the actual endpoint
margin of this prefix is consumed.
-/
theorem prefixReceiptTraceSquareMass_le_uniform_of_endpointCriticalMargin
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (length : ℕ)
    (endpointCriticalMargin :
      ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport (lineage.current length))
            (generatedComplexVorticityState
              (lineage.current length)
              (generatedSupport (lineage.current length))) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    lineage.prefixReceiptTraceSquareMass length ≤
      uniformReceiptTraceSquareCeiling ν θ := by
  let path : GeneratedCriticalScalePath ν θ :=
    { seed := lineage.current 0
      current := lineage.current length
      arrival := lineage.prefixReachable length
      initialMargin := endpointCriticalMargin }
  simpa [path, uniformReceiptTraceSquareCeiling,
    prefixReceiptTraceSquareMass] using
      ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareUniformBound.GeneratedCriticalScalePath.receiptTraceSquareMass_le_uniform
        path θLtOne

/--
The finite receipt-square cascade itself now drives the classical critical
consumer: if one exact generated prefix spends more than the uniform
viscous receipt-square budget, that same prefix endpoint has crossed the
critical enstrophy threshold.

No infinite-lineage margin, target time, continuation witness, or support
coverage enters the statement.
-/
theorem criticalThresholdCrossing_of_uniform_lt_prefixReceiptTraceSquareMass
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (length : ℕ)
    (budgetExceeded :
      uniformReceiptTraceSquareCeiling ν θ <
        lineage.prefixReceiptTraceSquareMass length) :
    θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
      ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport (lineage.current length))
          (generatedComplexVorticityState
            (lineage.current length)
            (generatedSupport (lineage.current length))) := by
  exact
    generatedIntegerShellReachable_criticalThresholdCrossing_of_uniform_lt_receiptTraceSquareMass
      (lineage.prefixReachable length) ν θ θLtOne
      (by
        simpa [prefixReceiptTraceSquareMass] using budgetExceeded)

/--
Each uniformly critical finite prefix inherits the cutoff-independent
receipt-square ceiling.
-/
theorem prefixReceiptTraceSquareMass_le_uniform
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (length : ℕ) :
    lineage.prefixReceiptTraceSquareMass length ≤
      uniformReceiptTraceSquareCeiling ν θ :=
  lineage.prefixReceiptTraceSquareMass_le_uniform_of_endpointCriticalMargin
    ν θ θLtOne length (criticalMargin length)

/--
An infinite lineage which remains in one strict critical regime has finite
total receipt-square mass.
-/
theorem receiptQuantum_sq_summable
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    Summable (fun index => lineage.receiptQuantum index ^ 2) := by
  apply summable_of_sum_range_le
  · intro index
    exact sq_nonneg _
  · intro length
    rw [← lineage.prefixReceiptTraceSquareMass_eq_sum_range length]
    exact
      lineage.prefixReceiptTraceSquareMass_le_uniform
        ν θ θLtOne criticalMargin length

/--
The generated receipt quantum must decay along every infinite lineage which
stays inside one strict critical regime.
-/
theorem receiptQuantum_tendsto_zero
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    Tendsto lineage.receiptQuantum atTop (𝓝 0) := by
  have squareTendsto :
      Tendsto
        (fun index => lineage.receiptQuantum index ^ 2)
        atTop (𝓝 0) :=
    (lineage.receiptQuantum_sq_summable
      ν θ θLtOne criticalMargin).tendsto_atTop_zero
  have sqrtTendsto :
      Tendsto
        (fun index => Real.sqrt
          (lineage.receiptQuantum index ^ 2))
        atTop (𝓝 (Real.sqrt 0)) :=
    squareTendsto.sqrt
  simpa [Real.sqrt_sq (lineage.receiptQuantum_nonneg _)] using
    sqrtTendsto

/--
Quantitative macroscopic-burst sparsity.  Among the first `length` actual
receipts, the number whose generated quantum is at least `ε` is bounded by
the common square budget divided by `ε²`.
-/
theorem largeReceiptQuantum_prefix_card_le
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ ε : ℝ)
    (θLtOne : θ < 1)
    (εPos : 0 < ε)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (length : ℕ) :
    (((Finset.range length).filter
        fun index => ε ≤ lineage.receiptQuantum index).card : ℝ) ≤
      uniformReceiptTraceSquareCeiling ν θ / ε ^ 2 := by
  let large :
      Finset ℕ :=
    (Finset.range length).filter
      fun index => ε ≤ lineage.receiptQuantum index
  have eachLarge :
      ∀ index ∈ large,
        ε ^ 2 ≤ lineage.receiptQuantum index ^ 2 := by
    intro index indexMem
    have quantumLower :
        ε ≤ lineage.receiptQuantum index :=
      (Finset.mem_filter.mp indexMem).2
    exact
      (sq_le_sq₀ εPos.le
        (lineage.receiptQuantum_nonneg index)).2 quantumLower
  have largeCardCost :
      (large.card : ℝ) * ε ^ 2 ≤
        ∑ index ∈ large,
          lineage.receiptQuantum index ^ 2 := by
    simpa [nsmul_eq_mul] using
      Finset.card_nsmul_le_sum
        large
        (fun index => lineage.receiptQuantum index ^ 2)
        (ε ^ 2) eachLarge
  have largeSumLePrefix :
      (∑ index ∈ large,
          lineage.receiptQuantum index ^ 2) ≤
        ∑ index ∈ Finset.range length,
          lineage.receiptQuantum index ^ 2 := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun index indexMem indexNotLarge => sq_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_pos εPos)).2
  exact
    largeCardCost.trans
      (largeSumLePrefix.trans
        (by
          rw [← lineage.prefixReceiptTraceSquareMass_eq_sum_range length]
          exact
            lineage.prefixReceiptTraceSquareMass_le_uniform
              ν θ θLtOne criticalMargin length))

end GeneratedIntegerShellInfiniteLineage

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
end NavierStokes
end SaturationMonoid
