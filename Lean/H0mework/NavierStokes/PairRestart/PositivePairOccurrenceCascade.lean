import H0mework.NavierStokes.PairRestart.PairOccurrenceWork

/-!
# Positive pair-occurrence cascade on the native whole restart chain

Finite accumulated physical time already forces the signed, typed pair work
of the actual whole restart chain to be unbounded.  This module resolves the
remaining sign ambiguity before any occurrence quotient: the positive parts
of the literal `(segment, output, first, output-first)` works cannot be
summable.

The proof stays on one `GeneratedWholeRestartCurrent.run`.  It does not
select a macro reentry, output, input pair, cutoff, critical margin, branch,
or payment certificate.  Consequently the next analytic responsibility is
an upper bound for this exact positive-occurrence series, rather than a
signed-cancellation estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositivePairOccurrenceCascade

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork

noncomputable section

/-- Index of one actual typed pair occurrence on the chronological whole
restart chain. -/
abbrev WholeRestartPairOccurrenceIndex :=
  ℕ × (IntegerWavevector × IntegerWavevector)

/-- Positive part of one actual time-integrated pair occurrence.  The index
retains the segment, output, first input and hence the determined second
input `output - first`. -/
def wholeRestartPositivePairOccurrenceWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (occurrence : WholeRestartPairOccurrenceIndex) : ℝ :=
  max
    (actualWholePairOccurrenceWork
      (run initial occurrence.1).contact.prefixReceipt
      occurrence.2.1 occurrence.2.2)
    0

theorem wholeRestartPositivePairOccurrenceWork_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (occurrence : WholeRestartPairOccurrenceIndex) :
    0 ≤ wholeRestartPositivePairOccurrenceWork initial occurrence := by
  exact le_max_right _ _

private theorem positivePairOccurrenceWork_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      wholeRestartPositivePairOccurrenceWork
        initial (index, output, first) := by
  have signedSummable :
      Summable fun first : IntegerWavevector =>
        actualWholePairOccurrenceWork
          (run initial index).contact.prefixReceipt output first :=
    (hasSum_actualWholePairOccurrenceWork
      (run initial index).contact.prefixReceipt output).summable
  exact
    signedSummable.abs.of_nonneg_of_le
      (fun first =>
        wholeRestartPositivePairOccurrenceWork_nonneg
          initial (index, output, first))
      (fun first =>
        max_le_iff.mpr
          ⟨le_abs_self
              (actualWholePairOccurrenceWork
                (run initial index).contact.prefixReceipt output first),
            abs_nonneg _⟩)

/-- Positive occurrence work of one actual restart segment on a finite
output inventory.  Input-pair identity remains unquotiented. -/
def wholeRestartSegmentPositivePairOccurrenceWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  ∑ output ∈ wholeRestartModes radius,
    ∑' first : IntegerWavevector,
      wholeRestartPositivePairOccurrenceWork
        initial (index, output, first)

/-- Chronological finite-prefix positive occurrence ledger. -/
def wholeRestartAccumulatedPositivePairOccurrenceWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentPositivePairOccurrenceWork
      initial index radius

theorem wholeRestartSegmentPositivePairOccurrenceWork_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    0 ≤ wholeRestartSegmentPositivePairOccurrenceWork
      initial index radius := by
  unfold wholeRestartSegmentPositivePairOccurrenceWork
  exact Finset.sum_nonneg fun output _outputMem =>
    tsum_nonneg fun first =>
      wholeRestartPositivePairOccurrenceWork_nonneg
        initial (index, output, first)

theorem wholeRestartAccumulatedPositivePairOccurrenceWork_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    0 ≤ wholeRestartAccumulatedPositivePairOccurrenceWork
      initial length radius := by
  unfold wholeRestartAccumulatedPositivePairOccurrenceWork
  exact Finset.sum_nonneg fun index _indexMem =>
    wholeRestartSegmentPositivePairOccurrenceWork_nonneg
      initial index radius

/-- Resolving signs occurrence by occurrence can only increase the actual
chronological work. -/
theorem wholeRestartAccumulatedPairOccurrenceWork_le_positive
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedPairOccurrenceWork
        initial length radius ≤
      wholeRestartAccumulatedPositivePairOccurrenceWork
        initial length radius := by
  unfold wholeRestartAccumulatedPairOccurrenceWork
    wholeRestartAccumulatedPositivePairOccurrenceWork
  apply Finset.sum_le_sum
  intro index _indexMem
  unfold wholeRestartSegmentPairOccurrenceWork
    wholeRestartSegmentPositivePairOccurrenceWork
    actualWholeFinitePairOccurrenceWork
  apply Finset.sum_le_sum
  intro output _outputMem
  exact
    Summable.tsum_le_tsum
      (fun first =>
        le_max_left
          (actualWholePairOccurrenceWork
            (run initial index).contact.prefixReceipt output first)
          0)
      (hasSum_actualWholePairOccurrenceWork
        (run initial index).contact.prefixReceipt output).summable
      (positivePairOccurrenceWork_summable initial index output)

/-- Finite accumulated physical time forces the finite-prefix positive
occurrence ledger itself to be unbounded.  This is the rectangle-shaped
consumer needed by prefix receipt-square estimates. -/
theorem elapsedTime_bddAbove_forces_accumulatedPositivePairOccurrenceWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedPositivePairOccurrenceWork
          initial index.1 index.2) := by
  intro positiveBounded
  rcases positiveBounded with ⟨upper, upperBound⟩
  apply
    (elapsedTime_bddAbove_forces_accumulatedPairOccurrenceWork_unbounded
      initial elapsedBounded)
  refine ⟨upper, ?_⟩
  rintro _ ⟨index, rfl⟩
  exact
    (wholeRestartAccumulatedPairOccurrenceWork_le_positive
      initial index.1 index.2).trans
        (upperBound ⟨index, rfl⟩)

/-- Finite accumulated physical time forces a genuinely non-summable
positive cascade of actual typed pair occurrences on the same whole restart
chain.  Hence the earlier signed unboundedness cannot be attributed solely
to cancellation between positive and negative occurrence rows. -/
theorem elapsedTime_bddAbove_forces_positivePairOccurrenceWork_nonsummable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ Summable (wholeRestartPositivePairOccurrenceWork initial) := by
  intro positiveSummable
  have stagePositiveSummable :
      Summable fun index : ℕ =>
        ∑' pair : IntegerWavevector × IntegerWavevector,
          wholeRestartPositivePairOccurrenceWork initial (index, pair) :=
    positiveSummable.prod
  have accumulatedBounded :
      BddAbove
        (Set.range fun index : ℕ × ℕ =>
          wholeRestartAccumulatedPairOccurrenceWork
            initial index.1 index.2) := by
    refine ⟨∑' occurrence : WholeRestartPairOccurrenceIndex,
      wholeRestartPositivePairOccurrenceWork initial occurrence, ?_⟩
    rintro _ ⟨index, rfl⟩
    calc
      wholeRestartAccumulatedPairOccurrenceWork
            initial index.1 index.2 ≤
          wholeRestartAccumulatedPositivePairOccurrenceWork
            initial index.1 index.2 :=
        wholeRestartAccumulatedPairOccurrenceWork_le_positive
          initial index.1 index.2
      _ =
          ∑ segment ∈ Finset.range index.1,
            ∑ output ∈ wholeRestartModes index.2,
              ∑' first : IntegerWavevector,
                wholeRestartPositivePairOccurrenceWork
                  initial (segment, output, first) := by
        rfl
      _ ≤
          ∑ segment ∈ Finset.range index.1,
            ∑' pair : IntegerWavevector × IntegerWavevector,
              wholeRestartPositivePairOccurrenceWork
                initial (segment, pair) := by
        apply Finset.sum_le_sum
        intro segment _segmentMem
        have pairPositiveSummable :
            Summable fun pair : IntegerWavevector × IntegerWavevector =>
              wholeRestartPositivePairOccurrenceWork
                initial (segment, pair) :=
          positiveSummable.prod_factor segment
        have outputPositiveSummable :
            Summable fun output : IntegerWavevector =>
              ∑' first : IntegerWavevector,
                wholeRestartPositivePairOccurrenceWork
                  initial (segment, output, first) :=
          pairPositiveSummable.prod
        calc
          (∑ output ∈ wholeRestartModes index.2,
              ∑' first : IntegerWavevector,
                wholeRestartPositivePairOccurrenceWork
                  initial (segment, output, first)) ≤
              ∑' output : IntegerWavevector,
                ∑' first : IntegerWavevector,
                  wholeRestartPositivePairOccurrenceWork
                    initial (segment, output, first) := by
            exact
              outputPositiveSummable.sum_le_tsum
                (wholeRestartModes index.2)
                (fun output _outputNotMem =>
                  tsum_nonneg fun first =>
                    wholeRestartPositivePairOccurrenceWork_nonneg
                      initial (segment, output, first))
          _ =
              ∑' pair : IntegerWavevector × IntegerWavevector,
                wholeRestartPositivePairOccurrenceWork
                  initial (segment, pair) :=
            pairPositiveSummable.tsum_prod.symm
      _ ≤
          ∑' segment : ℕ,
            ∑' pair : IntegerWavevector × IntegerWavevector,
              wholeRestartPositivePairOccurrenceWork
                initial (segment, pair) := by
        exact
          stagePositiveSummable.sum_le_tsum
            (Finset.range index.1)
            (fun segment _segmentNotMem =>
              tsum_nonneg fun pair =>
                wholeRestartPositivePairOccurrenceWork_nonneg
                  initial (segment, pair))
      _ =
          ∑' occurrence : WholeRestartPairOccurrenceIndex,
            wholeRestartPositivePairOccurrenceWork initial occurrence :=
        positiveSummable.tsum_prod.symm
  exact
    (elapsedTime_bddAbove_forces_accumulatedPairOccurrenceWork_unbounded
      initial elapsedBounded) accumulatedBounded

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositivePairOccurrenceCascade
end NavierStokes
end SaturationMonoid
