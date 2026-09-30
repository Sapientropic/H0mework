import H0mework.NavierStokes.PairRestart.PositivePairOccurrenceCascade

/-!
# Positive output-row cascade on the native whole restart chain

The typed pair-occurrence ledger is deliberately finer than the physical
Fourier row seen by the Navier--Stokes equation.  Pair contributions at one
output must first undergo their exact absolutely summable convolution;
only the resulting output-row work is then split into positive and negative
parts.  This is the physical `consume-before-sign` allocation.

Finite accumulated physical time still forces these positive output rows to
be unbounded and nonsummable.  Thus the hard gate does not depend on charging
every positive input pair separately: it survives all exact within-row
interference while retaining the actual segment and output identities.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkCascade

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositivePairOccurrenceCascade

noncomputable section

/-- Index of one physical output row on the chronological whole restart
chain.  All input-pair interference has already been summed at this row. -/
abbrev WholeRestartOutputWorkIndex :=
  ℕ × IntegerWavevector

/-- Positive part of one actual, fully aggregated output-row work. -/
def wholeRestartPositiveOutputWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (occurrence : WholeRestartOutputWorkIndex) : ℝ :=
  max
    (actualWholeRowBilinearWork
      (run initial occurrence.1).contact.prefixReceipt
      occurrence.2)
    0

theorem wholeRestartPositiveOutputWork_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (occurrence : WholeRestartOutputWorkIndex) :
    0 ≤ wholeRestartPositiveOutputWork initial occurrence := by
  exact le_max_right _ _

/-- Positive output work of one actual restart segment on a canonical
finite output inventory. -/
def wholeRestartSegmentPositiveOutputWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  ∑ output ∈ wholeRestartModes radius,
    wholeRestartPositiveOutputWork initial (index, output)

/-- Chronological finite-prefix ledger after exact within-output
interference and before aggregation across distinct output rows. -/
def wholeRestartAccumulatedPositiveOutputWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentPositiveOutputWork initial index radius

theorem wholeRestartSegmentPositiveOutputWork_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    0 ≤ wholeRestartSegmentPositiveOutputWork initial index radius := by
  unfold wholeRestartSegmentPositiveOutputWork
  exact Finset.sum_nonneg fun output _outputMem =>
    wholeRestartPositiveOutputWork_nonneg initial (index, output)

theorem wholeRestartAccumulatedPositiveOutputWork_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    0 ≤
      wholeRestartAccumulatedPositiveOutputWork
        initial length radius := by
  unfold wholeRestartAccumulatedPositiveOutputWork
  exact Finset.sum_nonneg fun index _indexMem =>
    wholeRestartSegmentPositiveOutputWork_nonneg
      initial index radius

/-- Exact convolution at every output is performed before signs are split;
the resulting positive-row ledger still dominates the signed physical
bilinear work. -/
theorem wholeRestartAccumulatedBilinearWork_le_positiveOutputWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedBilinearWork initial length radius ≤
      wholeRestartAccumulatedPositiveOutputWork
        initial length radius := by
  unfold wholeRestartAccumulatedBilinearWork
    wholeRestartAccumulatedPositiveOutputWork
    wholeRestartSegmentBilinearWork
    wholeRestartSegmentPositiveOutputWork
    actualWholeFiniteBilinearWork
  apply Finset.sum_le_sum
  intro index _indexMem
  apply Finset.sum_le_sum
  intro output _outputMem
  exact le_max_left _ _

/-- Finite accumulated physical time forces the positive output-row
rectangles to be unbounded.  All input-pair cancellation within each row has
already occurred. -/
theorem elapsedTime_bddAbove_forces_accumulatedPositiveOutputWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedPositiveOutputWork
          initial index.1 index.2) := by
  intro positiveBounded
  rcases positiveBounded with ⟨upper, upperBound⟩
  apply
    (elapsedTime_bddAbove_forces_accumulatedBilinearWork_unbounded
      initial elapsedBounded)
  refine ⟨upper, ?_⟩
  rintro _ ⟨index, rfl⟩
  exact
    (wholeRestartAccumulatedBilinearWork_le_positiveOutputWork
      initial index.1 index.2).trans
        (upperBound ⟨index, rfl⟩)

/-- The full family of positive output-row works is nonsummable whenever
the native whole restart time accumulates finitely.  This is the row-level
analytic hard gate consumed by weighted `H¹--H⁻¹` estimates. -/
theorem elapsedTime_bddAbove_forces_positiveOutputWork_nonsummable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ Summable (wholeRestartPositiveOutputWork initial) := by
  intro positiveSummable
  have stagePositiveSummable :
      Summable fun index : ℕ =>
        ∑' output : IntegerWavevector,
          wholeRestartPositiveOutputWork initial (index, output) :=
    positiveSummable.prod
  apply
    (elapsedTime_bddAbove_forces_accumulatedPositiveOutputWork_unbounded
      initial elapsedBounded)
  refine
    ⟨∑' occurrence : WholeRestartOutputWorkIndex,
        wholeRestartPositiveOutputWork initial occurrence,
      ?_⟩
  rintro _ ⟨index, rfl⟩
  calc
    wholeRestartAccumulatedPositiveOutputWork
          initial index.1 index.2 =
        ∑ segment ∈ Finset.range index.1,
          ∑ output ∈ wholeRestartModes index.2,
            wholeRestartPositiveOutputWork
              initial (segment, output) := by
      rfl
    _ ≤
        ∑ segment ∈ Finset.range index.1,
          ∑' output : IntegerWavevector,
            wholeRestartPositiveOutputWork
              initial (segment, output) := by
      apply Finset.sum_le_sum
      intro segment _segmentMem
      have outputPositiveSummable :
          Summable fun output : IntegerWavevector =>
            wholeRestartPositiveOutputWork
              initial (segment, output) :=
        positiveSummable.prod_factor segment
      exact
        outputPositiveSummable.sum_le_tsum
          (wholeRestartModes index.2)
          (fun output _outputNotMem =>
            wholeRestartPositiveOutputWork_nonneg
              initial (segment, output))
    _ ≤
        ∑' segment : ℕ,
          ∑' output : IntegerWavevector,
            wholeRestartPositiveOutputWork
              initial (segment, output) := by
      exact
        stagePositiveSummable.sum_le_tsum
          (Finset.range index.1)
          (fun segment _segmentNotMem =>
            tsum_nonneg fun output =>
              wholeRestartPositiveOutputWork_nonneg
                initial (segment, output))
    _ =
        ∑' occurrence : WholeRestartOutputWorkIndex,
          wholeRestartPositiveOutputWork initial occurrence :=
      positiveSummable.tsum_prod.symm

/-! ## Exact comparison with the finer pair-occurrence split -/

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

/-- Exact input-pair aggregation can only reduce the positive charge at a
nonzero output.  This records why the row cascade is the physical consumer
of the finer occurrence ledger rather than a second provenance norm. -/
theorem wholeRestartPositiveOutputWork_le_positivePairOccurrenceWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    wholeRestartPositiveOutputWork initial (index, output) ≤
      ∑' first : IntegerWavevector,
        wholeRestartPositivePairOccurrenceWork
          initial (index, output, first) := by
  have signedSummable :
      Summable fun first : IntegerWavevector =>
        actualWholePairOccurrenceWork
          (run initial index).contact.prefixReceipt output first :=
    (hasSum_actualWholePairOccurrenceWork
      (run initial index).contact.prefixReceipt output).summable
  have positiveSummable :=
    positivePairOccurrenceWork_summable initial index output
  have signedLePositive :
      (∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork
            (run initial index).contact.prefixReceipt output first) ≤
        ∑' first : IntegerWavevector,
          wholeRestartPositivePairOccurrenceWork
            initial (index, output, first) := by
    exact
      Summable.tsum_le_tsum
        (fun first =>
          le_max_left
            (actualWholePairOccurrenceWork
              (run initial index).contact.prefixReceipt output first)
            0)
        signedSummable positiveSummable
  have zeroLePositive :
      0 ≤
        ∑' first : IntegerWavevector,
          wholeRestartPositivePairOccurrenceWork
            initial (index, output, first) :=
    tsum_nonneg fun first =>
      wholeRestartPositivePairOccurrenceWork_nonneg
        initial (index, output, first)
  unfold wholeRestartPositiveOutputWork
  change
    max
        (actualWholeRowBilinearWork
          (run initial index).contact.prefixReceipt output)
        0 ≤ _
  rw [← actualWholeRowPreQuotientWork_eq_bilinearWork]
  rw [← tsum_actualWholePairOccurrenceWork_eq_rowPreQuotientWork
    (run initial index).contact.prefixReceipt output outputNonzero]
  exact max_le signedLePositive zeroLePositive

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkCascade
end NavierStokes
end SaturationMonoid
