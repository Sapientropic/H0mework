import H0mework.NavierStokes.ShellSources.PathTrajectory

/-!
# Whole-receipt persistence data on generated shell paths

The source grammar already writes one nonzero flattened coefficient trace per
successful shell receipt.  This module keeps that whole trace intact.  It
records the source-owned inventory, exact mass

```text
Q(receipt) = coefficientCarrierNormSq(receipt trace),
```

same-shell provenance, pairwise disjointness, and the elementary stability
implication

```text
endpoint-to-state difference energy ≤ Q / 4
  → receipt support energy at the state ≥ Q / 4.
```

No wave, coordinate, nonzero coefficient, amplitude lower bound, time
interval, or target state is selected at a producer mouth.  A later actual
time-increment theorem only has to bound the whole-receipt difference energy.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistence

open scoped BigOperators Function

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory

noncomputable section

/-! ## Whole-support difference carrier -/

/-- Squared coefficient difference on the complete nonzero support written by
one source receipt. -/
def receiptSupportDifferenceEnergy
    (receipt : GeneratedIntegerShellReceipt)
    (left right : ComplexVorticityHilbertState) : ℝ :=
  ∑ index ∈ (generatedIntegerShellReceiptTrace receipt).support,
    Complex.normSq
      (left index.1 index.2 - right index.1 index.2)

theorem receiptSupportDifferenceEnergy_nonneg
    (receipt : GeneratedIntegerShellReceipt)
    (left right : ComplexVorticityHilbertState) :
    0 ≤ receiptSupportDifferenceEnergy receipt left right := by
  unfold receiptSupportDifferenceEnergy
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem complex_normSq_le_two_current_add_difference
    (reference current : ℂ) :
    Complex.normSq reference ≤
      2 *
        (Complex.normSq current +
          Complex.normSq (reference - current)) := by
  rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm]
  have normLe :
      ‖reference‖ ≤ ‖current‖ + ‖reference - current‖ := by
    calc
      ‖reference‖ =
          ‖current + (reference - current)‖ := by
        congr 1
        ring
      _ ≤ ‖current‖ + ‖reference - current‖ :=
        norm_add_le _ _
  have squareLe :
      ‖reference‖ ^ 2 ≤
        (‖current‖ + ‖reference - current‖) ^ 2 :=
    (sq_le_sq₀
      (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr normLe
  nlinarith [sq_nonneg (‖current‖ - ‖reference - current‖)]

/-- Whole-receipt energy at a reference state is controlled by twice the
current support energy plus twice their support difference energy. -/
theorem receiptSupportEnergy_le_two_current_add_difference
    (receipt : GeneratedIntegerShellReceipt)
    (reference current : ComplexVorticityHilbertState) :
    receiptSupportEnergy receipt reference ≤
      2 * receiptSupportEnergy receipt current +
        2 * receiptSupportDifferenceEnergy
          receipt reference current := by
  unfold receiptSupportEnergy receiptSupportDifferenceEnergy
  calc
    (∑ index ∈ (generatedIntegerShellReceiptTrace receipt).support,
      Complex.normSq (reference index.1 index.2)) ≤
        ∑ index ∈
            (generatedIntegerShellReceiptTrace receipt).support,
          2 *
            (Complex.normSq (current index.1 index.2) +
              Complex.normSq
                (reference index.1 index.2 -
                  current index.1 index.2)) := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact
        complex_normSq_le_two_current_add_difference
          (reference index.1 index.2)
          (current index.1 index.2)
    _ =
      2 *
          (∑ index ∈
            (generatedIntegerShellReceiptTrace receipt).support,
            Complex.normSq (current index.1 index.2)) +
        2 *
          (∑ index ∈
            (generatedIntegerShellReceiptTrace receipt).support,
            Complex.normSq
              (reference index.1 index.2 -
                current index.1 index.2)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro index indexMem
      ring

/-! ## Source-owned receipt inventory -/

private theorem reachableReceipts_pairwise_selectedShell_lt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableReceipts arrival).Pairwise
      (fun left right =>
        left.selectedShellSq < right.selectedShellSq) := by
  have shellsPairwise :=
    generatedIntegerShellReachableShells_pairwise_lt arrival
  rw [←
    generatedIntegerShellReachableReceipts_map_selectedShellSq
      arrival] at shellsPairwise
  simpa only [List.pairwise_map] using shellsPairwise

/-- Exact chronological receipts have pairwise-disjoint complete flattened
supports.  The statement remains at receipt level, so downstream sums retain
the native source provenance rather than merely a list of anonymous traces. -/
theorem generatedIntegerShellReachableReceipts_pairwise_support_disjoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableReceipts arrival).Pairwise
      (fun left right =>
        Disjoint
          (generatedIntegerShellReceiptTrace left).support
          (generatedIntegerShellReceiptTrace right).support) := by
  exact
    (reachableReceipts_pairwise_selectedShell_lt arrival).imp
      (fun shellLt =>
        coefficientTrace_support_disjoint_of_selectedShellSq_ne
          (ne_of_lt shellLt))

/-- Every receipt in a generated path carries internally generated positive
mass, every supported coordinate has the receipt's selected shell, and the
common endpoint realizes exactly that complete mass. -/
theorem generatedIntegerShellReachable_receipt_wholePersistenceData
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival) :
    0 <
        coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt) ∧
      (∀ index ∈
          (generatedIntegerShellReceiptTrace receipt).support,
        integerWaveShellSq index.1 = receipt.selectedShellSq) ∧
      receiptSupportEnergy receipt
          (generatedComplexVorticityState current
            (generatedSupport current)) =
        coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt) := by
  exact
    ⟨generatedIntegerShellReceiptTrace_normSq_pos receipt,
      fun index indexMem =>
        shellSq_of_mem_coefficientTrace_support receipt indexMem,
      receiptSupportEnergy_generatedEndpoint arrival receiptMem⟩

/-- The endpoint write-back has no seed/cumulative interference on a
historical receipt support: its whole support energy is exactly the receipt's
own positive trace mass. -/
theorem generatedIntegerShellReachable_endpoint_receiptMass_pos
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival) :
    0 <
      receiptSupportEnergy receipt
        (generatedComplexVorticityState current
          (generatedSupport current)) := by
  rw [receiptSupportEnergy_generatedEndpoint arrival receiptMem]
  exact generatedIntegerShellReceiptTrace_normSq_pos receipt

/-! ## Static quarter-persistence consumer -/

/-- If a state remains within one quarter of the source-written whole-receipt
mass on that receipt's exact support, then at least one quarter of the entire
receipt mass persists in the state.

The difference bound is deliberately a consumer premise here.  The next
actual-update theorem must generate it from elapsed time and the uniform
`L²_t H⁻¹` derivative budget. -/
theorem generatedIntegerShellReachable_receiptEnergy_ge_quarter_of_difference
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival)
    (state : ComplexVorticityHilbertState)
    (differenceSmall :
      receiptSupportDifferenceEnergy receipt
            (generatedComplexVorticityState current
              (generatedSupport current))
            state ≤
        coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            4) :
    coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt) /
        4 ≤
      receiptSupportEnergy receipt state := by
  have referenceBound :=
    receiptSupportEnergy_le_two_current_add_difference
      receipt
      (generatedComplexVorticityState current
        (generatedSupport current))
      state
  rw [receiptSupportEnergy_generatedEndpoint
    arrival receiptMem] at referenceBound
  linarith

end

end ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistence
end NavierStokes
end SaturationMonoid
