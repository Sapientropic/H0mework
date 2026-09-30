import H0mework.NavierStokes.ShellGluing.NativeMacroWholeResidualFeedback

/-!
# Whole-PDE residual responsibility along the native macro lineage

The redirected macro runtime already generates its own recursive path.  This
module reads the actual whole-PDE responsibility at every current and proves
that the native support write is a literal, non-overlapping accumulation:

```text
support(i+1) = support(i) ∪ missingResidualSupport(i)
card support(L)
  = card support(0) + Σ i<L, card missingResidualSupport(i).
```

Every missing row is a nonzero old whole-PDE residual row.  Its squared
vector mass is therefore positive, while the total mass is zero exactly when
the whole residual is faithfully zero.  Missing supports from distinct macro
occurrences are disjoint because every row is installed before the next
source read.

No path, response, branch, support, residual, nonzero witness, coverage
certificate, horizon, or target solution is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualLineage

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualFeedback

noncomputable section

/-! ## Source-owned support and residual mass at one occurrence -/

/-- The exact old whole-PDE residual at one actual macro current. -/
def lineageOwnedWholeResidual
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    IntegerWavevector → ComplexCoordinateVector :=
  ownedCarrierWholeResidual ν (lineage.current index)

/-- Source-computed support of genuinely missing whole-PDE residual rows. -/
def lineageMissingResidualSupport
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    Finset IntegerWavevector :=
  generatedMissingNonlinearModes
    (lineage.current index).physicalSource

/--
Squared vector mass of all genuinely missing residual rows at one actual
macro occurrence.  Rows already owned by the current carrier are not charged
again.
-/
def lineageWholeResidualQuantum
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : ℝ :=
  ∑ output ∈ lineageMissingResidualSupport lineage index,
    complexCoordinateVectorNormSq
      (lineageOwnedWholeResidual lineage index output)

theorem lineageWholeResidualQuantum_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    0 ≤ lineageWholeResidualQuantum lineage index := by
  unfold lineageWholeResidualQuantum
  exact Finset.sum_nonneg fun output outputMem =>
    complexCoordinateVectorNormSq_nonneg
      (lineageOwnedWholeResidual lineage index output)

theorem lineageMissingResidualRow_ne_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ lineageMissingResidualSupport lineage index) :
    lineageOwnedWholeResidual lineage index output ≠ 0 := by
  simpa [lineageOwnedWholeResidual, lineageMissingResidualSupport,
    ownedCarrierWholeResidual, ownedCarrierTangent,
    currentPhysicalState] using
    currentFullPDEResidual_missing_ne_zero
      (lineage.current index).physicalSource ν.coeff outputMem

/--
The generated scalar mass is faithful to the complete missing-row
inventory.  Positivity is proved from the actual residual rows, not stored
in a certificate.
-/
theorem lineageWholeResidualQuantum_eq_zero_iff_missing_eq_empty
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageWholeResidualQuantum lineage index = 0 ↔
      lineageMissingResidualSupport lineage index = ∅ := by
  constructor
  · intro quantumZero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro output outputMem
    have rowMassZero :
        complexCoordinateVectorNormSq
            (lineageOwnedWholeResidual lineage index output) =
          0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun output outputMem =>
          complexCoordinateVectorNormSq_nonneg
            (lineageOwnedWholeResidual lineage index output))).mp
        quantumZero output outputMem
    exact
      (lineageMissingResidualRow_ne_zero
        lineage index outputMem)
        ((complexCoordinateVectorNormSq_eq_zero_iff
          (lineageOwnedWholeResidual lineage index output)).mp
            rowMassZero)
  · intro missingEmpty
    simp [lineageWholeResidualQuantum, missingEmpty]

/-- The source-generated residual mass vanishes exactly at faithful whole
PDE closure. -/
theorem lineageWholeResidualQuantum_eq_zero_iff_residual_eq_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageWholeResidualQuantum lineage index = 0 ↔
      lineageOwnedWholeResidual lineage index = 0 := by
  rw [lineageWholeResidualQuantum_eq_zero_iff_missing_eq_empty]
  exact
    (ownedCarrierWholeResidual_eq_zero_iff_missingModes_eq_empty
      ν (lineage.current index)).symm

theorem lineageWholeResidualQuantum_pos_iff_residual_ne_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    0 < lineageWholeResidualQuantum lineage index ↔
      lineageOwnedWholeResidual lineage index ≠ 0 := by
  exact
    (lineageWholeResidualQuantum_nonneg lineage index).lt_iff_ne.trans
      (not_congr
        (eq_comm.trans
          (lineageWholeResidualQuantum_eq_zero_iff_residual_eq_zero
            lineage index)))

/-! ## Exact native support accumulation -/

/--
The exact next physical carrier is the old carrier union the whole-PDE
missing support computed at that occurrence.
-/
theorem generatedSupport_succ_eq_union_missingResidualSupport
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    generatedSupport
        (lineage.current (index + 1)).physicalSource =
      generatedSupport (lineage.current index).physicalSource ∪
        lineageMissingResidualSupport lineage index := by
  rw [(lineage.step index).physicalSource_next,
    (redirectedMacroPhysicalReceipt
      ν (lineage.current index)).nextSource_generatedSupport,
    completeOmittedPhysicalLiftSource_generatedSupport]
  rfl

theorem generatedSupport_subset_succ
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    generatedSupport (lineage.current index).physicalSource ⊆
      generatedSupport
        (lineage.current (index + 1)).physicalSource := by
  rw [generatedSupport_succ_eq_union_missingResidualSupport]
  exact Finset.subset_union_left

theorem missingResidualSupport_subset_support_succ
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageMissingResidualSupport lineage index ⊆
      generatedSupport
        (lineage.current (index + 1)).physicalSource := by
  rw [generatedSupport_succ_eq_union_missingResidualSupport]
  exact Finset.subset_union_right

theorem missingResidualSupport_disjoint_currentSupport
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    Disjoint
      (lineageMissingResidualSupport lineage index)
      (generatedSupport (lineage.current index).physicalSource) := by
  apply Finset.disjoint_left.mpr
  intro output outputMissing outputCurrent
  exact
    ((mem_generatedMissingNonlinearModes_iff
      (lineage.current index).physicalSource output).mp
        outputMissing).2 outputCurrent

/-- The physical support is monotone along the actual source-generated macro
lineage. -/
theorem generatedSupport_monotone
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    Monotone
      (fun index =>
        generatedSupport (lineage.current index).physicalSource) := by
  exact monotone_nat_of_le_succ
    (generatedSupport_subset_succ lineage)

/--
Different actual macro occurrences own disjoint new whole-PDE residual rows.
Every row is installed before the next source read, so it cannot be charged
again as missing.
-/
theorem missingResidualSupport_disjoint_of_lt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    {earlier later : ℕ}
    (earlierLtLater : earlier < later) :
    Disjoint
      (lineageMissingResidualSupport lineage earlier)
      (lineageMissingResidualSupport lineage later) := by
  apply Finset.disjoint_left.mpr
  intro output outputEarlier outputLater
  have outputAtNext :
      output ∈
        generatedSupport
          (lineage.current (earlier + 1)).physicalSource :=
    missingResidualSupport_subset_support_succ
      lineage earlier outputEarlier
  have nextLeLater : earlier + 1 ≤ later :=
    Nat.succ_le_iff.mpr earlierLtLater
  have outputAtLater :
      output ∈
        generatedSupport (lineage.current later).physicalSource :=
    generatedSupport_monotone lineage nextLeLater outputAtNext
  exact
    ((mem_generatedMissingNonlinearModes_iff
      (lineage.current later).physicalSource output).mp
        outputLater).2 outputAtLater

/--
Exact one-step cardinality write-back: there is no hidden overlap between
the old physical carrier and the newly generated residual responsibility.
-/
theorem generatedSupport_card_succ
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (generatedSupport
        (lineage.current (index + 1)).physicalSource).card =
      (generatedSupport
        (lineage.current index).physicalSource).card +
        (lineageMissingResidualSupport lineage index).card := by
  rw [generatedSupport_succ_eq_union_missingResidualSupport,
    Finset.card_union_of_disjoint
      (missingResidualSupport_disjoint_currentSupport
        lineage index).symm]

/-- Number of new whole-PDE responsibility rows generated before one actual
macro boundary. -/
def lineageMissingResidualCardPrefix
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) : ℕ :=
  ∑ index ∈ Finset.range length,
    (lineageMissingResidualSupport lineage index).card

/--
Exact arbitrary-prefix support telescope.  This is the native no-silent-loss
ledger for whole-PDE residual responsibility; it counts physical Fourier
rows, not a detached occurrence-memory norm.
-/
theorem generatedSupport_card_eq_initial_add_missingResidualCardPrefix
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ∀ length : ℕ,
      (generatedSupport
          (lineage.current length).physicalSource).card =
        (generatedSupport
          (lineage.current 0).physicalSource).card +
          lineageMissingResidualCardPrefix lineage length
  | 0 => by
      simp [lineageMissingResidualCardPrefix]
  | length + 1 => by
      rw [generatedSupport_card_succ lineage length,
        generatedSupport_card_eq_initial_add_missingResidualCardPrefix
          lineage length]
      simp [lineageMissingResidualCardPrefix,
        Finset.sum_range_succ]
      omega

/-- Squared residual mass accumulated before coefficient quotient over one
actual macro prefix. -/
def lineageWholeResidualSquareMassPrefix
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    lineageWholeResidualQuantum lineage index ^ 2

theorem lineageWholeResidualSquareMassPrefix_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    0 ≤ lineageWholeResidualSquareMassPrefix lineage length := by
  unfold lineageWholeResidualSquareMassPrefix
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualLineage
end NavierStokes
end SaturationMonoid
