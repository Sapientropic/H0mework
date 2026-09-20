import H0mework.Arithmetic.CodePairs.P941

/-!
# Proposition 942: a generated coverage gap produces unit permanent holonomy

P941 rephrased a failed generated coverage check as an explicit missing
residual-energy shell:

```text
rawBranchingSpectrumHasEnergy S k = false
```

This file connects that gap to the confinement language.  If the spectrum also
contains an active cell one unit above the missing shell, then that cell has no
one-unit successor.  Therefore it is exactly a P914 raw unit-permanent-holonomy
cell.

This is the obstruction bridge:

```text
missing energy shell + active upper cell
  -> no unit successor
  -> unit permanent holonomy
```

No prime pair, trace-zero loop, or Goldbach witness is stored in the object.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Energy-shell membership from an actual spectrum cell -/

/-- If a cell with residual energy `k` is present in a finite raw branching
spectrum, then the Boolean energy-shell membership check returns `true`. -/
theorem rawBranchingSpectrumHasEnergy_eq_true_of_mem_energy
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {c : SU7BranchingDecompositionCell n} {k : ℕ}
    (hmem : c ∈ S.cells)
    (henergy :
      rawAtomCodeBranchingDecompositionResidualEnergy c = k) :
    rawBranchingSpectrumHasEnergy S k = true := by
  unfold rawBranchingSpectrumHasEnergy
  exact List.any_eq_true.mpr
    ⟨c, hmem, decide_eq_true_eq.mpr henergy⟩

/-! ## Coverage gaps with an active upper cell -/

/-- A coverage gap that is hit by an active cell one energy unit above it.

This is the local obstruction configuration.  The object stores the missing
shell and the upper active cell; it does not store any successor, prime edge,
or zero-residual witness. -/
structure SU7GeneratedCoverageGapUpperCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) where
  gap : SU7GeneratedSpectrumCoverageGap S maxEnergy
  upperCell : SU7BranchingDecompositionCell n
  upper_mem : upperCell ∈ S.cells
  upper_nonzero :
    rawAtomCodeBranchingDecompositionResidual upperCell ≠ 0
  upper_energy :
    rawAtomCodeBranchingDecompositionResidualEnergy upperCell =
      gap.level + 1

/-- A missing predecessor shell hit by an active upper cell is exactly a raw
unit-permanent-holonomy cell: there is no in-spectrum cell whose residual
energy is one lower. -/
theorem unitPermanentHolonomy_of_coverageGapUpperCell
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {maxEnergy : ℕ}
    (G : SU7GeneratedCoverageGapUpperCell S maxEnergy) :
    SU7RawBranchingUnitPermanentHolonomyCell S G.upperCell := by
  refine rawUnitPermanentHolonomyCell_of_no_unit_successor
    G.upper_mem G.upper_nonzero ?_
  intro next hnext_mem hnext_eq
  have hsucc :
      rawAtomCodeBranchingDecompositionResidualEnergy next + 1 =
        G.gap.level + 1 := by
    rw [hnext_eq, G.upper_energy]
  have hnext_energy :
      rawAtomCodeBranchingDecompositionResidualEnergy next =
        G.gap.level := by
    exact Nat.succ.inj hsucc
  have hhas :
      rawBranchingSpectrumHasEnergy S G.gap.level = true :=
    rawBranchingSpectrumHasEnergy_eq_true_of_mem_energy
      hnext_mem hnext_energy
  rw [G.gap.hasEnergy_false] at hhas
  contradiction

/-- Forbidding unit permanent holonomy forbids every coverage gap that has an
active upper cell. -/
theorem forbidsUnitPermanentHolonomy_forbidsCoverageGapUpperCell
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {maxEnergy : ℕ}
    (hforbid : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S)
    (G : SU7GeneratedCoverageGapUpperCell S maxEnergy) :
    False :=
  hforbid G.upperCell
    (unitPermanentHolonomy_of_coverageGapUpperCell G)

/-- A spectrum forbids active coverage gaps when no missing shell can be hit by
an active upper cell. -/
def SU7GeneratedSpectrumForbidsActiveCoverageGap
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) : Prop :=
  ∀ _G : SU7GeneratedCoverageGapUpperCell S maxEnergy, False

/-- Unit-holonomy confinement implies active coverage-gap exclusion. -/
theorem forbidsActiveCoverageGap_of_forbidsUnitPermanentHolonomy
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ)
    (hforbid : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S) :
    SU7GeneratedSpectrumForbidsActiveCoverageGap S maxEnergy := by
  intro G
  exact forbidsUnitPermanentHolonomy_forbidsCoverageGapUpperCell
    hforbid G

/-! ## Certificate -/

/-- P942 certificate: missing generated energy shells become confinement-visible
unit permanent holonomy as soon as an active upper cell tries to spend into the
missing shell. -/
structure SU7CoverageGapHolonomyBridgeCertificate where
  has_energy_of_member :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      {c : SU7BranchingDecompositionCell n} {k : ℕ},
      c ∈ S.cells ->
      rawAtomCodeBranchingDecompositionResidualEnergy c = k ->
        rawBranchingSpectrumHasEnergy S k = true
  gap_upper_to_unit_holonomy :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      {maxEnergy : ℕ}
      (G : SU7GeneratedCoverageGapUpperCell S maxEnergy),
        SU7RawBranchingUnitPermanentHolonomyCell S G.upperCell
  forbids_unit_holonomy_to_no_active_gap :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ->
        SU7GeneratedSpectrumForbidsActiveCoverageGap S maxEnergy

/-- Canonical P942 gap-to-holonomy bridge certificate. -/
def su7CoverageGapHolonomyBridgeCertificate :
    SU7CoverageGapHolonomyBridgeCertificate where
  has_energy_of_member :=
    rawBranchingSpectrumHasEnergy_eq_true_of_mem_energy
  gap_upper_to_unit_holonomy :=
    unitPermanentHolonomy_of_coverageGapUpperCell
  forbids_unit_holonomy_to_no_active_gap :=
    forbidsActiveCoverageGap_of_forbidsUnitPermanentHolonomy


end
end StandardModelConstraint
end SaturationMonoid
