import H0mework.Arithmetic.ShellSources.P918

/-!
# Proposition 920: checked raw spectra produce physical zero branch cells

P918 made the finite raw SU(7) branching-spectrum checker executable.  This
file fixes the readout order: a checked spectrum first produces a P909
`SU7GeneratedPhysicalZeroBranchCell` with zero physical residual and locally
generated atom-code primality proofs.  The trace-zero prime-edge loop and
Goldbach readout are then projections of that physical zero cell.

Thus the producer output is not a stored prime pair.  It is a gauge-allowed
physical branch cell whose residual vanishes.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Checked spectra to physical zero cells -/

/-- A checked finite raw spectrum computes a non-storing physical zero branch
cell through the route

`P918 checked spectrum -> P917 coverage -> P910 raw shell -> P909 physical cell`.
-/
def generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_rawBranchingShell
    (rawBranchingShell_of_checkedEnergyShellRule R)

/-- The physical cell produced from a checked finite raw spectrum has zero
physical residual. -/
theorem checkedEnergyShellRule_physicalResidual_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    physicalResidual
      (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule R).cell = 0 :=
  (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule R).residual_zero

/-- The left atom code of the generated physical cell is prime, produced from
the tensor irreducibility filter rather than stored in the checked spectrum. -/
theorem checkedEnergyShellRule_left_atomCode_prime
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    Nat.Prime
      (atomCode
        (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
          R).cell.leftAtom) :=
  (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
    R).left_atomCode_prime

/-- The right atom code of the generated physical cell is prime, produced from
the tensor irreducibility filter rather than stored in the checked spectrum. -/
theorem checkedEnergyShellRule_right_atomCode_prime
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    Nat.Prime
      (atomCode
        (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
          R).cell.rightAtom) :=
  (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
    R).right_atomCode_prime

/-- Zero physical residual of the generated cell gives even-fiber balance in
raw atom codes. -/
theorem checkedEnergyShellRule_atomCode_sum_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    atomCode
      (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
        R).cell.leftAtom +
      atomCode
        (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
          R).cell.rightAtom =
        2 * n :=
  SU7GeneratedPhysicalZeroBranchCell.sum_eq
    (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule R)

/-- The trace-zero prime-edge loop is a projection of the generated physical
zero cell. -/
def traceZeroPrimeEdgeLoop_of_checkedEnergyShellRule_physical
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule R)

/-! ## Fiberwise checked spectra -/

/-- Fiberwise checked spectra produce physical zero branch cells on every even
fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_checkedEnergyShellRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
    (Classical.choice (H n hn))

/-- Fiberwise checked spectra produce trace-zero prime-edge loops by projecting
their generated physical zero branch cells. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_checkedEnergyShellRules_physical
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact
    traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
      (generatedPhysicalZeroBranchCellEveryEvenFiber_of_checkedEnergyShellRules
        H n hn)

/-- Fiberwise checked spectra give ordinary even Goldbach through the physical
zero-cell readout, not through a stored prime-pair readout. -/
theorem evenGoldbach_of_checkedEnergyShellRules_physicalCells
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_checkedEnergyShellRules_physical
      H)

/-! ## Certificate -/

/-- P920 certificate: the checked finite raw-spectrum producer outputs
physical zero branch cells first; prime-edge loops are only projections. -/
structure SU7CheckedSpectrumPhysicalZeroCellProducerCertificate where
  checked_rule_to_physical_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingCheckedEnergyShellRule C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  checked_rule_residual_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawBranchingCheckedEnergyShellRule C n),
      physicalResidual
        (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule R).cell = 0
  checked_rule_left_prime :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawBranchingCheckedEnergyShellRule C n),
      Nat.Prime
        (atomCode
          (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
            R).cell.leftAtom)
  checked_rule_right_prime :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawBranchingCheckedEnergyShellRule C n),
      Nat.Prime
        (atomCode
          (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
            R).cell.rightAtom)
  checked_rule_sum_eq :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawBranchingCheckedEnergyShellRule C n),
      atomCode
        (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
          R).cell.leftAtom +
        atomCode
          (generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
            R).cell.rightAtom =
          2 * n
  checked_rule_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingCheckedEnergyShellRule C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_physical_zero :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C ->
        ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P920 producer certificate. -/
def su7CheckedSpectrumPhysicalZeroCellProducerCertificate :
    SU7CheckedSpectrumPhysicalZeroCellProducerCertificate where
  checked_rule_to_physical_zero :=
    generatedPhysicalZeroBranchCell_of_checkedEnergyShellRule
  checked_rule_residual_zero :=
    checkedEnergyShellRule_physicalResidual_zero
  checked_rule_left_prime :=
    checkedEnergyShellRule_left_atomCode_prime
  checked_rule_right_prime :=
    checkedEnergyShellRule_right_atomCode_prime
  checked_rule_sum_eq :=
    checkedEnergyShellRule_atomCode_sum_eq
  checked_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_checkedEnergyShellRule_physical
  every_fiber_to_physical_zero :=
    generatedPhysicalZeroBranchCellEveryEvenFiber_of_checkedEnergyShellRules
  every_fiber_to_goldbach :=
    evenGoldbach_of_checkedEnergyShellRules_physicalCells


end
end StandardModelConstraint
end SaturationMonoid
