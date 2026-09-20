import H0mework.Physics.BranchSources.P921

/-!
# Proposition 922: certified raw cell lists generate local checked spectra

P921 introduced the right executable interface: a finite raw branching spectrum
with tensor irreducibility only for cells in the list.  This file lowers that
interface one step: a generator can emit a list of certified raw cells.  Each
entry contains

* one raw `SU7BranchingDecompositionCell`;
* tensor irreducibility proofs for its two endpoint codes.

It still stores no `Nat.Prime`, no prime pair, and no trace-zero loop.  Lean
forgets the certified list to an ordinary raw spectrum, reconstructs the local
tensor filter by `List.mem_map`, and then uses P921.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Certified raw branching cells -/

/-- A raw branching-decomposition cell with local tensor irreducibility proofs
for its endpoint codes.  This is not a prime-edge cell. -/
structure SU7CertifiedRawBranchingCell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  cell : SU7BranchingDecompositionCell n
  left_tensor_irreducible :
    SU7TensorIrreducible C { code := cell.leftWeightCode }
  right_tensor_irreducible :
    SU7TensorIrreducible C { code := cell.rightWeightCode }

/-- Forget a certified raw cell list to the ordinary raw branching spectrum
that P921 consumes. -/
def rawBranchingSpectrum_of_certifiedCells
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7CertifiedRawBranchingCell C n)) :
    SU7BranchingDecompositionSpectrum n where
  cells := xs.map (fun x => x.cell)

/-- Membership in the forgotten raw spectrum comes from a certified cell. -/
theorem exists_certifiedCell_of_mem_rawBranchingSpectrum
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7CertifiedRawBranchingCell C n))
    {c : SU7BranchingDecompositionCell n}
    (hmem :
      c ∈ (rawBranchingSpectrum_of_certifiedCells xs).cells) :
    ∃ x : SU7CertifiedRawBranchingCell C n,
      x ∈ xs ∧ x.cell = c := by
  unfold rawBranchingSpectrum_of_certifiedCells at hmem
  rcases List.mem_map.mp hmem with ⟨x, hx, hxc⟩
  exact ⟨x, hx, hxc⟩

/-- A certified raw cell list generates P921's membership-scoped tensor
filter. -/
def localTensorFilter_of_certifiedCells
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7CertifiedRawBranchingCell C n)) :
    SU7RawBranchingLocalTensorFilter C
      (rawBranchingSpectrum_of_certifiedCells xs) where
  left_tensor_irreducible := by
    intro c hmem
    rcases exists_certifiedCell_of_mem_rawBranchingSpectrum xs hmem with
      ⟨x, _hx, hxc⟩
    subst c
    exact x.left_tensor_irreducible
  right_tensor_irreducible := by
    intro c hmem
    rcases exists_certifiedCell_of_mem_rawBranchingSpectrum xs hmem with
      ⟨x, _hx, hxc⟩
    subst c
    exact x.right_tensor_irreducible

/-! ## Certified checked lists -/

/-- A checked local energy-shell rule whose spectrum is generated from a
certified raw cell list. -/
structure SU7CertifiedRawBranchingCheckedCellList
    (C : SU7WeightTensorCoding) (n : ℕ) where
  cells : List (SU7CertifiedRawBranchingCell C n)
  startCell : SU7BranchingDecompositionCell n
  start_mem :
    startCell ∈ (rawBranchingSpectrum_of_certifiedCells cells).cells
  maxEnergy : ℕ
  energy_bound :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ (rawBranchingSpectrum_of_certifiedCells cells).cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c ≤ maxEnergy
  coverage_check :
    rawBranchingEnergyShellCoverageCheck
      (rawBranchingSpectrum_of_certifiedCells cells) maxEnergy = true

/-- A certified checked cell list generates P921's checked local energy-shell
rule. -/
def checkedLocalEnergyShellRule_of_certifiedCellList
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7CertifiedRawBranchingCheckedCellList C n) :
    SU7RawBranchingCheckedLocalEnergyShellRule C n where
  spectrum := rawBranchingSpectrum_of_certifiedCells L.cells
  startCell := L.startCell
  start_mem := L.start_mem
  local_tensor_filter := localTensorFilter_of_certifiedCells L.cells
  maxEnergy := L.maxEnergy
  energy_bound := L.energy_bound
  coverage_check := L.coverage_check

/-- A certified checked cell list computes a generated physical zero branch
cell. -/
def generatedPhysicalZeroBranchCell_of_certifiedCellList
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7CertifiedRawBranchingCheckedCellList C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_checkedLocalEnergyShellRule
    (checkedLocalEnergyShellRule_of_certifiedCellList L)

/-- A certified checked cell list computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_certifiedCellList
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7CertifiedRawBranchingCheckedCellList C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_certifiedCellList L)

/-- Every even fiber carries a certified checked raw cell list. -/
def SU7CertifiedRawBranchingCheckedCellListEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7CertifiedRawBranchingCheckedCellList C n)

/-- Fiberwise certified checked cell lists generate P921 checked local rules. -/
def checkedLocalEnergyShellRulesEveryEvenFiber_of_certifiedCellLists
    {C : SU7WeightTensorCoding}
    (H : SU7CertifiedRawBranchingCheckedCellListEveryEvenFiber C) :
    SU7RawBranchingCheckedLocalEnergyShellRuleEveryEvenFiber C := by
  intro n hn
  exact ⟨checkedLocalEnergyShellRule_of_certifiedCellList
    (Classical.choice (H n hn))⟩

/-- Fiberwise certified checked cell lists give ordinary even Goldbach through
P922 -> P921, with no stored prime pair in the producer. -/
theorem evenGoldbach_of_certifiedCellLists
    {C : SU7WeightTensorCoding}
    (H : SU7CertifiedRawBranchingCheckedCellListEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_checkedLocalEnergyShellRules
    (checkedLocalEnergyShellRulesEveryEvenFiber_of_certifiedCellLists H)

/-! ## Certificate -/

/-- P922 certificate: certified raw cell lists generate the checked local
energy-shell interface. -/
structure SU7CertifiedRawCellListProducerCertificate where
  certified_list_to_spectrum :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      List (SU7CertifiedRawBranchingCell C n) ->
        SU7BranchingDecompositionSpectrum n
  certified_list_to_local_filter :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7CertifiedRawBranchingCell C n)),
      SU7RawBranchingLocalTensorFilter C
        (rawBranchingSpectrum_of_certifiedCells xs)
  checked_list_to_rule :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7CertifiedRawBranchingCheckedCellList C n ->
        SU7RawBranchingCheckedLocalEnergyShellRule C n
  checked_list_to_physical_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7CertifiedRawBranchingCheckedCellList C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7CertifiedRawBranchingCheckedCellListEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P922 certified raw-list producer certificate. -/
def su7CertifiedRawCellListProducerCertificate :
    SU7CertifiedRawCellListProducerCertificate where
  certified_list_to_spectrum :=
    rawBranchingSpectrum_of_certifiedCells
  certified_list_to_local_filter :=
    localTensorFilter_of_certifiedCells
  checked_list_to_rule :=
    checkedLocalEnergyShellRule_of_certifiedCellList
  checked_list_to_physical_zero :=
    generatedPhysicalZeroBranchCell_of_certifiedCellList
  every_fiber_to_goldbach :=
    evenGoldbach_of_certifiedCellLists


end
end StandardModelConstraint
end SaturationMonoid
