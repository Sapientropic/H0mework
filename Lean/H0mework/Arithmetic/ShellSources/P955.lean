import H0mework.Arithmetic.ShellSources.P954

/-!
# Proposition 955: generated no-prime branch-cell lists

P954 accepts an arbitrary no-prime branch-cell list plus a finite
endpoint-energy shell checker.  This file builds the concrete source list from
the existing Boolean raw SU(7) generator without ever storing `Nat.Prime`.

The route is:

```text
Boolean multiplicative-atomic endpoint check
-> multiplicative atomicity
-> raw-code tensor irreducibility
-> SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n
```

The generated list is therefore a representation/tensor object.  Prime facts
remain projection theorems from P932/P930.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false
set_option linter.unusedVariables false

/-! ## Boolean atomicity generates raw-code tensor irreducibility -/

/-- Multiplicative atomicity of a raw code gives tensor irreducibility in the
raw-code tensor carrier. -/
theorem rawCodeTensorIrreducible_of_natMultiplicativelyAtomic
    {w : SU7WeightLattice}
    (h : NatMultiplicativelyAtomic w.code) :
    SU7TensorIrreducible rawCodeTensorCoding w := by
  constructor
  · exact h.1
  · intro u v htensor
    exact h.2 u.code v.code
      (by simpa [rawCodeTensorCoding] using htensor.symm)

/-- A successful Boolean multiplicative-atomicity check gives raw-code tensor
irreducibility, still without mentioning `Nat.Prime`. -/
theorem rawCodeTensorIrreducible_of_atomicCheck_eq_true
    {code : ℕ}
    (hcheck : natMultiplicativelyAtomicCheck code = true) :
    SU7TensorIrreducible rawCodeTensorCoding { code := code } :=
  rawCodeTensorIrreducible_of_natMultiplicativelyAtomic
    (natMultiplicativelyAtomic_of_check_eq_true hcheck)

/-! ## Lifting Boolean raw cells to no-prime branch cells -/

/-- Lift one Boolean-checked endpoint into a no-prime SU(7) branch atom. -/
def noPrimeBranchingAtomOfBooleanEndpoint
    (code : ℕ)
    (hcheck : natMultiplicativelyAtomicCheck code = true)
    (sector : ColorWeakHyperchargeSector) :
    SU7NoPrimeBranchingAtom rawCodeTensorCoding where
  weight := { code := code }
  tensor_irreducible :=
    rawCodeTensorIrreducible_of_atomicCheck_eq_true hcheck
  sector := sector

@[simp] theorem noPrimeBranchingAtomOfBooleanEndpoint_atomCode
    (code : ℕ)
    (hcheck : natMultiplicativelyAtomicCheck code = true)
    (sector : ColorWeakHyperchargeSector) :
    atomCode
        (noPrimeBranchingAtomOfBooleanEndpoint
          code hcheck sector).toSU7Atom =
      code := rfl

/-- Lift one Boolean-atomic raw branching cell into a no-prime branch-spectrum
cell over `rawCodeTensorCoding`. -/
def noPrimeBranchingCellOfBooleanAtomicRawCell
    {n : ℕ} (x : SU7BooleanAtomicRawBranchingCell n) :
    SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n where
  branch := x.cell.branch
  leftAtom :=
    noPrimeBranchingAtomOfBooleanEndpoint
      x.cell.leftWeightCode x.left_check
      (sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints x.cell.incidence).1)
  rightAtom :=
    noPrimeBranchingAtomOfBooleanEndpoint
      x.cell.rightWeightCode x.right_check
      (sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints x.cell.incidence).2)

@[simp] theorem noPrimeBranchingCellOfBooleanAtomicRawCell_leftCode
    {n : ℕ} (x : SU7BooleanAtomicRawBranchingCell n) :
    atomCode
        (noPrimeBranchingCellOfBooleanAtomicRawCell x).leftAtom.toSU7Atom =
      x.cell.leftWeightCode := rfl

@[simp] theorem noPrimeBranchingCellOfBooleanAtomicRawCell_rightCode
    {n : ℕ} (x : SU7BooleanAtomicRawBranchingCell n) :
    atomCode
        (noPrimeBranchingCellOfBooleanAtomicRawCell x).rightAtom.toSU7Atom =
      x.cell.rightWeightCode := rfl

/-- The no-prime lift preserves endpoint residual energy exactly. -/
theorem noPrimeBranchingCellOfBooleanAtomicRawCell_energy_eq
    {n : ℕ} (x : SU7BooleanAtomicRawBranchingCell n) :
    noPrimeBranchingEndpointResidualEnergy
        (noPrimeBranchingCellOfBooleanAtomicRawCell x) =
      rawAtomCodeBranchingDecompositionResidualEnergy x.cell := by
  rw [rawBranchingResidualEnergy_eq_codePair x.cell]
  rfl

/-! ## Generated no-prime branch-cell list -/

/-- Lift a Boolean-atomic raw cell list to no-prime branch-spectrum cells. -/
def noPrimeBranchingCellsOfBooleanAtomicRawCells
    {n : ℕ} (xs : List (SU7BooleanAtomicRawBranchingCell n)) :
    List (SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n) :=
  xs.map noPrimeBranchingCellOfBooleanAtomicRawCell

/-- The generated no-prime branch-cell list from the explicit Boolean raw
SU(7) generator. -/
def generatedNoPrimeBranchingCells (n bound : ℕ) :
    List (SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n) :=
  noPrimeBranchingCellsOfBooleanAtomicRawCells
    (booleanAtomicRawBranchingCandidateList n bound)

/-- Membership in the generated no-prime list comes from a generated
Boolean-atomic raw cell. -/
theorem exists_booleanAtomicRawCell_of_mem_generatedNoPrimeBranchingCells
    {n bound : ℕ}
    {B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n}
    (hmem : B ∈ generatedNoPrimeBranchingCells n bound) :
    ∃ x : SU7BooleanAtomicRawBranchingCell n,
      x ∈ booleanAtomicRawBranchingCandidateList n bound ∧
        noPrimeBranchingCellOfBooleanAtomicRawCell x = B := by
  unfold generatedNoPrimeBranchingCells
    noPrimeBranchingCellsOfBooleanAtomicRawCells at hmem
  exact List.mem_map.mp hmem

/-- Generated no-prime branch cells inherit the raw endpoint-code bound from
the explicit Boolean raw generator. -/
theorem generatedNoPrimeBranchingCellsWithinBound
    (n bound : ℕ) :
    NoPrimeBranchingCellsWithinBound bound
      (generatedNoPrimeBranchingCells n bound) := by
  intro B hmem
  rcases
      exists_booleanAtomicRawCell_of_mem_generatedNoPrimeBranchingCells
        hmem with
    ⟨x, hxmem, hxB⟩
  subst B
  constructor
  · change x.cell.leftWeightCode ∈ rawCodeBoundedList bound
    exact booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      hxmem
  · change x.cell.rightWeightCode ∈ rawCodeBoundedList bound
    exact booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      hxmem

/-- A generated raw energy-shell witness lifts to a generated no-prime
endpoint-energy witness. -/
theorem noPrimeEndpointEnergyShell_of_generatedRawEnergyShell
    {n bound k : ℕ}
    (h : GeneratedRawEnergyShellRealized n bound k) :
    ∃ B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n,
      B ∈ generatedNoPrimeBranchingCells n bound ∧
        noPrimeBranchingEndpointResidualEnergy B = k := by
  rcases h with ⟨x, hxmem, hxenergy⟩
  refine
    ⟨noPrimeBranchingCellOfBooleanAtomicRawCell x, ?_, ?_⟩
  · unfold generatedNoPrimeBranchingCells
      noPrimeBranchingCellsOfBooleanAtomicRawCells
    exact List.mem_map.mpr ⟨x, hxmem, rfl⟩
  · rw [noPrimeBranchingCellOfBooleanAtomicRawCell_energy_eq]
    exact hxenergy

/-- A generated raw energy-shell witness makes the no-prime has-energy
checker succeed on the generated no-prime list. -/
theorem generatedNoPrimeHasEndpointEnergy_of_generatedRawEnergyShell
    {n bound k : ℕ}
    (h : GeneratedRawEnergyShellRealized n bound k) :
    noPrimeBranchingCellHasEndpointEnergy
        (generatedNoPrimeBranchingCells n bound) k = true := by
  rcases noPrimeEndpointEnergyShell_of_generatedRawEnergyShell h with
    ⟨B, hBmem, hBenergy⟩
  unfold noPrimeBranchingCellHasEndpointEnergy
  apply List.any_eq_true.mpr
  exact ⟨B, hBmem, decide_eq_true_eq.mpr hBenergy⟩

/-! ## Generated checked no-prime rules -/

/-- A generated no-prime checked rule is built from the explicit generated
branch-cell list plus its Boolean endpoint-energy coverage check. -/
def generatedNoPrimeCheckedEnergyShellRuleOfCheck
    {n bound : ℕ}
    (hcheck :
      noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)) = true) :
    SU7NoPrimeBranchingCheckedEnergyShellRule rawCodeTensorCoding n where
  cells := generatedNoPrimeBranchingCells n bound
  rawCodeBound := bound
  cells_within_bound := generatedNoPrimeBranchingCellsWithinBound n bound
  coverage_check := hcheck

/-- A successful generated no-prime coverage check forbids unit permanent
holonomy in the filtered generated raw spectrum. -/
theorem generatedNoPrimeCoverageCheck_forbidsFilteredSpectrumUnitHolonomy
    {n bound : ℕ}
    (hcheck :
      noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)) = true) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n bound))) :=
  noPrimeCheckedEnergyShell_forbidsFilteredSpectrumUnitHolonomy
    (generatedNoPrimeCheckedEnergyShellRuleOfCheck hcheck)

/-! ## Certificate -/

/-- P955 certificate: the explicit Boolean raw generator lifts to a no-prime
SU(7) branch-cell list through raw-code tensor irreducibility, and a finite
coverage check on that list feeds P954. -/
structure SU7GeneratedNoPrimeBranchingListCertificate where
  atomic_to_tensor_irreducible :
    ∀ {w : SU7WeightLattice},
      NatMultiplicativelyAtomic w.code ->
        SU7TensorIrreducible rawCodeTensorCoding w
  boolean_cell_to_no_prime :
    ∀ {n : ℕ}, SU7BooleanAtomicRawBranchingCell n ->
      SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n
  generated_cells :
    ∀ n bound : ℕ,
      List (SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n)
  generated_within_bound :
    ∀ n bound : ℕ,
      NoPrimeBranchingCellsWithinBound bound
        (generatedNoPrimeBranchingCells n bound)
  raw_shell_to_no_prime_shell :
    ∀ {n bound k : ℕ},
      GeneratedRawEnergyShellRealized n bound k ->
        ∃ B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n,
          B ∈ generatedNoPrimeBranchingCells n bound ∧
            noPrimeBranchingEndpointResidualEnergy B = k
  coverage_check_to_filtered_no_holonomy :
    ∀ {n bound : ℕ},
      noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) = true ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound
            (noPrimeBranchingAllowedPredicate
              (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P955 generated no-prime branch-list certificate. -/
def su7GeneratedNoPrimeBranchingListCertificate :
    SU7GeneratedNoPrimeBranchingListCertificate where
  atomic_to_tensor_irreducible :=
    rawCodeTensorIrreducible_of_natMultiplicativelyAtomic
  boolean_cell_to_no_prime :=
    noPrimeBranchingCellOfBooleanAtomicRawCell
  generated_cells :=
    generatedNoPrimeBranchingCells
  generated_within_bound :=
    generatedNoPrimeBranchingCellsWithinBound
  raw_shell_to_no_prime_shell :=
    noPrimeEndpointEnergyShell_of_generatedRawEnergyShell
  coverage_check_to_filtered_no_holonomy :=
    generatedNoPrimeCoverageCheck_forbidsFilteredSpectrumUnitHolonomy


end
end StandardModelConstraint
end SaturationMonoid
