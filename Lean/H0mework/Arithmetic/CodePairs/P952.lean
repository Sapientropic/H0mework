import H0mework.Arithmetic.ShellSources.P951

/-!
# Proposition 952: branch-cell unit descent forbids filtered holonomy

P951 made the Boolean allowed-sector predicate executable from a list of
no-prime SU(7) branch cells.  P952 pushes the P950 no-holonomy obligation back
onto that same list:

```text
every nonzero no-prime branch cell has an in-list successor one energy unit
lower
  -> no filtered raw code-pair permanent holonomy.
```

The source list still stores no `Nat.Prime`, no zero cell, and no Goldbach
pair.  Primality is used only to prove that generated endpoint codes pass the
Boolean atomicity check.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## No-prime list residual energy and boundedness -/

/-- Endpoint-code residual energy of a no-prime branch cell. -/
def noPrimeBranchingEndpointResidualEnergy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) : ℕ :=
  rawCodePairResidualEnergy n
    (atomCode B.leftAtom.toSU7Atom)
    (atomCode B.rightAtom.toSU7Atom)

/-- A no-prime branch-cell list is bounded when every generated endpoint code
lies in the same raw code bound. -/
def NoPrimeBranchingCellsWithinBound
    {C : SU7WeightTensorCoding} {n : ℕ}
    (bound : ℕ)
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) : Prop :=
  ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
    B ∈ xs ->
      atomCode B.leftAtom.toSU7Atom ∈ rawCodeBoundedList bound ∧
        atomCode B.rightAtom.toSU7Atom ∈ rawCodeBoundedList bound

/-- No-prime branch-cell unit descent, stated on the source list itself. -/
def NoPrimeBranchingCellUnitSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) : Prop :=
  ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
    B ∈ xs ->
      noPrimeBranchingEndpointResidualEnergy B ≠ 0 ->
        ∃ B' : SU7NoPrimeBranchingSpectrumCell C n,
          B' ∈ xs ∧
            noPrimeBranchingEndpointResidualEnergy B' + 1 =
              noPrimeBranchingEndpointResidualEnergy B

/-! ## Projection helpers -/

/-- Source no-prime cells pass the Boolean atomicity checker on the left
endpoint. -/
theorem noPrimeBranchingCell_left_atomicCheck
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    natMultiplicativelyAtomicCheck
        (atomCode B.leftAtom.toSU7Atom) = true :=
  (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mpr
    (noPrimeBranchingAtom_atomCode_prime B.leftAtom)

/-- Source no-prime cells pass the Boolean atomicity checker on the right
endpoint. -/
theorem noPrimeBranchingCell_right_atomicCheck
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    natMultiplicativelyAtomicCheck
        (atomCode B.rightAtom.toSU7Atom) = true :=
  (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mpr
    (noPrimeBranchingAtom_atomCode_prime B.rightAtom)

/-! ## Cell-level unit descent feeds P950 -/

/-- Branch-cell unit descent on a bounded no-prime list implies the P950
filtered raw code-pair no-permanent-holonomy predicate. -/
theorem noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_cellUnitSuccessorLaw
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (hbounded : NoPrimeBranchingCellsWithinBound bound xs)
    (Hsucc : NoPrimeBranchingCellUnitSuccessorLaw xs) :
    NoPrimeAllowedSectorForbidsUnitPermanentHolonomy bound xs := by
  unfold NoPrimeAllowedSectorForbidsUnitPermanentHolonomy
  exact
    (noFilteredRawCodePairPermanentHolonomy_iff_unitSuccessorLaw
      n bound (noPrimeBranchingAllowedPredicate xs)).mpr
      (by
        intro left right hallowed _hleft_bound _hright_bound
          _hleft_check _hright_check hnonzero
        rcases exists_noPrimeBranchingCell_of_allowedPredicate
            (C := C) (n := n) (xs := xs) hallowed with
          ⟨B, hBmem, hleft, hright⟩
        have hBnonzero :
            noPrimeBranchingEndpointResidualEnergy B ≠ 0 := by
          unfold noPrimeBranchingEndpointResidualEnergy
          simpa [hleft, hright] using hnonzero
        rcases Hsucc B hBmem hBnonzero with ⟨B', hB'mem, hsucc⟩
        refine
          ⟨atomCode B'.leftAtom.toSU7Atom,
            atomCode B'.rightAtom.toSU7Atom,
            noPrimeBranchingAllowedPredicate_of_mem hB'mem,
            (hbounded B' hB'mem).1,
            (hbounded B' hB'mem).2,
            noPrimeBranchingCell_left_atomicCheck B',
            noPrimeBranchingCell_right_atomicCheck B',
            ?_⟩
        unfold noPrimeBranchingEndpointResidualEnergy at hsucc
        simpa [hleft, hright] using hsucc)

/-- The same branch-cell unit descent immediately forbids unit permanent
holonomy in the filtered generated SU(7) spectrum. -/
theorem gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeCellUnitSuccessorLaw
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (hbounded : NoPrimeBranchingCellsWithinBound bound xs)
    (Hsucc : NoPrimeBranchingCellUnitSuccessorLaw xs) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate xs)) :=
  gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeAllowedSector
    (noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_cellUnitSuccessorLaw
      hbounded Hsucc)

/-! ## Certificate -/

/-- P952 certificate: bounded no-prime branch-cell unit descent is sufficient
to eliminate P950 filtered permanent holonomy. -/
structure SU7NoPrimeBranchCellUnitDescentCertificate where
  left_atomic_check :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      natMultiplicativelyAtomicCheck
          (atomCode B.leftAtom.toSU7Atom) = true
  right_atomic_check :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      natMultiplicativelyAtomicCheck
          (atomCode B.rightAtom.toSU7Atom) = true
  cell_descent_to_no_filtered_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellsWithinBound bound xs ->
        NoPrimeBranchingCellUnitSuccessorLaw xs ->
          NoPrimeAllowedSectorForbidsUnitPermanentHolonomy bound xs
  cell_descent_to_filtered_spectrum_no_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellsWithinBound bound xs ->
        NoPrimeBranchingCellUnitSuccessorLaw xs ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate xs))

/-- Canonical P952 no-prime branch-cell unit-descent certificate. -/
def su7NoPrimeBranchCellUnitDescentCertificate :
    SU7NoPrimeBranchCellUnitDescentCertificate where
  left_atomic_check := noPrimeBranchingCell_left_atomicCheck
  right_atomic_check := noPrimeBranchingCell_right_atomicCheck
  cell_descent_to_no_filtered_holonomy :=
    noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_cellUnitSuccessorLaw
  cell_descent_to_filtered_spectrum_no_holonomy :=
    gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeCellUnitSuccessorLaw


end
end StandardModelConstraint
end SaturationMonoid
