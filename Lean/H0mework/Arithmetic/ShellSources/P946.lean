import H0mework.Arithmetic.CodePairs.P945

/-!
# Proposition 946: generated SU(7) spectra are nonempty above code 2

P945 reduced the generated color-loop producer to:

```text
generated spectrum nonempty
+ generated spectrum forbids unit permanent holonomy
```

This file discharges the nonemptiness side directly from the explicit finite
SU(7) generator.  For any code bound at least `2`, the canonical raw code pair
`(2, 2)` passes the Boolean multiplicative-atomicity check and therefore
appears in the generated spectrum.

The remaining producer datum is now only the confinement side:

```text
for some bound >= 2, the generated spectrum forbids unit permanent holonomy
```
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## The canonical `(2, 2)` branch witness -/

/-- The endpoint code `2` passes the finite multiplicative-atomicity checker.
-/
theorem natMultiplicativelyAtomicCheck_two :
    natMultiplicativelyAtomicCheck 2 = true := by
  norm_num [natMultiplicativelyAtomicCheck, natHasNontrivialDivisorCheck]
  intro x _hx h2 hle _hdiv
  omega

/-- The endpoint code `2` is present in every bounded raw-code list whose
bound is at least `2`. -/
theorem two_mem_rawCodeBoundedList
    {bound : ℕ} (hbound : 2 ≤ bound) :
    2 ∈ rawCodeBoundedList bound := by
  simp [rawCodeBoundedList]
  omega

/-- The canonical `(2, 2)` code pair realizes one raw code-pair shell for any
fiber and any code bound at least `2`. -/
theorem rawCodePairShell_two_two
    (n bound : ℕ) (hbound : 2 ≤ bound) :
    RawCodePairEnergyShellRealized
      n bound (rawCodePairResidualEnergy n 2 2) := by
  refine ⟨2, 2, ?_, ?_, ?_, ?_, rfl⟩
  · exact two_mem_rawCodeBoundedList hbound
  · exact two_mem_rawCodeBoundedList hbound
  · exact natMultiplicativelyAtomicCheck_two
  · exact natMultiplicativelyAtomicCheck_two

/-- The canonical `(2, 2)` pair appears as a generated Boolean-atomic raw
energy-shell witness. -/
theorem generatedRawEnergyShell_two_two
    (n bound : ℕ) (hbound : 2 ≤ bound) :
    GeneratedRawEnergyShellRealized
      n bound (rawCodePairResidualEnergy n 2 2) :=
  generatedRawEnergyShell_of_rawCodePairShell
    (rawCodePairShell_two_two n bound hbound)

/-! ## Generated spectrum nonemptiness -/

/-- Every generated SU(7) raw branching spectrum with bound at least `2` is
nonempty. -/
theorem booleanGeneratedRawBranchingSpectrum_nonempty_of_bound_ge_two
    (n bound : ℕ) (hbound : 2 ≤ bound) :
    (booleanGeneratedRawBranchingSpectrum n bound).cells ≠ [] := by
  rcases generatedRawEnergyShell_two_two n bound hbound with
    ⟨x, hxmem, _hxenergy⟩
  have hcell :
      x.cell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells :=
    booleanAtomicCell_mem_booleanGeneratedSpectrum hxmem
  intro hnil
  rw [hnil] at hcell
  simp at hcell

/-! ## Unit-confinement-only generated certificates -/

/-- A generated confinement certificate whose only substantive physical field
is unit permanent-holonomy exclusion.  Nonemptiness is produced automatically
from `codeBound_ge_two`. -/
structure SU7GeneratedBooleanRawBranchingUnitConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  codeBound_ge_two : 2 ≤ codeBound
  forbids_unit_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum n codeBound)

/-- A unit-confinement-only certificate produces the P945 nonempty-confinement
certificate. -/
def nonemptyConfinementCertificate_of_unitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n where
  codeBound := G.codeBound
  spectrum_nonempty :=
    booleanGeneratedRawBranchingSpectrum_nonempty_of_bound_ge_two
      n G.codeBound G.codeBound_ge_two
  forbids_unit_permanent_holonomy :=
    G.forbids_unit_permanent_holonomy

/-- A unit-confinement-only certificate produces a no-gap certificate. -/
def noGapCertificate_of_unitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingNoGapCertificate n :=
  noGapCertificate_of_nonemptyConfinementCertificate
    (nonemptyConfinementCertificate_of_unitConfinementCertificate G)

/-- A unit-confinement-only certificate computes a trace-zero prime-edge loop.
-/
def traceZeroPrimeEdgeLoop_of_unitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_nonemptyConfinementCertificate
    (nonemptyConfinementCertificate_of_unitConfinementCertificate G)

/-- Every even fiber carries a generated unit-confinement certificate. -/
def SU7GeneratedUnitConfinementEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty
      (SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n)

/-- Fiberwise generated unit confinement gives ordinary even Goldbach. -/
theorem evenGoldbach_of_generatedUnitConfinement
    (H : SU7GeneratedUnitConfinementEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_generatedNonemptyConfinement
    (by
      intro n hn
      exact
        ⟨nonemptyConfinementCertificate_of_unitConfinementCertificate
          (Classical.choice (H n hn))⟩)

/-! ## Certificate -/

/-- P946 certificate: explicit finite generation supplies nonemptiness; only
unit permanent-holonomy exclusion remains as the physical producer. -/
structure SU7GeneratedUnitConfinementOnlyProducerCertificate where
  two_atomic_check :
    natMultiplicativelyAtomicCheck 2 = true
  two_mem_bound :
    ∀ {bound : ℕ}, 2 ≤ bound -> 2 ∈ rawCodeBoundedList bound
  two_two_shell :
    ∀ n bound : ℕ, 2 ≤ bound ->
      RawCodePairEnergyShellRealized
        n bound (rawCodePairResidualEnergy n 2 2)
  generated_spectrum_nonempty :
    ∀ n bound : ℕ, 2 ≤ bound ->
      (booleanGeneratedRawBranchingSpectrum n bound).cells ≠ []
  unit_confinement_to_no_gap :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n ->
        SU7GeneratedBooleanRawBranchingNoGapCertificate n
  unit_confinement_to_trace_zero :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    SU7GeneratedUnitConfinementEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P946 generated unit-confinement-only producer certificate. -/
def su7GeneratedUnitConfinementOnlyProducerCertificate :
    SU7GeneratedUnitConfinementOnlyProducerCertificate where
  two_atomic_check :=
    natMultiplicativelyAtomicCheck_two
  two_mem_bound :=
    two_mem_rawCodeBoundedList
  two_two_shell :=
    rawCodePairShell_two_two
  generated_spectrum_nonempty :=
    booleanGeneratedRawBranchingSpectrum_nonempty_of_bound_ge_two
  unit_confinement_to_no_gap :=
    noGapCertificate_of_unitConfinementCertificate
  unit_confinement_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_unitConfinementCertificate
  every_fiber_to_goldbach :=
    evenGoldbach_of_generatedUnitConfinement


end
end StandardModelConstraint
end SaturationMonoid
