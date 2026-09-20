import H0mework.Arithmetic.ShellSources.P946

/-!
# Proposition 947: unit confinement reduces to raw code-pair descent

P946 left one substantive producer:

```text
the generated SU(7) spectrum forbids unit permanent holonomy.
```

This file lowers that statement to the raw endpoint-code level.  The remaining
law is not a stored zero cell and not a stored Goldbach pair:

```text
every nonzero bounded Boolean-atomic raw code-pair residual energy has a
bounded Boolean-atomic raw code-pair successor whose energy is lower by one.
```

The SU(7) branch/incidence coordinates are then only the canonical lift from
P929.  Thus the last confinement obligation is now a raw code-pair descent
law, not another spectrum-level receipt.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generated Boolean-cell unit descent -/

/-- Unit descent stated directly on the generated Boolean-atomic branch cells.

This predicate contains no zero cell.  It says that every generated cell with
nonzero raw residual has another generated cell whose residual energy is lower
by exactly one. -/
def GeneratedBooleanAtomicUnitSuccessorLaw
    (n bound : ℕ) : Prop :=
  ∀ x : SU7BooleanAtomicRawBranchingCell n,
    x ∈ booleanAtomicRawBranchingCandidateList n bound ->
      rawAtomCodeBranchingDecompositionResidual x.cell ≠ 0 ->
        ∃ y : SU7BooleanAtomicRawBranchingCell n,
          y ∈ booleanAtomicRawBranchingCandidateList n bound ∧
            rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 =
              rawAtomCodeBranchingDecompositionResidualEnergy x.cell

/-- Generated Boolean-cell descent is exactly enough to produce the spectrum
unit-successor law of P914 for the generated SU(7) spectrum. -/
theorem generatedSpectrumUnitSuccessorLaw_of_booleanAtomicUnitSuccessorLaw
    {n bound : ℕ}
    (H : GeneratedBooleanAtomicUnitSuccessorLaw n bound) :
    SU7RawBranchingSpectrumUnitSuccessorLaw
      (booleanGeneratedRawBranchingSpectrum n bound) := by
  intro c hmem hnonzero
  rcases exists_booleanAtomicCell_of_mem_booleanGeneratedSpectrum
      (n := n) (bound := bound) hmem with
    ⟨x, hxmem, hxcell⟩
  rcases H x hxmem (by simpa [hxcell] using hnonzero) with
    ⟨y, hymem, hyenergy⟩
  refine ⟨y.cell, booleanAtomicCell_mem_booleanGeneratedSpectrum hymem, ?_⟩
  simpa [hxcell] using hyenergy

/-- Generated Boolean-cell descent forbids unit permanent holonomy in the
generated SU(7) spectrum. -/
theorem forbidsUnitPermanentHolonomy_of_booleanAtomicUnitSuccessorLaw
    {n bound : ℕ}
    (H : GeneratedBooleanAtomicUnitSuccessorLaw n bound) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum n bound) :=
  (noRawUnitPermanentHolonomy_iff_unitSuccessorLaw
    (booleanGeneratedRawBranchingSpectrum n bound)).mpr
      (generatedSpectrumUnitSuccessorLaw_of_booleanAtomicUnitSuccessorLaw H)

/-! ## Raw code-pair unit descent -/

/-- Unit descent stated only on raw endpoint codes.

No `Nat.Prime`, no prime exponent, no zero cell, and no SU(7) branch-cell
normal form is stored here.  A nonzero absolute residual energy must have a
bounded Boolean-atomic successor with energy lower by exactly one. -/
def RawCodePairEnergyUnitSuccessorLaw
    (n bound : ℕ) : Prop :=
  ∀ left right : ℕ,
    left ∈ rawCodeBoundedList bound ->
      right ∈ rawCodeBoundedList bound ->
        natMultiplicativelyAtomicCheck left = true ->
          natMultiplicativelyAtomicCheck right = true ->
            rawCodePairResidualEnergy n left right ≠ 0 ->
              ∃ left' right' : ℕ,
                left' ∈ rawCodeBoundedList bound ∧
                  right' ∈ rawCodeBoundedList bound ∧
                    natMultiplicativelyAtomicCheck left' = true ∧
                      natMultiplicativelyAtomicCheck right' = true ∧
                        rawCodePairResidualEnergy n left' right' + 1 =
                          rawCodePairResidualEnergy n left right

/-- Raw code-pair unit descent lifts to generated Boolean-cell unit descent
through P929's canonical SU(7) branch/incidence lift. -/
theorem booleanAtomicUnitSuccessorLaw_of_rawCodePairEnergyUnitSuccessorLaw
    {n bound : ℕ}
    (H : RawCodePairEnergyUnitSuccessorLaw n bound) :
    GeneratedBooleanAtomicUnitSuccessorLaw n bound := by
  intro x hxmem hnonzero
  have hshell :
      RawCodePairEnergyShellRealized n bound
        (rawAtomCodeBranchingDecompositionResidualEnergy x.cell) :=
    rawCodePairShell_of_generatedRawEnergyShell
      ⟨x, hxmem, rfl⟩
  rcases hshell with
    ⟨left, right, hleft_mem, hright_mem,
      hleft_check, hright_check, henergy⟩
  have hpair_nonzero :
      rawCodePairResidualEnergy n left right ≠ 0 := by
    intro hzero
    have hxenergy_zero :
        rawAtomCodeBranchingDecompositionResidualEnergy x.cell = 0 := by
      simpa [hzero] using henergy.symm
    exact hnonzero
      ((rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff x.cell).mp
        hxenergy_zero)
  rcases
      H left right hleft_mem hright_mem hleft_check hright_check
        hpair_nonzero with
    ⟨left', right', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, hsucc⟩
  have hnext_shell :
      RawCodePairEnergyShellRealized n bound
        (rawCodePairResidualEnergy n left' right') :=
    ⟨left', right', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, rfl⟩
  rcases generatedRawEnergyShell_of_rawCodePairShell hnext_shell with
    ⟨y, hymem, hyenergy⟩
  refine ⟨y, hymem, ?_⟩
  calc
    rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 =
        rawCodePairResidualEnergy n left' right' + 1 := by
          rw [hyenergy]
    _ = rawCodePairResidualEnergy n left right := hsucc
    _ = rawAtomCodeBranchingDecompositionResidualEnergy x.cell := henergy

/-- Raw code-pair unit descent forbids generated unit permanent holonomy. -/
theorem forbidsUnitPermanentHolonomy_of_rawCodePairEnergyUnitSuccessorLaw
    {n bound : ℕ}
    (H : RawCodePairEnergyUnitSuccessorLaw n bound) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum n bound) :=
  forbidsUnitPermanentHolonomy_of_booleanAtomicUnitSuccessorLaw
    (booleanAtomicUnitSuccessorLaw_of_rawCodePairEnergyUnitSuccessorLaw H)

/-! ## Code-pair unit-confinement certificates -/

/-- A generated confinement certificate whose only substantive producer field
is the raw code-pair unit descent law.  Spectrum nonemptiness is still produced
by P946 from the `(2, 2)` generated endpoint witness. -/
structure SU7GeneratedRawCodePairUnitConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  codeBound_ge_two : 2 ≤ codeBound
  raw_code_pair_unit_successor :
    RawCodePairEnergyUnitSuccessorLaw n codeBound

/-- Raw code-pair unit confinement produces the P946 generated unit-
confinement-only certificate. -/
def unitConfinementCertificate_of_rawCodePairUnitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedRawCodePairUnitConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n where
  codeBound := G.codeBound
  codeBound_ge_two := G.codeBound_ge_two
  forbids_unit_permanent_holonomy :=
    forbidsUnitPermanentHolonomy_of_rawCodePairEnergyUnitSuccessorLaw
      G.raw_code_pair_unit_successor

/-- Raw code-pair unit confinement produces the generated no-gap certificate.
-/
def noGapCertificate_of_rawCodePairUnitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedRawCodePairUnitConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingNoGapCertificate n :=
  noGapCertificate_of_unitConfinementCertificate
    (unitConfinementCertificate_of_rawCodePairUnitConfinementCertificate G)

/-- Raw code-pair unit confinement computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_rawCodePairUnitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedRawCodePairUnitConfinementCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_unitConfinementCertificate
    (unitConfinementCertificate_of_rawCodePairUnitConfinementCertificate G)

/-- Every even fiber carries a raw code-pair unit-confinement certificate. -/
def SU7GeneratedRawCodePairUnitConfinementEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty
      (SU7GeneratedRawCodePairUnitConfinementCertificate n)

/-- Fiberwise raw code-pair unit confinement gives ordinary even Goldbach via
the P947 -> P946 -> P945 -> P944 -> P943 -> P940/P939 chain. -/
theorem evenGoldbach_of_generatedRawCodePairUnitConfinement
    (H : SU7GeneratedRawCodePairUnitConfinementEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_generatedUnitConfinement
    (by
      intro n hn
      exact
        ⟨unitConfinementCertificate_of_rawCodePairUnitConfinementCertificate
          (Classical.choice (H n hn))⟩)

/-! ## Certificate -/

/-- P947 certificate: generated unit confinement is reduced to raw code-pair
unit descent.  This is the present hard producer interface for the color-loop
route: prove the raw endpoint-code descent law from SU(7) confinement, and the
rest of the Goldbach readout is already machine-checked. -/
structure SU7GeneratedRawCodePairUnitConfinementProducerCertificate where
  boolean_descent_to_spectrum_successor :
    ∀ {n bound : ℕ},
      GeneratedBooleanAtomicUnitSuccessorLaw n bound ->
        SU7RawBranchingSpectrumUnitSuccessorLaw
          (booleanGeneratedRawBranchingSpectrum n bound)
  boolean_descent_to_no_unit_holonomy :
    ∀ {n bound : ℕ},
      GeneratedBooleanAtomicUnitSuccessorLaw n bound ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (booleanGeneratedRawBranchingSpectrum n bound)
  raw_code_pair_descent_to_boolean_descent :
    ∀ {n bound : ℕ},
      RawCodePairEnergyUnitSuccessorLaw n bound ->
        GeneratedBooleanAtomicUnitSuccessorLaw n bound
  raw_code_pair_descent_to_no_unit_holonomy :
    ∀ {n bound : ℕ},
      RawCodePairEnergyUnitSuccessorLaw n bound ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (booleanGeneratedRawBranchingSpectrum n bound)
  raw_code_pair_certificate_to_no_gap :
    ∀ {n : ℕ},
      SU7GeneratedRawCodePairUnitConfinementCertificate n ->
        SU7GeneratedBooleanRawBranchingNoGapCertificate n
  raw_code_pair_certificate_to_trace_zero :
    ∀ {n : ℕ},
      SU7GeneratedRawCodePairUnitConfinementCertificate n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    SU7GeneratedRawCodePairUnitConfinementEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P947 raw code-pair unit-confinement producer certificate. -/
def su7GeneratedRawCodePairUnitConfinementProducerCertificate :
    SU7GeneratedRawCodePairUnitConfinementProducerCertificate where
  boolean_descent_to_spectrum_successor :=
    generatedSpectrumUnitSuccessorLaw_of_booleanAtomicUnitSuccessorLaw
  boolean_descent_to_no_unit_holonomy :=
    forbidsUnitPermanentHolonomy_of_booleanAtomicUnitSuccessorLaw
  raw_code_pair_descent_to_boolean_descent :=
    booleanAtomicUnitSuccessorLaw_of_rawCodePairEnergyUnitSuccessorLaw
  raw_code_pair_descent_to_no_unit_holonomy :=
    forbidsUnitPermanentHolonomy_of_rawCodePairEnergyUnitSuccessorLaw
  raw_code_pair_certificate_to_no_gap :=
    noGapCertificate_of_rawCodePairUnitConfinementCertificate
  raw_code_pair_certificate_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawCodePairUnitConfinementCertificate
  every_fiber_to_goldbach :=
    evenGoldbach_of_generatedRawCodePairUnitConfinement


end
end StandardModelConstraint
end SaturationMonoid
