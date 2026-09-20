import H0mework.Arithmetic.ShellSources.P928
import H0mework.Arithmetic.CodePairs.Residual

/-!
# Proposition 929: generated shell coverage reduces to raw code-pair coverage

P928 made the generated coverage checker transparent as energy-shell
realization over generated Boolean-atomic branch cells.  This file removes the
remaining finite SU(7) list noise: the branch and incidence coordinates are a
nonempty lift.  The residual energy itself only sees the two raw endpoint
codes and the even fiber.

The remaining no-gap producer can now be stated as pure code-pair shell
coverage:

```text
for every k below the generated bound, there are two bounded endpoint codes
whose Boolean multiplicative-atomicity checks pass and whose absolute
raw-code residual is k.
```

No `Nat.Prime`, no prime exponent, and no Goldbach pair is stored in this
interface.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Code-pair residual shells -/

/-- A raw code-pair energy shell is realized when two bounded endpoint codes
pass the Boolean multiplicative-atomicity checker and have residual energy
`k`. -/
def RawCodePairEnergyShellRealized
    (n bound k : ℕ) : Prop :=
  ∃ left right : ℕ,
    left ∈ rawCodeBoundedList bound ∧
      right ∈ rawCodeBoundedList bound ∧
        natMultiplicativelyAtomicCheck left = true ∧
          natMultiplicativelyAtomicCheck right = true ∧
            rawCodePairResidualEnergy n left right = k

/-- Code-pair coverage is shell-by-shell realization by raw endpoint codes. -/
def RawCodePairEnergyCoverage (n bound : ℕ) : Prop :=
  ∀ k : ℕ, k < generatedRawBranchingMaxEnergy n bound ->
    RawCodePairEnergyShellRealized n bound k

/-! ## Canonical lift from a code pair to the SU(7) branch enumerator -/

/-- A fixed branch/incidence lift of two raw endpoint codes.  The branch and
incidence coordinates are deliberately canonical here; the energy readout only
depends on `left` and `right`. -/
def canonicalRawCodePairBranchingCell
    (n left right : ℕ) : SU7BranchingDecompositionCell n where
  branch := SU3FlagSchubertCell.e
  incidence := SU7BlockIncidence.colorWeak
  leftWeightCode := left
  rightWeightCode := right

@[simp] theorem canonicalRawCodePairBranchingCell_left
    (n left right : ℕ) :
    (canonicalRawCodePairBranchingCell n left right).leftWeightCode =
      left := rfl

@[simp] theorem canonicalRawCodePairBranchingCell_right
    (n left right : ℕ) :
    (canonicalRawCodePairBranchingCell n left right).rightWeightCode =
      right := rfl

/-- Raw branch-cell residual energy is exactly the raw code-pair residual
energy of its endpoint codes. -/
theorem rawBranchingResidualEnergy_eq_codePair
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    rawAtomCodeBranchingDecompositionResidualEnergy c =
      rawCodePairResidualEnergy n c.leftWeightCode c.rightWeightCode := by
  unfold rawAtomCodeBranchingDecompositionResidualEnergy
    rawAtomCodeBranchingDecompositionResidual
    rawAtomCodePhysicalBranchingSpectrumResidual
    physicalBranchingSpectrumCell_of_branchingDecompositionCell
    representationSupportSlot_of_branchingDecompositionCell
    leftAtomOfBranchingDecompositionCell
    rightAtomOfBranchingDecompositionCell
    su7AtomOfBranchingEndpoint
    atomCode
    rawCodePairResidualEnergy
    rawCodePairResidual
  rfl

/-- The canonical branch lift preserves raw code-pair residual energy. -/
theorem canonicalRawCodePairBranchingCell_energy_eq
    (n left right : ℕ) :
    rawAtomCodeBranchingDecompositionResidualEnergy
        (canonicalRawCodePairBranchingCell n left right) =
      rawCodePairResidualEnergy n left right := by
  simpa using
    rawBranchingResidualEnergy_eq_codePair
      (canonicalRawCodePairBranchingCell n left right)

/-- The raw residual-energy readout is blind to the Schubert branch and SU(7)
incidence coordinates once the two endpoint codes are fixed.

This is a diagnostic guardrail for the generated-shell route: the six SU(7)
incidence slots are real representation/source coordinates, but the current
P950 scalar energy shell does not distinguish them.  Any filtered normal-form
reachability theorem must add a sector-dependent filter/readout or prove a
faithful preservation law before using the six sectors as more than duplicate
copies of the same endpoint-code energy shell. -/
theorem rawBranchingResidualEnergy_eq_of_same_endpoint_codes
    {n : ℕ}
    (branch₁ branch₂ : SU3FlagSchubertCell)
    (incidence₁ incidence₂ : SU7BlockIncidence)
    (left right : ℕ) :
    rawAtomCodeBranchingDecompositionResidualEnergy
        ({ branch := branch₁
           incidence := incidence₁
           leftWeightCode := left
           rightWeightCode := right } :
          SU7BranchingDecompositionCell n) =
      rawAtomCodeBranchingDecompositionResidualEnergy
        ({ branch := branch₂
           incidence := incidence₂
           leftWeightCode := left
           rightWeightCode := right } :
          SU7BranchingDecompositionCell n) := by
  rw [rawBranchingResidualEnergy_eq_codePair,
    rawBranchingResidualEnergy_eq_codePair]

/-! ## Generated-cell realization is exactly code-pair realization -/

/-- A generated branch-shell witness forgets to a raw code-pair witness. -/
theorem rawCodePairShell_of_generatedRawEnergyShell
    {n bound k : ℕ}
    (h : GeneratedRawEnergyShellRealized n bound k) :
    RawCodePairEnergyShellRealized n bound k := by
  rcases h with ⟨x, hxmem, hxenergy⟩
  refine ⟨x.cell.leftWeightCode, x.cell.rightWeightCode, ?_, ?_,
    x.left_check, x.right_check, ?_⟩
  ·
    unfold booleanAtomicRawBranchingCandidateList at hxmem
    unfold booleanAtomicCellOfCandidate? at hxmem
    unfold rawBranchingCandidateCells at hxmem
    simp only [List.mem_filterMap] at hxmem
    rcases hxmem with ⟨c, hc_mem, hc_some⟩
    simp [rawCodeBoundedList] at hc_mem
    rcases hc_mem with
      ⟨branch, _hbranch, incidence, _hincidence,
        left, hleft_bound, right, _hright_bound, hc_eq⟩
    split at hc_some
    · split at hc_some
      · cases hc_some
        have hleft_eq : c.leftWeightCode = left := by
          exact
            (congrArg SU7BranchingDecompositionCell.leftWeightCode
              hc_eq).symm
        change c.leftWeightCode ∈ rawCodeBoundedList bound
        simpa [rawCodeBoundedList, hleft_eq] using hleft_bound
      · contradiction
    · contradiction
  ·
    unfold booleanAtomicRawBranchingCandidateList at hxmem
    unfold booleanAtomicCellOfCandidate? at hxmem
    unfold rawBranchingCandidateCells at hxmem
    simp only [List.mem_filterMap] at hxmem
    rcases hxmem with ⟨c, hc_mem, hc_some⟩
    simp [rawCodeBoundedList] at hc_mem
    rcases hc_mem with
      ⟨branch, _hbranch, incidence, _hincidence,
        left, _hleft_bound, right, hright_bound, hc_eq⟩
    split at hc_some
    · split at hc_some
      · cases hc_some
        have hright_eq : c.rightWeightCode = right := by
          exact
            (congrArg SU7BranchingDecompositionCell.rightWeightCode
              hc_eq).symm
        change c.rightWeightCode ∈ rawCodeBoundedList bound
        simpa [rawCodeBoundedList, hright_eq] using hright_bound
      · contradiction
    · contradiction
  ·
    simpa [rawBranchingResidualEnergy_eq_codePair x.cell]
      using hxenergy

/-- A raw code-pair witness lifts back to a generated Boolean-atomic branch
cell by using the canonical SU(7) branch/incidence coordinates. -/
theorem generatedRawEnergyShell_of_rawCodePairShell
    {n bound k : ℕ}
    (h : RawCodePairEnergyShellRealized n bound k) :
    GeneratedRawEnergyShellRealized n bound k := by
  rcases h with
    ⟨left, right, hleft_mem, hright_mem,
      hleft_check, hright_check, henergy⟩
  let c := canonicalRawCodePairBranchingCell n left right
  let x : SU7BooleanAtomicRawBranchingCell n :=
    { cell := c
      left_check := by
        simpa [c, canonicalRawCodePairBranchingCell]
          using hleft_check
      right_check := by
        simpa [c, canonicalRawCodePairBranchingCell]
          using hright_check }
  refine ⟨x, ?_, ?_⟩
  ·
    unfold booleanAtomicRawBranchingCandidateList
    simp only [List.mem_filterMap]
    refine ⟨c, ?_, ?_⟩
    ·
      have hleft_le : left ≤ bound := by
        simpa [rawCodeBoundedList] using hleft_mem
      have hright_le : right ≤ bound := by
        simpa [rawCodeBoundedList] using hright_mem
      simp [rawBranchingCandidateCells, rawCodeBoundedList,
        SU3FlagSchubertCell.all, SU7BlockIncidence.all,
        c, canonicalRawCodePairBranchingCell]
      exact ⟨hleft_le, hright_le⟩
    ·
      unfold booleanAtomicCellOfCandidate?
      simp [x, c, canonicalRawCodePairBranchingCell,
        hleft_check, hright_check]
  ·
    simpa [x, c, canonicalRawCodePairBranchingCell_energy_eq]
      using henergy

/-- Generated branch-shell realization is exactly raw code-pair shell
realization. -/
theorem generatedRawEnergyShell_iff_codePairShell
    (n bound k : ℕ) :
    GeneratedRawEnergyShellRealized n bound k ↔
      RawCodePairEnergyShellRealized n bound k := by
  constructor
  · exact rawCodePairShell_of_generatedRawEnergyShell
  · exact generatedRawEnergyShell_of_rawCodePairShell

/-- Generated branch coverage is exactly raw code-pair coverage. -/
theorem generatedRawEnergyCoverage_iff_codePairCoverage
    (n bound : ℕ) :
    GeneratedRawEnergyCoverage n bound ↔
      RawCodePairEnergyCoverage n bound := by
  constructor
  · intro hcoverage k hk
    exact
      (generatedRawEnergyShell_iff_codePairShell n bound k).mp
        (hcoverage k hk)
  · intro hcoverage k hk
    exact
      (generatedRawEnergyShell_iff_codePairShell n bound k).mpr
        (hcoverage k hk)

/-- Code-pair coverage feeds P928's transparent generated shell theorem. -/
def generatedCoverageCertificate_of_codePairCoverage
    {n bound : ℕ}
    (startCell : SU7BranchingDecompositionCell n)
    (hstart :
      startCell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells)
    (hcoverage : RawCodePairEnergyCoverage n bound) :
    SU7GeneratedBooleanRawBranchingCoverageCertificate n :=
  generatedCoverageCertificate_of_energyCoverage
    startCell hstart
    ((generatedRawEnergyCoverage_iff_codePairCoverage n bound).mpr
      hcoverage)

/-- Code-pair coverage gives the unit-bracket law through the generated SU(7)
branch lift. -/
theorem unitSuccessorLaw_of_codePairCoverage
    {n bound : ℕ}
    (startCell : SU7BranchingDecompositionCell n)
    (hstart :
      startCell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells)
    (hcoverage : RawCodePairEnergyCoverage n bound) :
    SU7RawBranchingSpectrumUnitSuccessorLaw
      (booleanGeneratedRawBranchingSpectrum n bound) :=
  unitSuccessorLaw_of_generatedEnergyCoverage
    startCell hstart
    ((generatedRawEnergyCoverage_iff_codePairCoverage n bound).mpr
      hcoverage)

/-! ## Certificate -/

/-- P929 certificate: explicit generated branch-shell coverage has exactly the
same content as bounded raw code-pair shell coverage. -/
structure SU7GeneratedCoverageCodePairReductionCertificate where
  shell_realized_iff_code_pair :
    ∀ n bound k : ℕ,
      GeneratedRawEnergyShellRealized n bound k ↔
        RawCodePairEnergyShellRealized n bound k
  coverage_iff_code_pair :
    ∀ n bound : ℕ,
      GeneratedRawEnergyCoverage n bound ↔
        RawCodePairEnergyCoverage n bound
  code_pair_coverage_to_certificate :
    ∀ {n bound : ℕ}
      (startCell : SU7BranchingDecompositionCell n),
      startCell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells ->
        RawCodePairEnergyCoverage n bound ->
          SU7GeneratedBooleanRawBranchingCoverageCertificate n
  code_pair_coverage_to_unit_bracket :
    ∀ {n bound : ℕ}
      (startCell : SU7BranchingDecompositionCell n),
      startCell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells ->
        RawCodePairEnergyCoverage n bound ->
          SU7RawBranchingSpectrumUnitSuccessorLaw
            (booleanGeneratedRawBranchingSpectrum n bound)

/-- Canonical P929 code-pair reduction certificate. -/
def su7GeneratedCoverageCodePairReductionCertificate :
    SU7GeneratedCoverageCodePairReductionCertificate where
  shell_realized_iff_code_pair :=
    generatedRawEnergyShell_iff_codePairShell
  coverage_iff_code_pair :=
    generatedRawEnergyCoverage_iff_codePairCoverage
  code_pair_coverage_to_certificate :=
    generatedCoverageCertificate_of_codePairCoverage
  code_pair_coverage_to_unit_bracket :=
    unitSuccessorLaw_of_codePairCoverage


end
end StandardModelConstraint
end SaturationMonoid
