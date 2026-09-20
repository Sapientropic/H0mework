import H0mework.Arithmetic.ShellSources.P964

/-!
# Proposition 965: gauge-filtered shell coverage is the no-gap producer

P948 showed that full raw-pair unit descent is false.  P964 lowered the
generated flow/quantization throat to transparent raw shell coverage.

This file states the next hard object in the right place: a Boolean SU(7)
allowed-sector shell coverage theorem.  It proves that such coverage:

* gives filtered raw code-pair unit descent, hence forbids permanent holonomy
  in the filtered generated spectrum;
* forgets to the unfiltered generated shell coverage needed by P964, hence
  produces the no-prime residual-flow / quantized-bridge throat.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Gauge-filtered shell coverage -/

/-- An allowed raw code-pair energy shell is realized when two bounded endpoint
codes pass the Boolean multiplicative-atomicity checks, are selected by the
SU(7) allowed-sector predicate, and have residual energy `k`. -/
def BoolGaugeFilteredRawCodePairEnergyShellRealized
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) (k : ℕ) : Prop :=
  ∃ left right : ℕ,
    allowed left right = true ∧
      left ∈ rawCodeBoundedList bound ∧
        right ∈ rawCodeBoundedList bound ∧
          natMultiplicativelyAtomicCheck left = true ∧
            natMultiplicativelyAtomicCheck right = true ∧
              rawCodePairResidualEnergy n left right = k

/-- Allowed-sector shell coverage up to the generated residual-energy bound.

This is the physical producer target after P948: not all raw pairs must
descend, but the SU(7)-selected sector must realize every residual shell. -/
def BoolGaugeFilteredRawCodePairEnergyCoverage
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) : Prop :=
  ∀ k : ℕ, k < generatedRawBranchingMaxEnergy n bound ->
    BoolGaugeFilteredRawCodePairEnergyShellRealized n bound allowed k

/-! ## Forgetting allowed-sector coverage -/

/-- Allowed shell realization forgets to ordinary raw code-pair shell
realization. -/
theorem rawCodePairShell_of_boolGaugeFilteredShell
    {n bound k : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (h : BoolGaugeFilteredRawCodePairEnergyShellRealized
      n bound allowed k) :
    RawCodePairEnergyShellRealized n bound k := by
  rcases h with
    ⟨left, right, _hallowed, hleft_mem, hright_mem,
      hleft_check, hright_check, henergy⟩
  exact
    ⟨left, right, hleft_mem, hright_mem,
      hleft_check, hright_check, henergy⟩

/-- Allowed-sector shell coverage forgets to raw code-pair shell coverage. -/
theorem rawCodePairCoverage_of_boolGaugeFilteredCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    RawCodePairEnergyCoverage n bound := by
  intro k hk
  exact rawCodePairShell_of_boolGaugeFilteredShell (H k hk)

/-- Allowed-sector shell coverage gives P964's generated shell coverage. -/
theorem generatedRawEnergyCoverage_of_boolGaugeFilteredCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    GeneratedRawEnergyCoverage n bound :=
  (generatedRawEnergyCoverage_iff_codePairCoverage n bound).mpr
    (rawCodePairCoverage_of_boolGaugeFilteredCoverage H)

/-! ## Allowed shell coverage gives unit descent in the allowed sector -/

/-- Any bounded Boolean-atomic raw endpoint pair has residual energy bounded
by the generated raw maximum, because its canonical SU(7) lift appears in the
explicit generated spectrum. -/
theorem rawCodePairResidualEnergy_le_generatedRawMaxEnergy_of_bounded_atomic
    {n bound left right : ℕ}
    (hleft_mem : left ∈ rawCodeBoundedList bound)
    (hright_mem : right ∈ rawCodeBoundedList bound)
    (hleft_check : natMultiplicativelyAtomicCheck left = true)
    (hright_check : natMultiplicativelyAtomicCheck right = true) :
    rawCodePairResidualEnergy n left right ≤
      generatedRawBranchingMaxEnergy n bound := by
  let x :=
    booleanAtomicCellOfRawCodePair
      n left right hleft_check hright_check
  have hxmem :
      x ∈ booleanAtomicRawBranchingCandidateList n bound :=
    booleanAtomicCellOfRawCodePair_mem_generated
      hleft_mem hright_mem hleft_check hright_check
  have hxcell_mem :
      x.cell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells :=
    booleanAtomicCell_mem_booleanGeneratedSpectrum hxmem
  have hbound :
      rawAtomCodeBranchingDecompositionResidualEnergy x.cell ≤
        generatedRawBranchingMaxEnergy n bound :=
    generatedRawBranching_energy_bound x.cell hxcell_mem
  simpa [x, booleanAtomicCellOfRawCodePair_energy_eq] using hbound

/-- Gauge-filtered shell coverage gives one-unit descent for every active
allowed raw code-pair. -/
theorem boolGaugeFilteredUnitSuccessorLaw_of_energyCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      n bound allowed := by
  intro left right hallowed hleft_mem hright_mem
    hleft_check hright_check hnonzero
  let e := rawCodePairResidualEnergy n left right
  have he_pos : 0 < e := by
    dsimp [e]
    omega
  have he_le :
      e ≤ generatedRawBranchingMaxEnergy n bound := by
    dsimp [e]
    exact
      rawCodePairResidualEnergy_le_generatedRawMaxEnergy_of_bounded_atomic
        hleft_mem hright_mem hleft_check hright_check
  have hklt : e - 1 < generatedRawBranchingMaxEnergy n bound := by
    omega
  rcases H (e - 1) hklt with
    ⟨left', right', hallowed', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, henergy'⟩
  refine
    ⟨left', right', hallowed', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, ?_⟩
  rw [henergy']
  omega

/-- Gauge-filtered shell coverage forbids filtered raw code-pair permanent
holonomy. -/
theorem boolGaugeFilteredForbidsPermanentHolonomy_of_energyCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    BoolGaugeFilteredRawCodePairForbidsUnitPermanentHolonomy
      n bound allowed :=
  (noFilteredRawCodePairPermanentHolonomy_iff_unitSuccessorLaw
    n bound allowed).mpr
      (boolGaugeFilteredUnitSuccessorLaw_of_energyCoverage H)

/-- Gauge-filtered shell coverage forbids unit permanent holonomy in the
filtered generated spectrum. -/
theorem filteredSpectrumNoHolonomy_of_boolGaugeFilteredCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound allowed) :=
  gaugeFilteredForbidsUnitPermanentHolonomy_of_rawCodePairLaw
    (boolGaugeFilteredUnitSuccessorLaw_of_energyCoverage H)

/-! ## Feeding P964's no-prime flow/quantization throat -/

/-- Gauge-filtered shell coverage produces the generated no-prime
flow/quantization certificate by forgetting the allowed tag at the P964
boundary. -/
def generatedNoPrimeFlowQuantizationCertificate_of_boolGaugeFilteredCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (hbound : 2 ≤ bound)
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n :=
  generatedNoPrimeFlowQuantizationCertificate_of_energyCoverage hbound
    (generatedRawEnergyCoverage_of_boolGaugeFilteredCoverage H)

/-- Gauge-filtered shell coverage also yields the P964 filtered generated
no-holonomy readout for the no-prime list. -/
def noPrimeFilteredNoHolonomy_of_boolGaugeFilteredCoverage
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (hbound : 2 ≤ bound)
    (H : BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n bound))) :=
  filteredNoHolonomy_of_generatedEnergyCoverage_via_flowQuantization hbound
    (generatedRawEnergyCoverage_of_boolGaugeFilteredCoverage H)

/-! ## Certificate -/

/-- P965 certificate: allowed-sector shell coverage is the exact no-gap
producer object now needed by the color-loop route. -/
structure SU7GaugeFilteredShellCoverageProducerCertificate where
  allowed_shell_to_raw_shell :
    ∀ {n bound k : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairEnergyShellRealized n bound allowed k ->
        RawCodePairEnergyShellRealized n bound k
  allowed_coverage_to_generated_coverage :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed ->
        GeneratedRawEnergyCoverage n bound
  bounded_atomic_energy_le_generated_max :
    ∀ {n bound left right : ℕ},
      left ∈ rawCodeBoundedList bound ->
        right ∈ rawCodeBoundedList bound ->
          natMultiplicativelyAtomicCheck left = true ->
            natMultiplicativelyAtomicCheck right = true ->
              rawCodePairResidualEnergy n left right ≤
                generatedRawBranchingMaxEnergy n bound
  allowed_coverage_to_unit_successor :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed ->
        BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw n bound allowed
  allowed_coverage_to_no_filtered_holonomy :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound allowed)
  allowed_coverage_to_no_prime_flow_quantization :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      2 ≤ bound ->
        BoolGaugeFilteredRawCodePairEnergyCoverage n bound allowed ->
          SU7GeneratedNoPrimeFlowQuantizationCertificate n

/-- Canonical P965 gauge-filtered shell-coverage producer certificate. -/
def su7GaugeFilteredShellCoverageProducerCertificate :
    SU7GaugeFilteredShellCoverageProducerCertificate where
  allowed_shell_to_raw_shell :=
    rawCodePairShell_of_boolGaugeFilteredShell
  allowed_coverage_to_generated_coverage :=
    generatedRawEnergyCoverage_of_boolGaugeFilteredCoverage
  bounded_atomic_energy_le_generated_max :=
    rawCodePairResidualEnergy_le_generatedRawMaxEnergy_of_bounded_atomic
  allowed_coverage_to_unit_successor :=
    boolGaugeFilteredUnitSuccessorLaw_of_energyCoverage
  allowed_coverage_to_no_filtered_holonomy :=
    filteredSpectrumNoHolonomy_of_boolGaugeFilteredCoverage
  allowed_coverage_to_no_prime_flow_quantization := by
    intro n bound allowed hbound H
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_boolGaugeFilteredCoverage
        hbound H


end
end StandardModelConstraint
end SaturationMonoid
