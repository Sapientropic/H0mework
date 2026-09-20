import H0mework.Arithmetic.ShellSources.P1048
import H0mework.Arithmetic.CodePairs.P944
import H0mework.Arithmetic.ShellSources.P946
import H0mework.Arithmetic.CodePairs.P948

/-!
# Proposition 1049: top-confinement produces ge-three generated coverage

P1048 names the finite generated coverage target consumed by the ge-three
flow/quantization layer.  This file pushes one producer step lower: a generated
top residual cell plus unit-holonomy confinement is enough to fill every lower
generated shell, by P944, and therefore produces the P1048 finite coverage
object with the same endpoint-code bound.

The key discipline here is that a downstream zero cell is not used as a
coverage premise.  The producer is the full-shell top-confinement route:

```text
top generated cell at computed max energy
+ unit-holonomy confinement
-> active support for every lower shell
-> Boolean generated coverage certificate
-> ge-three shell/flow normalizer
```
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Ge-three top-confinement producer -/

/-- Every even fiber carries a generated top-confinement certificate whose
endpoint-code bound is a single fiber function and contains `3`.

This is the physical full-shell producer for P1048: top cell plus unit
confinement, not a prefiltered exact shell. -/
structure SU7GeneratedTopConfinementEveryEvenFiberGeThree where
  codeBound : ℕ -> ℕ
  codeBound_ge_three : ∀ n : ℕ, 2 ≤ n -> 3 ≤ codeBound n
  cert :
    ∀ n : ℕ, 2 ≤ n ->
      SU7GeneratedBooleanRawBranchingTopConfinementCertificate n
  cert_codeBound :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      (cert n hn).codeBound = codeBound n

/-- Forget the ge-three bound discipline and recover the older P944
every-fiber top-confinement proposition. -/
def generatedTopConfinementEveryEvenFiber_of_geThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7GeneratedTopConfinementEveryEvenFiber := by
  intro n hn
  exact ⟨H.cert n hn⟩

/-! ## Top confinement -> transparent and finite generated coverage -/

/-- A ge-three top-confinement producer gives transparent generated raw shell
coverage on every even fiber.  This is the source-facing handoff; the finite
Boolean certificate can be rebuilt from this shell law with the canonical
`(2, 2)` start cell. -/
def generatedRawEnergyCoverageGeThree_of_topConfinementGeThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree where
  codeBound := H.codeBound
  codeBound_ge_three := H.codeBound_ge_three
  energy_coverage := by
    intro n hn
    have hcoverage :
        GeneratedRawEnergyCoverage n (H.cert n hn).codeBound :=
      generatedRawEnergyCoverage_of_topConfinementCertificate (H.cert n hn)
    simpa [H.cert_codeBound n hn] using hcoverage

/-- A ge-three top-confinement producer gives the P1048 finite generated
coverage producer. -/
def generatedBooleanCoverageGeThree_of_topConfinementGeThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7GeneratedBooleanRawBranchingCoverageEveryEvenFiberGeThree :=
  generatedBooleanCoverageGeThree_of_rawEnergyCoverageGeThree
    (generatedRawEnergyCoverageGeThree_of_topConfinementGeThree H)

/-! ## Unit confinement -> top confinement -/

/-- Every even fiber carries a generated unit-confinement certificate whose
endpoint-code bound is a single fiber function and contains `3`.

P946 supplies spectrum nonemptiness from the finite generator, so this is one
producer layer below top confinement: the only physical field is unit-holonomy
confinement. -/
structure SU7GeneratedUnitConfinementEveryEvenFiberGeThree where
  codeBound : ℕ -> ℕ
  codeBound_ge_three : ∀ n : ℕ, 2 ≤ n -> 3 ≤ codeBound n
  cert :
    ∀ n : ℕ, 2 ≤ n ->
      SU7GeneratedBooleanRawBranchingUnitConfinementCertificate n
  cert_codeBound :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      (cert n hn).codeBound = codeBound n

/-- Forget the ge-three bound discipline and recover the older P946
every-fiber unit-confinement proposition. -/
def generatedUnitConfinementEveryEvenFiber_of_geThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7GeneratedUnitConfinementEveryEvenFiber := by
  intro n hn
  exact ⟨H.cert n hn⟩

/-- A ge-three top-confinement producer forgets to the ge-three
unit-confinement producer.  The top cell is useful for the coverage route, but
it is not a second endpoint source once the unit-confinement field and bound
discipline are already present. -/
def generatedUnitConfinementGeThree_of_topConfinementGeThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7GeneratedUnitConfinementEveryEvenFiberGeThree where
  codeBound := H.codeBound
  codeBound_ge_three := H.codeBound_ge_three
  cert := by
    intro n hn
    exact
      { codeBound := (H.cert n hn).codeBound
        codeBound_ge_two := by
          rw [H.cert_codeBound n hn]
          exact two_le_of_three_le_bound (H.codeBound_ge_three n hn)
        forbids_unit_permanent_holonomy :=
          (H.cert n hn).forbids_unit_permanent_holonomy }
  cert_codeBound := H.cert_codeBound

/-- A ge-three unit-confinement producer gives a ge-three top-confinement
producer: nonemptiness is produced by P946, and the top cell is selected by
P945's finite max-attainment theorem. -/
def generatedTopConfinementGeThree_of_unitConfinementGeThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree where
  codeBound := H.codeBound
  codeBound_ge_three := H.codeBound_ge_three
  cert := by
    intro n hn
    exact
      topConfinementCertificate_of_nonemptyConfinementCertificate
        (nonemptyConfinementCertificate_of_unitConfinementCertificate
          (H.cert n hn))
  cert_codeBound := by
    intro n hn
    simp [topConfinementCertificate_of_nonemptyConfinementCertificate,
      nonemptyConfinementCertificate_of_unitConfinementCertificate,
      H.cert_codeBound n hn]

/-- A ge-three unit-confinement producer gives the P1048 finite generated
coverage producer. -/
def generatedBooleanCoverageGeThree_of_unitConfinementGeThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7GeneratedBooleanRawBranchingCoverageEveryEvenFiberGeThree :=
  generatedBooleanCoverageGeThree_of_topConfinementGeThree
    (generatedTopConfinementGeThree_of_unitConfinementGeThree H)

/-- At the source-existence level, ge-three top confinement and ge-three unit
confinement are the same endpoint throat.  Top confinement carries a selected
top cell readout; unit confinement regenerates such a top cell through the
finite-spectrum nonemptiness theorem. -/
theorem nonemptyTopConfinementGeThree_iff_nonemptyUnitConfinementGeThree :
    Nonempty SU7GeneratedTopConfinementEveryEvenFiberGeThree ↔
      Nonempty SU7GeneratedUnitConfinementEveryEvenFiberGeThree := by
  constructor
  · intro h
    exact ⟨generatedUnitConfinementGeThree_of_topConfinementGeThree h.some⟩
  · intro h
    exact ⟨generatedTopConfinementGeThree_of_unitConfinementGeThree h.some⟩

/-! ## Direct downstream handoff -/

/-- A ge-three top-confinement producer gives canonical no-prime endpoint shell
coverage over the raw-code tensor coding. -/
def noPrimeEndpointCoverageGeThree_of_topConfinementGeThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree
      rawCodeTensorCoding :=
  noPrimeEndpointCoverageGeThree_of_generatedBooleanCoverageGeThree
    (generatedBooleanCoverageGeThree_of_topConfinementGeThree H)

/-- A ge-three top-confinement producer gives P1047's ge-three
flow/quantization object. -/
def flowQuantizationGeThree_of_topConfinementGeThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree :=
  flowQuantizationGeThree_of_generatedBooleanCoverageGeThree
    (generatedBooleanCoverageGeThree_of_topConfinementGeThree H)

/-- A ge-three top-confinement producer gives the residual normalizer on every
even fiber. -/
theorem generatedNoPrimeResidualNormalizers_of_topConfinementGeThree
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber :=
  generatedNoPrimeResidualNormalizers_of_generatedBooleanCoverageGeThree
    (generatedBooleanCoverageGeThree_of_topConfinementGeThree H)

/-- A ge-three unit-confinement producer gives transparent generated raw shell
coverage on every even fiber. -/
def generatedRawEnergyCoverageGeThree_of_unitConfinementGeThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree :=
  generatedRawEnergyCoverageGeThree_of_topConfinementGeThree
    (generatedTopConfinementGeThree_of_unitConfinementGeThree H)

/-- A ge-three unit-confinement producer gives canonical no-prime endpoint
shell coverage over the raw-code tensor coding. -/
def noPrimeEndpointCoverageGeThree_of_unitConfinementGeThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree
      rawCodeTensorCoding :=
  noPrimeEndpointCoverageGeThree_of_generatedBooleanCoverageGeThree
    (generatedBooleanCoverageGeThree_of_unitConfinementGeThree H)

/-- A ge-three unit-confinement producer gives P1047's ge-three
flow/quantization object. -/
def flowQuantizationGeThree_of_unitConfinementGeThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree :=
  flowQuantizationGeThree_of_generatedBooleanCoverageGeThree
    (generatedBooleanCoverageGeThree_of_unitConfinementGeThree H)

/-- A ge-three unit-confinement producer gives the residual normalizer on every
even fiber. -/
theorem generatedNoPrimeResidualNormalizers_of_unitConfinementGeThree
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber :=
  generatedNoPrimeResidualNormalizers_of_generatedBooleanCoverageGeThree
    (generatedBooleanCoverageGeThree_of_unitConfinementGeThree H)

/-! ## Boundary: P1049 cannot close at the minimal ge-three bound -/

/-- The generated Boolean raw-branching spectrum at the first obstructed fiber
cannot forbid unit permanent holonomy with endpoint-code bound `3`.

This is the P1049-level version of the P948 obstruction.  It blocks a false
closure route where the ge-three unit/top-confinement throat is inhabited by
the minimal bound alone: the generated spectrum contains the `(3, 3)` shell at
energy `6`, but no generated Boolean-atomic shell at energy `5`. -/
theorem not_booleanGeneratedRawBranchingSpectrum_forbidsUnitHolonomy_six_three :
    ¬ SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum 6 3) := by
  intro hforbid
  have hsucc :
      SU7RawBranchingSpectrumUnitSuccessorLaw
        (booleanGeneratedRawBranchingSpectrum 6 3) :=
    (noRawUnitPermanentHolonomy_iff_unitSuccessorLaw
      (booleanGeneratedRawBranchingSpectrum 6 3)).mp hforbid
  have hshell_six : GeneratedRawEnergyShellRealized 6 3 6 :=
    generatedRawEnergyShell_of_rawCodePairShell
      ⟨3, 3,
        three_mem_rawCodeBoundedList_three,
        three_mem_rawCodeBoundedList_three,
        natMultiplicativelyAtomicCheck_three,
        natMultiplicativelyAtomicCheck_three,
        rawCodePairResidualEnergy_six_three_three⟩
  rcases hshell_six with ⟨x, hxmem, hxenergy⟩
  have hxmem_spectrum :
      x.cell ∈ (booleanGeneratedRawBranchingSpectrum 6 3).cells :=
    booleanAtomicCell_mem_booleanGeneratedSpectrum hxmem
  have hxnonzero :
      rawAtomCodeBranchingDecompositionResidual x.cell ≠ 0 := by
    intro hzero
    have hxenergy_zero :
        rawAtomCodeBranchingDecompositionResidualEnergy x.cell = 0 :=
      (rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff
        x.cell).mpr hzero
    omega
  rcases hsucc x.cell hxmem_spectrum hxnonzero with
    ⟨next, hnext_mem, hnext_energy_succ⟩
  have hnext_energy_five :
      rawAtomCodeBranchingDecompositionResidualEnergy next = 5 := by
    omega
  rcases exists_booleanAtomicCell_of_mem_booleanGeneratedSpectrum
      (n := 6) (bound := 3) hnext_mem with
    ⟨y, hymem, hycell⟩
  have hgenerated_five : GeneratedRawEnergyShellRealized 6 3 5 := by
    refine ⟨y, hymem, ?_⟩
    simpa [hycell] using hnext_energy_five
  exact no_rawCodePairResidualEnergy_five_six_bound_three
    (rawCodePairShell_of_generatedRawEnergyShell hgenerated_five)

/-- A P1049 ge-three unit-confinement producer cannot use endpoint-code
bound `3` at the first obstructed fiber.  Any real producer for this throat
must generate extra endpoint room or a stronger allowed-sector theorem. -/
theorem unitConfinementGeThree_codeBound_six_ne_three
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    H.codeBound 6 ≠ 3 := by
  intro hcode
  have hn : 2 ≤ 6 := by decide
  have hcert_bound : (H.cert 6 hn).codeBound = 3 := by
    rw [H.cert_codeBound 6 hn, hcode]
  have hforbid :
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
        (booleanGeneratedRawBranchingSpectrum 6 3) := by
    simpa [hcert_bound] using
      (H.cert 6 hn).forbids_unit_permanent_holonomy
  exact
    not_booleanGeneratedRawBranchingSpectrum_forbidsUnitHolonomy_six_three
      hforbid

/-- Since P1049's unit-confinement throat already requires `3 <= codeBound`,
the first obstructed fiber must use at least `4`. -/
theorem unitConfinementGeThree_codeBound_six_ge_four
    (H : SU7GeneratedUnitConfinementEveryEvenFiberGeThree) :
    4 ≤ H.codeBound 6 := by
  have hn : 2 ≤ 6 := by decide
  have hge_three : 3 ≤ H.codeBound 6 :=
    H.codeBound_ge_three 6 hn
  have hne_three : H.codeBound 6 ≠ 3 :=
    unitConfinementGeThree_codeBound_six_ne_three H
  omega

/-- A P1049 ge-three top-confinement producer cannot use endpoint-code bound
`3` at the first obstructed fiber, because top confinement also contains the
same unit-holonomy exclusion field for the generated spectrum. -/
theorem topConfinementGeThree_codeBound_six_ne_three
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    H.codeBound 6 ≠ 3 := by
  intro hcode
  have hn : 2 ≤ 6 := by decide
  have hcert_bound : (H.cert 6 hn).codeBound = 3 := by
    rw [H.cert_codeBound 6 hn, hcode]
  have hforbid :
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
        (booleanGeneratedRawBranchingSpectrum 6 3) := by
    simpa [hcert_bound] using
      (H.cert 6 hn).forbids_unit_permanent_holonomy
  exact
    not_booleanGeneratedRawBranchingSpectrum_forbidsUnitHolonomy_six_three
      hforbid

/-- Since P1049's top-confinement throat already requires `3 <= codeBound`,
the first obstructed fiber must use at least `4`. -/
theorem topConfinementGeThree_codeBound_six_ge_four
    (H : SU7GeneratedTopConfinementEveryEvenFiberGeThree) :
    4 ≤ H.codeBound 6 := by
  have hn : 2 ≤ 6 := by decide
  have hge_three : 3 ≤ H.codeBound 6 :=
    H.codeBound_ge_three 6 hn
  have hne_three : H.codeBound 6 ≠ 3 :=
    topConfinementGeThree_codeBound_six_ne_three H
  omega

/-! ## Certificate -/

/-- P1049 certificate: physical full-shell top-confinement is the immediate
producer for P1048's ge-three finite generated coverage target. -/
structure GeneratedTopConfinementGeThreeCoverageProducerCertificate where
  top_ge_three_forgets :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7GeneratedTopConfinementEveryEvenFiber
  top_ge_three_to_generated_coverage :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7GeneratedBooleanRawBranchingCoverageEveryEvenFiberGeThree
  top_ge_three_to_unit_ge_three :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7GeneratedUnitConfinementEveryEvenFiberGeThree
  nonempty_top_iff_unit :
    Nonempty SU7GeneratedTopConfinementEveryEvenFiberGeThree ↔
      Nonempty SU7GeneratedUnitConfinementEveryEvenFiberGeThree
  top_ge_three_to_raw_shells :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree
  top_ge_three_to_no_prime_endpoint_shells :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree
        rawCodeTensorCoding
  top_ge_three_to_flow_quantization :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree
  top_ge_three_to_normalizers :
    SU7GeneratedTopConfinementEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber
  unit_ge_three_forgets :
    SU7GeneratedUnitConfinementEveryEvenFiberGeThree ->
      SU7GeneratedUnitConfinementEveryEvenFiber
  unit_ge_three_to_top_ge_three :
    SU7GeneratedUnitConfinementEveryEvenFiberGeThree ->
      SU7GeneratedTopConfinementEveryEvenFiberGeThree
  unit_ge_three_to_generated_coverage :
    SU7GeneratedUnitConfinementEveryEvenFiberGeThree ->
      SU7GeneratedBooleanRawBranchingCoverageEveryEvenFiberGeThree
  unit_ge_three_to_flow_quantization :
    SU7GeneratedUnitConfinementEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree
  unit_ge_three_to_normalizers :
    SU7GeneratedUnitConfinementEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber

/-- Canonical P1049 top-confinement ge-three producer certificate. -/
def generatedTopConfinementGeThreeCoverageProducerCertificate :
    GeneratedTopConfinementGeThreeCoverageProducerCertificate where
  top_ge_three_forgets :=
    generatedTopConfinementEveryEvenFiber_of_geThree
  top_ge_three_to_generated_coverage :=
    generatedBooleanCoverageGeThree_of_topConfinementGeThree
  top_ge_three_to_unit_ge_three :=
    generatedUnitConfinementGeThree_of_topConfinementGeThree
  nonempty_top_iff_unit :=
    nonemptyTopConfinementGeThree_iff_nonemptyUnitConfinementGeThree
  top_ge_three_to_raw_shells :=
    generatedRawEnergyCoverageGeThree_of_topConfinementGeThree
  top_ge_three_to_no_prime_endpoint_shells :=
    noPrimeEndpointCoverageGeThree_of_topConfinementGeThree
  top_ge_three_to_flow_quantization :=
    flowQuantizationGeThree_of_topConfinementGeThree
  top_ge_three_to_normalizers :=
    generatedNoPrimeResidualNormalizers_of_topConfinementGeThree
  unit_ge_three_forgets :=
    generatedUnitConfinementEveryEvenFiber_of_geThree
  unit_ge_three_to_top_ge_three :=
    generatedTopConfinementGeThree_of_unitConfinementGeThree
  unit_ge_three_to_generated_coverage :=
    generatedBooleanCoverageGeThree_of_unitConfinementGeThree
  unit_ge_three_to_flow_quantization :=
    flowQuantizationGeThree_of_unitConfinementGeThree
  unit_ge_three_to_normalizers :=
    generatedNoPrimeResidualNormalizers_of_unitConfinementGeThree


end
end StandardModelConstraint
end SaturationMonoid
