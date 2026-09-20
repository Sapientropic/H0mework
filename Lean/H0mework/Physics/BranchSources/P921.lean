import H0mework.Physics.BranchSources.P920

/-!
# Proposition 921: local tensor filters for checked raw spectra

P910/P918 used a global tensor-irreducibility filter over all raw
branching-decomposition cells in a fiber.  That is too strong for an executable
finite spectrum generator: a generated list only needs tensor irreducibility
for the cells it actually contains.

This file replaces that throat with a membership-scoped tensor filter.  A
checked finite spectrum with

* local endpoint tensor irreducibility for in-list cells;
* raw energy bounds;
* Boolean energy-shell coverage;

produces a physical zero branch cell first, and only then projects to
prime-edge data.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Local tensor filters -/

/-- Tensor irreducibility required only for cells contained in one finite raw
branching spectrum. -/
structure SU7RawBranchingLocalTensorFilter
    (C : SU7WeightTensorCoding) {n : ℕ}
    (S : SU7BranchingDecompositionSpectrum n) where
  left_tensor_irreducible :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ S.cells ->
        SU7TensorIrreducible C { code := c.leftWeightCode }
  right_tensor_irreducible :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ S.cells ->
        SU7TensorIrreducible C { code := c.rightWeightCode }

/-- Lift one in-spectrum raw cell to a tensor-irreducible cell using only the
local tensor filter. -/
def tensorIrreducibleCell_of_localRawBranchingCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ S.cells) :
    SU7TensorIrreducibleBranchingSpectrumCell C n where
  branch := c.branch
  leftAtom :=
    { weight := { code := c.leftWeightCode }
      tensor_irreducible := F.left_tensor_irreducible c hmem
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints c.incidence).1 }
  rightAtom :=
    { weight := { code := c.rightWeightCode }
      tensor_irreducible := F.right_tensor_irreducible c hmem
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints c.incidence).2 }

/-- The local tensor lift preserves raw residual exactly. -/
theorem tensorIrreducibleCell_of_localRawBranchingCell_rawResidual_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ S.cells) :
    tensorIrreducibleBranchingSpectrumResidual
        (tensorIrreducibleCell_of_localRawBranchingCell F c hmem) =
      rawAtomCodeBranchingDecompositionResidual c := by
  rfl

/-- A local tensor-filtered zero raw cell computes a generated physical zero
branch cell without any global irreducibility assumption. -/
def generatedPhysicalZeroBranchCell_of_localRawZeroCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ S.cells)
    (hzero : rawAtomCodeBranchingDecompositionResidual c = 0) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  let B := tensorIrreducibleCell_of_localRawBranchingCell F c hmem
  { cell := physicalBranchCell_of_tensorIrreducibleCell B
    residual_zero := by
      have hBzero : tensorIrreducibleBranchingSpectrumResidual B = 0 := by
        change
          tensorIrreducibleBranchingSpectrumResidual
              (tensorIrreducibleCell_of_localRawBranchingCell F c hmem) = 0
        rw [tensorIrreducibleCell_of_localRawBranchingCell_rawResidual_eq]
        exact hzero
      exact physicalResidual_zero_of_tensorIrreducibleCell B hBzero
    left_atomCode_prime := tensorPhysicalBranchCell_left_atomCode_prime B
    right_atomCode_prime := tensorPhysicalBranchCell_right_atomCode_prime B }

/-! ## Zero cells from local successor laws -/

/-- A spectrum-level unit successor law, together with a start cell, produces
a zero raw residual cell.  This proof does not use any tensor filter. -/
theorem exists_zeroRawCell_of_unitSuccessorLaw_from_start
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (start : SU7BranchingDecompositionCell n)
    (hstart : start ∈ S.cells)
    (Hsucc : SU7RawBranchingSpectrumUnitSuccessorLaw S) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ S.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 := by
  let E (c : SU7BranchingDecompositionCell n) :=
    rawAtomCodeBranchingDecompositionResidualEnergy c
  let motive (e : ℕ) : Prop :=
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ S.cells ->
        E c = e ->
          ∃ z : SU7BranchingDecompositionCell n,
            z ∈ S.cells ∧
              rawAtomCodeBranchingDecompositionResidual z = 0
  have hmain : ∀ e : ℕ, motive e := by
    intro e
    refine Nat.strong_induction_on e ?_
    intro e ih c hmem hE
    by_cases hzero : rawAtomCodeBranchingDecompositionResidual c = 0
    · exact ⟨c, hmem, hzero⟩
    · rcases Hsucc c hmem hzero with ⟨next, hnext_mem, hnext_E⟩
      have hnext_lt : E next < e := by
        dsimp [E] at hnext_E hE ⊢
        omega
      exact ih (E next) hnext_lt next hnext_mem rfl
  exact hmain (E start) start hstart rfl

/-! ## Local no-gap rules -/

/-- A local no-gap rule for a finite raw spectrum.

The tensor irreducibility proof is scoped to members of `spectrum.cells`.
Confinement/no-gap is purely residual-dynamical. -/
structure SU7RawBranchingLocalNoGapRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  local_tensor_filter : SU7RawBranchingLocalTensorFilter C spectrum
  forbids_strict_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy spectrum
  energy_unit_density :
    SU7RawBranchingSpectrumEnergyUnitDensity spectrum

/-- A local no-gap rule produces the spectrum-level unit successor law. -/
def unitSuccessorLaw_of_localNoGapRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingLocalNoGapRule C n) :
    SU7RawBranchingSpectrumUnitSuccessorLaw R.spectrum :=
  unitSuccessorLaw_of_strictSuccessorLaw_and_unitDensity
    R.spectrum
    ((noRawStrictPermanentHolonomy_iff_strictSuccessorLaw R.spectrum).mp
      R.forbids_strict_permanent_holonomy)
    R.energy_unit_density

/-- A local no-gap rule computes an in-spectrum zero raw residual cell. -/
theorem exists_zeroRawCell_of_localNoGapRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingLocalNoGapRule C n) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ R.spectrum.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 :=
  exists_zeroRawCell_of_unitSuccessorLaw_from_start
    R.spectrum R.startCell R.start_mem
    (unitSuccessorLaw_of_localNoGapRule R)

/-- A local no-gap rule computes a generated physical zero branch cell using
only membership-scoped tensor irreducibility at the selected zero cell. -/
def generatedPhysicalZeroBranchCell_of_localNoGapRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingLocalNoGapRule C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  let hZ := exists_zeroRawCell_of_localNoGapRule R
  let z := Classical.choose hZ
  let hz := Classical.choose_spec hZ
  generatedPhysicalZeroBranchCell_of_localRawZeroCell
    R.local_tensor_filter z hz.1 hz.2

/-- A local no-gap rule computes a trace-zero prime-edge loop by projecting
the generated physical zero branch cell. -/
def traceZeroPrimeEdgeLoop_of_localNoGapRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingLocalNoGapRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_localNoGapRule R)

/-! ## Checked local energy-shell rules -/

/-- Executable checked finite raw spectrum with membership-scoped tensor
irreducibility. -/
structure SU7RawBranchingCheckedLocalEnergyShellRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  local_tensor_filter : SU7RawBranchingLocalTensorFilter C spectrum
  maxEnergy : ℕ
  energy_bound :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c ≤ maxEnergy
  coverage_check :
    rawBranchingEnergyShellCoverageCheck spectrum maxEnergy = true

/-- A checked local energy-shell rule has strict residual descent. -/
theorem checkedLocalEnergyShell_strictSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedLocalEnergyShellRule C n) :
    SU7RawBranchingSpectrumStrictSuccessorLaw R.spectrum := by
  intro c hmem hnonzero
  let e := rawAtomCodeBranchingDecompositionResidualEnergy c
  have hpos : 0 < e :=
    rawAtomCodeBranchingDecompositionResidualEnergy_pos_of_nonzero
      c hnonzero
  have hle : e ≤ R.maxEnergy := R.energy_bound c hmem
  have hcov :
      SU7RawBranchingEnergyShellCoverage R.spectrum R.maxEnergy :=
    rawBranchingEnergyShellCoverage_of_check
      R.spectrum R.maxEnergy R.coverage_check
  rcases hcov e hpos hle with ⟨lower, hlower_mem, hlower_E⟩
  refine ⟨lower, hlower_mem, ?_⟩
  rw [hlower_E]
  omega

/-- A checked local energy-shell rule has unit density. -/
theorem checkedLocalEnergyShell_energyUnitDensity
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedLocalEnergyShellRule C n) :
    SU7RawBranchingSpectrumEnergyUnitDensity R.spectrum := by
  intro c lower hmem _hlower_mem hlower_lt
  let e := rawAtomCodeBranchingDecompositionResidualEnergy c
  have hpos : 0 < e := by
    omega
  have hle : e ≤ R.maxEnergy := R.energy_bound c hmem
  have hcov :
      SU7RawBranchingEnergyShellCoverage R.spectrum R.maxEnergy :=
    rawBranchingEnergyShellCoverage_of_check
      R.spectrum R.maxEnergy R.coverage_check
  rcases hcov e hpos hle with ⟨step, hstep_mem, hstep_E⟩
  refine ⟨step, hstep_mem, ?_⟩
  rw [hstep_E]
  omega

/-- A checked local energy-shell rule generates a local no-gap rule. -/
def localNoGapRule_of_checkedLocalEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedLocalEnergyShellRule C n) :
    SU7RawBranchingLocalNoGapRule C n where
  spectrum := R.spectrum
  startCell := R.startCell
  start_mem := R.start_mem
  local_tensor_filter := R.local_tensor_filter
  forbids_strict_permanent_holonomy :=
    (noRawStrictPermanentHolonomy_iff_strictSuccessorLaw R.spectrum).mpr
      (checkedLocalEnergyShell_strictSuccessorLaw R)
  energy_unit_density :=
    checkedLocalEnergyShell_energyUnitDensity R

/-- A checked local energy-shell rule computes a generated physical zero
branch cell. -/
def generatedPhysicalZeroBranchCell_of_checkedLocalEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedLocalEnergyShellRule C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_localNoGapRule
    (localNoGapRule_of_checkedLocalEnergyShellRule R)

/-- A checked local energy-shell rule computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_checkedLocalEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedLocalEnergyShellRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_checkedLocalEnergyShellRule R)

/-- Every even fiber carries a checked local energy-shell rule. -/
def SU7RawBranchingCheckedLocalEnergyShellRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingCheckedLocalEnergyShellRule C n)

/-- Fiberwise checked local energy-shell rules produce generated physical zero
branch cells on every even fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_checkedLocalEnergyShellRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedLocalEnergyShellRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_checkedLocalEnergyShellRule
    (Classical.choice (H n hn))

/-- Fiberwise checked local energy-shell rules give ordinary even Goldbach. -/
theorem evenGoldbach_of_checkedLocalEnergyShellRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedLocalEnergyShellRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (fun n hn =>
      traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
        (generatedPhysicalZeroBranchCellEveryEvenFiber_of_checkedLocalEnergyShellRules
          H n hn))

/-! ## Certificate -/

/-- P921 certificate: checked raw spectra now need only local tensor
irreducibility for listed cells. -/
structure SU7CheckedLocalEnergyShellProducerCertificate where
  local_zero_cell :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (start : SU7BranchingDecompositionCell n),
      start ∈ S.cells ->
        SU7RawBranchingSpectrumUnitSuccessorLaw S ->
          ∃ z : SU7BranchingDecompositionCell n,
            z ∈ S.cells ∧
              rawAtomCodeBranchingDecompositionResidual z = 0
  local_zero_to_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n}
      (_F : SU7RawBranchingLocalTensorFilter C S)
      (c : SU7BranchingDecompositionCell n),
      c ∈ S.cells ->
        rawAtomCodeBranchingDecompositionResidual c = 0 ->
          SU7GeneratedPhysicalZeroBranchCell n
  checked_rule_to_local_no_gap :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingCheckedLocalEnergyShellRule C n ->
        SU7RawBranchingLocalNoGapRule C n
  checked_rule_to_physical_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingCheckedLocalEnergyShellRule C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingCheckedLocalEnergyShellRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P921 local-filter producer certificate. -/
def su7CheckedLocalEnergyShellProducerCertificate :
    SU7CheckedLocalEnergyShellProducerCertificate where
  local_zero_cell :=
    exists_zeroRawCell_of_unitSuccessorLaw_from_start
  local_zero_to_physical :=
    generatedPhysicalZeroBranchCell_of_localRawZeroCell
  checked_rule_to_local_no_gap :=
    localNoGapRule_of_checkedLocalEnergyShellRule
  checked_rule_to_physical_zero :=
    generatedPhysicalZeroBranchCell_of_checkedLocalEnergyShellRule
  every_fiber_to_goldbach :=
    evenGoldbach_of_checkedLocalEnergyShellRules


end
end StandardModelConstraint
end SaturationMonoid
