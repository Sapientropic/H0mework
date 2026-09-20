import H0mework.Arithmetic.ShellSources.P1032
import H0mework.Arithmetic.ShellSources.P961

/-!
# Proposition 1033: checked no-prime shells generate residual normalizers

P1032 connects no-prime residual normalizers to the tensor-atom lift producer.
P954/P961 already produce finite no-prime energy-shell descent data, but that
data had not been made into the P933 executable normalizer shape.

This file closes that gap:

```text
checked no-prime energy shell + nonempty source list
  -> residual normalizer
  -> no-prime residual dynamics tensor-atom producer
```

The construction stores no zero cell and no prime-edge endpoint.  The
normalizer maps an active cell to a source cell in a strictly lower residual
energy shell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Residual-energy readout equality -/

/-- The P933 residual energy and the P952 endpoint residual energy are the
same readout on a no-prime branch cell. -/
theorem noPrimeBranchingResidualEnergy_eq_endpoint
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    noPrimeBranchingResidualEnergy B =
      noPrimeBranchingEndpointResidualEnergy B := by
  unfold noPrimeBranchingResidualEnergy
    noPrimeBranchingEndpointResidualEnergy
    rawCodePairResidualEnergy rawCodePairResidual
    noPrimeBranchingResidual
    physicalResidual physicalBranchCell_of_noPrimeBranchingCell
    physicalBranchCell_of_tensorIrreducibleCell
    physicalBranchCell_of_physicalSpectrumCell
    physicalBranchingSpectrumCell_of_tensorIrreducibleCell
  rfl

/-- Nonzero residual gives nonzero endpoint residual energy. -/
theorem noPrimeBranchingEndpointResidualEnergy_ne_zero_of_residual_ne_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (h : noPrimeBranchingResidual B ≠ 0) :
    noPrimeBranchingEndpointResidualEnergy B ≠ 0 := by
  rw [← noPrimeBranchingResidualEnergy_eq_endpoint B]
  unfold noPrimeBranchingResidualEnergy
  exact Int.natAbs_ne_zero.mpr h

/-! ## Checked shell rules as normalizers -/

/-- A checked no-prime shell together with an explicit source start cell.  The
start cell is only a nonemptiness witness; it is not a zero-cell witness. -/
structure SU7NoPrimeCheckedShellWithStart
    (C : SU7WeightTensorCoding) (n : ℕ) where
  rule : SU7NoPrimeBranchingCheckedEnergyShellRule C n
  startCell : SU7NoPrimeBranchingSpectrumCell C n
  start_mem : startCell ∈ rule.cells

/-- A checked shell gives a strictly lower P933 residual-energy successor for
every active source cell. -/
theorem checkedShell_exists_lower_residualEnergy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n)
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hmem : B ∈ R.cells)
    (hnonzero : noPrimeBranchingResidual B ≠ 0) :
    ∃ lower : SU7NoPrimeBranchingSpectrumCell C n,
      lower ∈ R.cells ∧
        noPrimeBranchingResidualEnergy lower <
          noPrimeBranchingResidualEnergy B := by
  have hendpoint :
      noPrimeBranchingEndpointResidualEnergy B ≠ 0 :=
    noPrimeBranchingEndpointResidualEnergy_ne_zero_of_residual_ne_zero B
      hnonzero
  rcases noPrimeCheckedEnergyShell_strictSuccessorLaw R
      B hmem hendpoint with
    ⟨lower, hlower_mem, hlower_lt⟩
  refine ⟨lower, hlower_mem, ?_⟩
  rw [noPrimeBranchingResidualEnergy_eq_endpoint lower,
    noPrimeBranchingResidualEnergy_eq_endpoint B]
  exact hlower_lt

/-- Normalize one no-prime source cell by moving to a strictly lower
residual-energy cell when the residual is nonzero, and fixing zero cells. -/
def normalizeOfCheckedShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n)
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    SU7NoPrimeBranchingSpectrumCell C n :=
  by
    classical
    exact
      if hmem : B ∈ R.cells then
        if hzero : noPrimeBranchingResidual B = 0 then
          B
        else
          Classical.choose
            (checkedShell_exists_lower_residualEnergy R B hmem hzero)
    else
      B

/-- The checked-shell normalizer preserves membership in the finite source
list. -/
theorem normalizeOfCheckedShell_mem_preserves
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n)
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hmem : B ∈ R.cells) :
    normalizeOfCheckedShell R B ∈ R.cells := by
  unfold normalizeOfCheckedShell
  classical
  by_cases hzero : noPrimeBranchingResidual B = 0
  · rw [dif_pos hmem, dif_pos hzero]
    exact hmem
  · rw [dif_pos hmem, dif_neg hzero]
    exact
      (Classical.choose_spec
        (checkedShell_exists_lower_residualEnergy R B hmem hzero)).1

/-- The checked-shell normalizer strictly decreases residual energy away from
the zero fiber. -/
theorem normalizeOfCheckedShell_strictly_decreases_nonzero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n)
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hmem : B ∈ R.cells)
    (hnonzero : noPrimeBranchingResidual B ≠ 0) :
    noPrimeBranchingResidualEnergy (normalizeOfCheckedShell R B) <
      noPrimeBranchingResidualEnergy B := by
  unfold normalizeOfCheckedShell
  classical
  rw [dif_pos hmem, dif_neg hnonzero]
  exact
    (Classical.choose_spec
      (checkedShell_exists_lower_residualEnergy R B hmem hnonzero)).2

/-- The checked-shell normalizer fixes zero residual cells. -/
theorem normalizeOfCheckedShell_fixed_of_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n)
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hmem : B ∈ R.cells)
    (hzero : noPrimeBranchingResidual B = 0) :
    normalizeOfCheckedShell R B = B := by
  unfold normalizeOfCheckedShell
  classical
  rw [dif_pos hmem, dif_pos hzero]

/-- A checked no-prime shell with a start cell is exactly a P933 no-prime
residual normalizer. -/
def noPrimeResidualNormalizer_of_checkedShellWithStart
    {C : SU7WeightTensorCoding} {n : ℕ}
    (S : SU7NoPrimeCheckedShellWithStart C n) :
    SU7NoPrimeBranchingResidualNormalizer C n where
  spectrum := S.rule.cells
  startCell := S.startCell
  start_mem := S.start_mem
  normalize := normalizeOfCheckedShell S.rule
  normalize_mem_preserves :=
    normalizeOfCheckedShell_mem_preserves S.rule
  normalize_strictly_decreases_nonzero :=
    normalizeOfCheckedShell_strictly_decreases_nonzero S.rule
  normalize_fixed_of_zero :=
    normalizeOfCheckedShell_fixed_of_zero S.rule

/-! ## Generated checked shells feed the P1032 producer -/

/-- A generated no-prime unit-confinement certificate computes a P933
normalizer.  Nonemptiness is supplied by the `(2, 2)` generated cell from P960;
no zero cell is stored. -/
def noPrimeResidualNormalizer_of_generatedUnitConfinement
    {n : ℕ}
    (G : SU7GeneratedNoPrimeUnitConfinementCertificate n) :
    SU7NoPrimeBranchingResidualNormalizer rawCodeTensorCoding n :=
  let R :=
    generatedNoPrimeCheckedEnergyShellRuleOfCheck
      (generatedNoPrimeCoverageCheck_of_unitConfinementCertificate G)
  let hnonempty :=
    generatedNoPrimeBranchingCells_nonempty_of_bound_ge_two
      n G.codeBound G.codeBound_ge_two
  let start :=
    Classical.choose
      (List.exists_mem_of_ne_nil
        (generatedNoPrimeBranchingCells n G.codeBound) hnonempty)
  let hstart :=
    Classical.choose_spec
      (List.exists_mem_of_ne_nil
        (generatedNoPrimeBranchingCells n G.codeBound) hnonempty)
  noPrimeResidualNormalizer_of_checkedShellWithStart
    { rule := R
      startCell := start
      start_mem := hstart }

/-- Fiberwise generated unit-confinement certificates give P933 normalizers on
every even fiber. -/
theorem noPrimeResidualNormalizers_of_generatedUnitConfinementEveryEvenFiber
    (H : SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber) :
    SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber
      rawCodeTensorCoding := by
  intro n hn
  exact ⟨noPrimeResidualNormalizer_of_generatedUnitConfinement
    (Classical.choice (H n hn))⟩

/-- Fiberwise generated unit confinement feeds the direct P1032 tensor-atom
producer. -/
theorem su7TensorAtomLiftProducer_of_generatedUnitConfinementEveryEvenFiber
    (H : SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_noPrimeResidualNormalizers
    (noPrimeResidualNormalizers_of_generatedUnitConfinementEveryEvenFiber H)

/-- Fiberwise generated Lyapunov/no-gap certificates feed the same direct
tensor-atom producer through unit confinement. -/
theorem su7TensorAtomLiftProducer_of_generatedLyapunovEveryEvenFiber
    (H : SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding := by
  apply su7TensorAtomLiftProducer_of_generatedUnitConfinementEveryEvenFiber
  intro n hn
  exact ⟨generatedNoPrimeUnitConfinementCertificate_of_lyapunov
    (Classical.choice (H n hn))⟩

/-! ## Certificate -/

/-- P1033 certificate: finite checked no-prime shells produce executable
normalizers, and generated unit/Lyapunov confinement now reaches the P1016
tensor-atom lift producer through P1032. -/
structure CheckedShellNormalizerTensorProducerCertificate where
  energy_readouts_equal :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      noPrimeBranchingResidualEnergy B =
        noPrimeBranchingEndpointResidualEnergy B
  checked_shell_to_normalizer :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7NoPrimeCheckedShellWithStart C n ->
        SU7NoPrimeBranchingResidualNormalizer C n
  generated_unit_to_normalizers :
    SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber ->
      SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber
        rawCodeTensorCoding
  generated_unit_to_tensor_lift :
    SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding
  generated_lyapunov_to_tensor_lift :
    SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding

/-- Canonical P1033 certificate. -/
def checkedShellNormalizerTensorProducerCertificate :
    CheckedShellNormalizerTensorProducerCertificate where
  energy_readouts_equal := noPrimeBranchingResidualEnergy_eq_endpoint
  checked_shell_to_normalizer :=
    noPrimeResidualNormalizer_of_checkedShellWithStart
  generated_unit_to_normalizers :=
    noPrimeResidualNormalizers_of_generatedUnitConfinementEveryEvenFiber
  generated_unit_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_generatedUnitConfinementEveryEvenFiber
  generated_lyapunov_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_generatedLyapunovEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
