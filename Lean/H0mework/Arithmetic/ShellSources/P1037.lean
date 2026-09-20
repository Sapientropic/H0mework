import H0mework.Arithmetic.ShellSources.P1036

/-!
# Proposition 1037: nonempty checked shells are enough

P1036 used a checked shell plus an explicit start cell.  Runtime does not need
to emit that start separately: a nonempty finite checked source list is enough,
and Lean can choose the source anchor.

```text
checked finite no-prime shell + cells nonempty
  -> checked shell with start
  -> residual normalizer
  -> tensor-atom lift producer
```

This is also the preferred lower target for SU(7) representation / encoding /
finite-spectrum producers: prove the finite checked source list plus
nonemptiness, then transport through the normalizer chain rather than trying to
produce prime endpoints or a zero endpoint directly.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Nonempty checked shell interface -/

/-- A finite checked no-prime shell with a nonempty source list. -/
structure SU7NoPrimeNonemptyCheckedShell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  rule : SU7NoPrimeBranchingCheckedEnergyShellRule C n
  cells_nonempty : rule.cells ≠ []

/-- A nonempty checked shell yields the start-cell form required by P1036. -/
def checkedShellWithStart_of_nonemptyCheckedShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (S : SU7NoPrimeNonemptyCheckedShell C n) :
    SU7NoPrimeCheckedShellWithStart C n :=
  let hmem :=
    List.exists_mem_of_ne_nil S.rule.cells S.cells_nonempty
  { rule := S.rule
    startCell := Classical.choose hmem
    start_mem := Classical.choose_spec hmem }

/-- Every even fiber carries a finite checked no-prime shell with a nonempty
source list. -/
def SU7NoPrimeNonemptyCheckedShellEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7NoPrimeNonemptyCheckedShell C n)

/-- Nonempty checked shells on every even fiber produce checked shells with
starts on every even fiber. -/
theorem checkedShellWithStartEveryEvenFiber_of_nonemptyCheckedShellEveryEvenFiber
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeNonemptyCheckedShellEveryEvenFiber C) :
    SU7NoPrimeCheckedShellWithStartEveryEvenFiber C := by
  intro n hn
  exact ⟨checkedShellWithStart_of_nonemptyCheckedShell
    (Classical.choice (H n hn))⟩

/-- Nonempty checked shells on every even fiber produce P933 residual
normalizers. -/
theorem noPrimeResidualNormalizers_of_nonemptyCheckedShellEveryEvenFiber
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeNonemptyCheckedShellEveryEvenFiber C) :
    SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C :=
  noPrimeResidualNormalizers_of_checkedShellWithStartEveryEvenFiber
    (checkedShellWithStartEveryEvenFiber_of_nonemptyCheckedShellEveryEvenFiber H)

/-- Nonempty checked shells on every even fiber reach the tensor-atom lift
producer. -/
theorem su7TensorAtomLiftProducer_of_nonemptyCheckedShellEveryEvenFiber
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeNonemptyCheckedShellEveryEvenFiber C) :
    SU7TensorAtomLiftProducer C :=
  su7TensorAtomLiftProducer_of_checkedShellWithStartEveryEvenFiber
    (checkedShellWithStartEveryEvenFiber_of_nonemptyCheckedShellEveryEvenFiber H)

/-! ## Canonical raw-coding specialization -/

/-- Canonical raw tensor coding specialization of the nonempty checked-shell
producer interface. -/
theorem su7TensorAtomLiftProducer_of_rawNonemptyCheckedShellEveryEvenFiber
    (H :
      SU7NoPrimeNonemptyCheckedShellEveryEvenFiber rawCodeTensorCoding) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_nonemptyCheckedShellEveryEvenFiber H

/-! ## Generated unit-confinement entrance -/

/-- A generated no-prime unit-confinement certificate produces the finite
nonempty checked-shell throat.  This is the low-friction source target for
representation / encoding / finite-spectrum routes: it asks only for the
generated finite list, the executable coverage check, and nonemptiness. -/
def nonemptyCheckedShell_of_generatedNoPrimeUnitConfinement
    {n : ℕ}
    (G : SU7GeneratedNoPrimeUnitConfinementCertificate n) :
    SU7NoPrimeNonemptyCheckedShell rawCodeTensorCoding n where
  rule :=
    generatedNoPrimeCheckedEnergyShellRuleOfCheck
      (generatedNoPrimeCoverageCheck_of_unitConfinementCertificate G)
  cells_nonempty := by
    exact
      generatedNoPrimeBranchingCells_nonempty_of_bound_ge_two
        n G.codeBound G.codeBound_ge_two

/-- Fiberwise generated no-prime unit confinement now factors through the
nonempty checked-shell interface instead of jumping directly to the residual
normalizer. -/
theorem nonemptyCheckedShellEveryEvenFiber_of_generatedNoPrimeUnitConfinementEveryEvenFiber
    (H : SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber) :
    SU7NoPrimeNonemptyCheckedShellEveryEvenFiber rawCodeTensorCoding := by
  intro n hn
  exact
    ⟨nonemptyCheckedShell_of_generatedNoPrimeUnitConfinement
      (Classical.choice (H n hn))⟩

/-- Generated no-prime unit confinement reaches P933 normalizers through the
nonempty checked-shell throat. -/
theorem noPrimeResidualNormalizers_of_generatedNoPrimeUnitConfinementEveryEvenFiber_via_nonemptyCheckedShell
    (H : SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber) :
    SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber
      rawCodeTensorCoding :=
  noPrimeResidualNormalizers_of_nonemptyCheckedShellEveryEvenFiber
    (nonemptyCheckedShellEveryEvenFiber_of_generatedNoPrimeUnitConfinementEveryEvenFiber H)

/-! ## Certificate -/

/-- P1037 certificate: a nonempty finite checked shell is the leanest
harness-facing producer input for the tensor-atom lift. -/
structure NonemptyCheckedShellTensorProducerCertificate where
  nonempty_shell_to_with_start :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7NoPrimeNonemptyCheckedShell C n ->
        SU7NoPrimeCheckedShellWithStart C n
  nonempty_shells_to_with_start_every_fiber :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeNonemptyCheckedShellEveryEvenFiber C ->
        SU7NoPrimeCheckedShellWithStartEveryEvenFiber C
  nonempty_shells_to_normalizers :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeNonemptyCheckedShellEveryEvenFiber C ->
        SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C
  nonempty_shells_to_tensor_lift :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeNonemptyCheckedShellEveryEvenFiber C ->
        SU7TensorAtomLiftProducer C
  raw_nonempty_shells_to_tensor_lift :
    SU7NoPrimeNonemptyCheckedShellEveryEvenFiber rawCodeTensorCoding ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding
  generated_unit_confinement_to_raw_nonempty_shell :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeUnitConfinementCertificate n ->
        SU7NoPrimeNonemptyCheckedShell rawCodeTensorCoding n
  generated_unit_confinement_every_fiber_to_raw_nonempty_shells :
    SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber ->
      SU7NoPrimeNonemptyCheckedShellEveryEvenFiber rawCodeTensorCoding
  generated_unit_confinement_every_fiber_to_normalizers :
    SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber ->
      SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber rawCodeTensorCoding

/-- Canonical P1037 nonempty checked-shell producer certificate. -/
def nonemptyCheckedShellTensorProducerCertificate :
    NonemptyCheckedShellTensorProducerCertificate where
  nonempty_shell_to_with_start :=
    checkedShellWithStart_of_nonemptyCheckedShell
  nonempty_shells_to_with_start_every_fiber :=
    checkedShellWithStartEveryEvenFiber_of_nonemptyCheckedShellEveryEvenFiber
  nonempty_shells_to_normalizers :=
    noPrimeResidualNormalizers_of_nonemptyCheckedShellEveryEvenFiber
  nonempty_shells_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_nonemptyCheckedShellEveryEvenFiber
  raw_nonempty_shells_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_rawNonemptyCheckedShellEveryEvenFiber
  generated_unit_confinement_to_raw_nonempty_shell :=
    nonemptyCheckedShell_of_generatedNoPrimeUnitConfinement
  generated_unit_confinement_every_fiber_to_raw_nonempty_shells :=
    nonemptyCheckedShellEveryEvenFiber_of_generatedNoPrimeUnitConfinementEveryEvenFiber
  generated_unit_confinement_every_fiber_to_normalizers :=
    noPrimeResidualNormalizers_of_generatedNoPrimeUnitConfinementEveryEvenFiber_via_nonemptyCheckedShell


end
end StandardModelConstraint
end SaturationMonoid
