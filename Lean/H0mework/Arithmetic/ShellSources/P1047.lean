import H0mework.Physics.BranchSources.P1046
import H0mework.Arithmetic.ShellSources.P966

/-!
# Proposition 1047: every-fiber flow quantization with bound `>= 3`

P1046 showed that a P962 generated flow/quantization certificate becomes the
P979 residual normalizer once its endpoint-code bound contains both `2` and
`3`.  This file removes the loose side channel:

```text
every even fiber -> generated no-prime flow/quantization certificate
```

is strengthened to carry the bound proof in the same object.  Downstream code
can now consume a single ge-three producer instead of separately aligning an
existential certificate with a `Classical.choice` bound lemma.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Bound discipline -/

/-- A bound containing `3` also contains the older P962 lower bound `2`. -/
theorem two_le_of_three_le_bound {bound : ℕ} (hbound : 3 ≤ bound) :
    2 ≤ bound := by
  exact Nat.le_trans (by decide : 2 ≤ 3) hbound

/-! ## Flow quantization with the bound welded in -/

/-- Every even fiber carries a generated no-prime flow/quantization certificate
whose endpoint-code bound contains `3`.

This is the exact P1046-ready version of
`SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber`: the witness and the bound
proof travel together. -/
structure SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree where
  cert :
    ∀ n : ℕ, 2 ≤ n ->
      SU7GeneratedNoPrimeFlowQuantizationCertificate n
  codeBound_ge_three :
    ∀ n : ℕ, ∀ hn : 2 ≤ n, 3 ≤ (cert n hn).codeBound

/-- Forget the ge-three bound and recover the earlier P962 every-fiber shape. -/
def flowQuantizationEveryEvenFiber_of_geThree
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber := by
  intro n hn
  exact ⟨H.cert n hn⟩

/-- The ge-three every-fiber object feeds the P1046 residual-normalizer producer
without a separate `Classical.choice` alignment lemma. -/
theorem generatedNoPrimeResidualNormalizers_of_flowQuantizationEveryEvenFiberGeThree
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber := by
  intro n hn
  exact
    ⟨generatedNoPrimeResidualNormalizer_of_flowQuantization
      (H.cert n hn) (H.codeBound_ge_three n hn)⟩

/-! ## Transparent raw coverage entrance, now with `>= 3` -/

/-- Transparent generated raw shell coverage on every even fiber, with the
endpoint-code bound explicitly containing `3`. -/
structure SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree where
  codeBound : ℕ -> ℕ
  codeBound_ge_three : ∀ n : ℕ, 2 ≤ n -> 3 ≤ codeBound n
  energy_coverage :
    ∀ n : ℕ, 2 ≤ n -> GeneratedRawEnergyCoverage n (codeBound n)

/-- Ge-three transparent generated raw shell coverage constructs the stronger
every-fiber generated flow/quantization object. -/
def flowQuantizationGeThree_of_energyCoverageGeThree
    (H : SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree where
  cert := by
    intro n hn
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_energyCoverage
        (two_le_of_three_le_bound (H.codeBound_ge_three n hn))
        (H.energy_coverage n hn)
  codeBound_ge_three := by
    intro n hn
    exact H.codeBound_ge_three n hn

/-- Ge-three transparent generated raw shell coverage still produces the old
P962 every-fiber flow/quantization proposition. -/
def generatedFlowQuantizationEveryEvenFiber_of_energyCoverageGeThree
    (H : SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber :=
  flowQuantizationEveryEvenFiber_of_geThree
    (flowQuantizationGeThree_of_energyCoverageGeThree H)

/-- Ge-three transparent generated raw shell coverage produces the P1046/P979
residual normalizer directly. -/
theorem generatedNoPrimeResidualNormalizers_of_energyCoverageGeThree
    (H : SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree) :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber :=
  generatedNoPrimeResidualNormalizers_of_flowQuantizationEveryEvenFiberGeThree
    (flowQuantizationGeThree_of_energyCoverageGeThree H)

/-! ## No-prime endpoint shell entrance, now with `>= 3` -/

/-- Every even fiber carries a no-prime SU(7) branch-cell source list with
bounded endpoint codes, generated-max shell coverage, and a bound containing
`3`.

The cells still store SU(7) tensor-irreducible atoms and endpoint-energy shell
coverage; this object does not store arithmetic prime pairs or zero endpoints.
-/
structure SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree
    (C : SU7WeightTensorCoding) where
  codeBound : ℕ -> ℕ
  codeBound_ge_three : ∀ n : ℕ, 2 ≤ n -> 3 ≤ codeBound n
  cells :
    ∀ n : ℕ, 2 ≤ n -> List (SU7NoPrimeBranchingSpectrumCell C n)
  cells_within_bound :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      NoPrimeBranchingCellsWithinBound (codeBound n) (cells n hn)
  shell_coverage :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
        (codeBound n) (cells n hn)

/-- Ge-three no-prime branch-cell shell coverage constructs the stronger
every-fiber generated flow/quantization object. -/
def flowQuantizationGeThree_of_noPrimeEndpointCoverageGeThree
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree C) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree where
  cert := by
    intro n hn
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_noPrimeEndpointCoverage
        (two_le_of_three_le_bound (H.codeBound_ge_three n hn))
        (H.cells_within_bound n hn)
        (H.shell_coverage n hn)
  codeBound_ge_three := by
    intro n hn
    exact H.codeBound_ge_three n hn

/-- Ge-three no-prime branch-cell shell coverage still produces the old P962
every-fiber flow/quantization proposition. -/
def generatedFlowQuantizationEveryEvenFiber_of_noPrimeEndpointCoverageGeThree
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree C) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber :=
  flowQuantizationEveryEvenFiber_of_geThree
    (flowQuantizationGeThree_of_noPrimeEndpointCoverageGeThree H)

/-- Ge-three no-prime branch-cell shell coverage produces the P1046/P979
residual normalizer directly. -/
theorem generatedNoPrimeResidualNormalizers_of_noPrimeEndpointCoverageGeThree
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree C) :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber :=
  generatedNoPrimeResidualNormalizers_of_flowQuantizationEveryEvenFiberGeThree
    (flowQuantizationGeThree_of_noPrimeEndpointCoverageGeThree H)

/-! ## Certificate -/

/-- P1047 certificate: the flow/quantization producer is now generated in the
P1046-ready ge-three form, and both coverage entrances feed that form directly.
-/
structure GeneratedFlowQuantizationGeThreeProducerCertificate where
  forget_ge_three :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber
  ge_three_to_normalizers :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber
  raw_coverage_to_ge_three :
    SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree
  raw_coverage_to_normalizers :
    SU7GeneratedRawEnergyCoverageEveryEvenFiberGeThree ->
      SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber
  no_prime_coverage_to_ge_three :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree C ->
        SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiberGeThree
  no_prime_coverage_to_normalizers :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeEndpointShellCoverageEveryEvenFiberGeThree C ->
        SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber

/-- Canonical P1047 ge-three flow/quantization producer certificate. -/
def generatedFlowQuantizationGeThreeProducerCertificate :
    GeneratedFlowQuantizationGeThreeProducerCertificate where
  forget_ge_three := flowQuantizationEveryEvenFiber_of_geThree
  ge_three_to_normalizers :=
    generatedNoPrimeResidualNormalizers_of_flowQuantizationEveryEvenFiberGeThree
  raw_coverage_to_ge_three :=
    flowQuantizationGeThree_of_energyCoverageGeThree
  raw_coverage_to_normalizers :=
    generatedNoPrimeResidualNormalizers_of_energyCoverageGeThree
  no_prime_coverage_to_ge_three := by
    intro C
    exact flowQuantizationGeThree_of_noPrimeEndpointCoverageGeThree
  no_prime_coverage_to_normalizers := by
    intro C
    exact generatedNoPrimeResidualNormalizers_of_noPrimeEndpointCoverageGeThree

end
end StandardModelConstraint
end SaturationMonoid
