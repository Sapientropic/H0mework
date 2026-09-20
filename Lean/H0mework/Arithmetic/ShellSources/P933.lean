import H0mework.Arithmetic.ShellSources.P932

/-!
# Proposition 933: no-prime normalizers generate zero branch cells

P932 removed prime data from the SU(7) branching-spectrum cell and proved that
prime-edge loops are generated only at projection time.  This file removes the
next receipt: a producer does not have to store a zero cell either.

A no-prime residual-transport normalizer stores only:

* a spectrum of no-prime branch cells;
* a start cell;
* a normalization map;
* strict decrease of residual energy away from zero;
* fixedness on the zero residual fiber.

Strong induction on residual energy then generates a zero no-prime branch cell.
The final prime-edge loop is still produced through P932's tensor-irreducibility
projection.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## No-prime residual energy -/

/-- Absolute residual energy of a no-prime SU(7) branch-spectrum cell. -/
def noPrimeBranchingResidualEnergy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) : ℕ :=
  Int.natAbs (noPrimeBranchingResidual B)

/-! ## Residual-transport normalizers -/

/-- A no-prime residual-transport normalizer.

It contains no prime pair and no zero-cell witness.  The only dynamics field is
`normalize`, with strict residual-energy descent off the zero fiber. -/
structure SU7NoPrimeBranchingResidualNormalizer
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : List (SU7NoPrimeBranchingSpectrumCell C n)
  startCell : SU7NoPrimeBranchingSpectrumCell C n
  start_mem : startCell ∈ spectrum
  normalize :
    SU7NoPrimeBranchingSpectrumCell C n ->
      SU7NoPrimeBranchingSpectrumCell C n
  normalize_mem_preserves :
    ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ spectrum -> normalize B ∈ spectrum
  normalize_strictly_decreases_nonzero :
    ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ spectrum ->
        noPrimeBranchingResidual B ≠ 0 ->
          noPrimeBranchingResidualEnergy (normalize B) <
            noPrimeBranchingResidualEnergy B
  normalize_fixed_of_zero :
    ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ spectrum ->
        noPrimeBranchingResidual B = 0 ->
          normalize B = B

/-- Active fixed points of a no-prime normalizer are exactly zero residual
cells. -/
theorem noPrimeNormalizer_fixed_iff_residual_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7NoPrimeBranchingResidualNormalizer C n)
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hmem : B ∈ N.spectrum) :
    N.normalize B = B ↔ noPrimeBranchingResidual B = 0 := by
  constructor
  · intro hfixed
    by_contra hnonzero
    have hlt :
        noPrimeBranchingResidualEnergy B <
          noPrimeBranchingResidualEnergy B := by
      simpa [hfixed] using
        N.normalize_strictly_decreases_nonzero B hmem hnonzero
    exact (Nat.lt_irrefl _) hlt
  · intro hzero
    exact N.normalize_fixed_of_zero B hmem hzero

/-- A no-prime residual normalizer generates a zero residual branch cell by
strong induction on residual energy. -/
theorem exists_zeroNoPrimeCell_of_normalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7NoPrimeBranchingResidualNormalizer C n) :
    ∃ Z : SU7NoPrimeBranchingSpectrumCell C n,
      Z ∈ N.spectrum ∧ noPrimeBranchingResidual Z = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ N.spectrum ->
        noPrimeBranchingResidualEnergy B = e ->
          ∃ Z : SU7NoPrimeBranchingSpectrumCell C n,
            Z ∈ N.spectrum ∧ noPrimeBranchingResidual Z = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih B hmem henergy
    by_cases hzero : noPrimeBranchingResidual B = 0
    · exact ⟨B, hmem, hzero⟩
    · have hnext_mem : N.normalize B ∈ N.spectrum :=
        N.normalize_mem_preserves B hmem
      have hnext_lt :
          noPrimeBranchingResidualEnergy (N.normalize B) <
            noPrimeBranchingResidualEnergy B :=
        N.normalize_strictly_decreases_nonzero B hmem hzero
      exact ih
        (noPrimeBranchingResidualEnergy (N.normalize B))
        (by simpa [henergy] using hnext_lt)
        (N.normalize B) hnext_mem rfl
  have hstart :
      motive (noPrimeBranchingResidualEnergy N.startCell) :=
    Nat.strong_induction_on
      (noPrimeBranchingResidualEnergy N.startCell) hstep
  exact hstart N.startCell N.start_mem rfl

/-! ## Generated no-prime zero cells -/

/-- A generated no-prime zero branch cell.  It stores the zero residual proof,
but still no prime pair; prime-edge data are projected only downstream. -/
structure SU7GeneratedNoPrimeZeroBranchCell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  cell : SU7NoPrimeBranchingSpectrumCell C n
  residual_zero : noPrimeBranchingResidual cell = 0

/-- A generated no-prime zero cell projects to arithmetic balance. -/
theorem SU7GeneratedNoPrimeZeroBranchCell.sum_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    (G : SU7GeneratedNoPrimeZeroBranchCell C n) :
    atomCode G.cell.leftAtom.toSU7Atom +
        atomCode G.cell.rightAtom.toSU7Atom =
      2 * n :=
  noPrimeBranchingResidual_zero_to_sum G.cell G.residual_zero

/-- A generated no-prime zero cell projects to a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_generatedNoPrimeZeroCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (G : SU7GeneratedNoPrimeZeroBranchCell C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_noPrimeBranchingCell G.cell G.residual_zero

/-- A no-prime normalizer computes a generated no-prime zero cell. -/
def generatedNoPrimeZeroCell_of_normalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7NoPrimeBranchingResidualNormalizer C n) :
    SU7GeneratedNoPrimeZeroBranchCell C n :=
  let Z := Classical.choose (exists_zeroNoPrimeCell_of_normalizer N)
  let hZ := Classical.choose_spec (exists_zeroNoPrimeCell_of_normalizer N)
  { cell := Z
    residual_zero := hZ.2 }

/-- A no-prime normalizer computes a trace-zero prime-edge loop via P932's
projection. -/
def traceZeroPrimeEdgeLoop_of_noPrimeNormalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7NoPrimeBranchingResidualNormalizer C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedNoPrimeZeroCell
    (generatedNoPrimeZeroCell_of_normalizer N)

/-! ## Fiberwise normalizer producers -/

/-- Every even fiber carries a no-prime residual-transport normalizer. -/
def SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7NoPrimeBranchingResidualNormalizer C n)

/-- Fiberwise no-prime normalizers compute trace-zero prime-edge loops. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_noPrimeNormalizers
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_noPrimeNormalizer
    (Classical.choice (H n hn))

/-- Fiberwise no-prime normalizers give ordinary even Goldbach through the
generated no-prime cell projection. -/
theorem evenGoldbach_of_noPrimeNormalizers
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_noPrimeNormalizers H)

/-! ## Certificate -/

/-- P933 certificate: a residual-transport normalizer over no-prime branch
cells generates zero cells and then trace-zero prime-edge loops. -/
structure SU7NoPrimeResidualNormalizerProducerCertificate where
  fixed_iff_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7NoPrimeBranchingResidualNormalizer C n)
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      B ∈ N.spectrum ->
        (N.normalize B = B ↔ noPrimeBranchingResidual B = 0)
  normalizer_to_zero_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7NoPrimeBranchingResidualNormalizer C n),
      ∃ Z : SU7NoPrimeBranchingSpectrumCell C n,
        Z ∈ N.spectrum ∧ noPrimeBranchingResidual Z = 0
  normalizer_to_generated_no_prime_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7NoPrimeBranchingResidualNormalizer C n ->
        SU7GeneratedNoPrimeZeroBranchCell C n
  generated_zero_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7GeneratedNoPrimeZeroBranchCell C n -> TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical no-prime residual-normalizer producer certificate. -/
def su7NoPrimeResidualNormalizerProducerCertificate :
    SU7NoPrimeResidualNormalizerProducerCertificate where
  fixed_iff_zero := noPrimeNormalizer_fixed_iff_residual_zero
  normalizer_to_zero_cell := exists_zeroNoPrimeCell_of_normalizer
  normalizer_to_generated_no_prime_zero :=
    generatedNoPrimeZeroCell_of_normalizer
  generated_zero_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_generatedNoPrimeZeroCell
  every_fiber_to_goldbach := evenGoldbach_of_noPrimeNormalizers


end
end StandardModelConstraint
end SaturationMonoid
