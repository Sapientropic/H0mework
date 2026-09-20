import H0mework.Arithmetic.AtomicCodes.P906

/-!
# Proposition 907: tensor-irreducible spectrum confinement produces zero cells

P906 gives the local projection:

```text
tensor-irreducible branch cell + zero raw residual
  -> trace-zero prime-edge loop
```

This file supplies the next producer layer without reintroducing stored prime
fields.  A finite tensor-irreducible branch spectrum carries cells, positive
representation weights, and the confinement-style law that a positive-weight
nonzero residual cell cannot be a terminal holonomy state: there must be a
positive-weight lower-energy cell in the same spectrum.

Strong induction on the raw residual energy then produces a zero residual
cell.  Only after that does P906 compute the prime-edge trace-zero loop from
the tensor irreducibility proofs.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Tensor-irreducible residual energy -/

/-- Residual energy of a tensor-irreducible branch-spectrum cell. -/
def tensorIrreducibleBranchingSpectrumResidualEnergy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) : ℕ :=
  Int.natAbs (tensorIrreducibleBranchingSpectrumResidual B)

/-- Zero residual energy is exactly zero raw tensor residual. -/
theorem tensorIrreducibleBranchingSpectrumResidualEnergy_eq_zero_iff
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    tensorIrreducibleBranchingSpectrumResidualEnergy B = 0 ↔
      tensorIrreducibleBranchingSpectrumResidual B = 0 := by
  unfold tensorIrreducibleBranchingSpectrumResidualEnergy
  rw [Int.natAbs_eq_zero]

/-- Nonzero raw tensor residual has positive residual energy. -/
theorem tensorIrreducibleBranchingSpectrumResidualEnergy_pos_of_nonzero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hnonzero : tensorIrreducibleBranchingSpectrumResidual B ≠ 0) :
    0 < tensorIrreducibleBranchingSpectrumResidualEnergy B := by
  apply Nat.pos_of_ne_zero
  intro henergy
  exact hnonzero
    ((tensorIrreducibleBranchingSpectrumResidualEnergy_eq_zero_iff B).mp
      henergy)

/-! ## Finite tensor spectra and permanent holonomy -/

/-- A finite tensor-irreducible SU(7) branching spectrum over one even fiber.

The cells store only tensor-irreducible atoms and their branch labels.  The
weight function is representation multiplicity / incidence weight; zero weight
cells are inert, positive-weight cells are physically active. -/
structure SU7TensorIrreducibleBranchingSpectrum
    (C : SU7WeightTensorCoding) (n : ℕ) where
  cells : List (SU7TensorIrreducibleBranchingSpectrumCell C n)
  representationWeight :
    SU7TensorIrreducibleBranchingSpectrumCell C n -> ℕ

/-- A permanent tensor holonomy cell: active, nonzero residual, and with no
active lower-energy representative in the same finite spectrum. -/
structure SU7TensorIrreduciblePermanentHolonomyCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (S : SU7TensorIrreducibleBranchingSpectrum C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) : Prop where
  mem : B ∈ S.cells
  weight_positive : 0 < S.representationWeight B
  residual_nonzero : tensorIrreducibleBranchingSpectrumResidual B ≠ 0
  no_lower_active :
    ∀ next : SU7TensorIrreducibleBranchingSpectrumCell C n,
      next ∈ S.cells ->
        0 < S.representationWeight next ->
          ¬ tensorIrreducibleBranchingSpectrumResidualEnergy next <
            tensorIrreducibleBranchingSpectrumResidualEnergy B

/-- The tensor spectrum forbids permanent holonomy when no active nonzero
residual cell can be terminal. -/
def SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (S : SU7TensorIrreducibleBranchingSpectrum C n) : Prop :=
  ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
    ¬ SU7TensorIrreduciblePermanentHolonomyCell S B

/-- No permanent holonomy supplies an active lower-energy successor for every
active nonzero residual cell. -/
theorem tensorIrreducible_lowerEnergyCell_of_noPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7TensorIrreducibleBranchingSpectrum C n}
    (hforbid : SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy S)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hmem : B ∈ S.cells)
    (hwt : 0 < S.representationWeight B)
    (hnonzero : tensorIrreducibleBranchingSpectrumResidual B ≠ 0) :
    ∃ next : SU7TensorIrreducibleBranchingSpectrumCell C n,
      next ∈ S.cells ∧
        0 < S.representationWeight next ∧
          tensorIrreducibleBranchingSpectrumResidualEnergy next <
            tensorIrreducibleBranchingSpectrumResidualEnergy B := by
  by_contra hnone
  exact
    (hforbid B)
      { mem := hmem
        weight_positive := hwt
        residual_nonzero := hnonzero
        no_lower_active := by
          intro next hnext_mem hnext_wt hlt
          exact hnone ⟨next, hnext_mem, hnext_wt, hlt⟩ }

/-! ## Confinement rule and zero-cell extraction -/

/-- Tensor-irreducible spectrum confinement on one even fiber.

This is the local finite-spectrum producer.  It does not store a zero cell:
it stores a start cell plus the no-permanent-holonomy law, from which the zero
cell is computed by descent. -/
structure SU7TensorIrreducibleSpectrumConfinementRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7TensorIrreducibleBranchingSpectrum C n
  startCell : SU7TensorIrreducibleBranchingSpectrumCell C n
  start_mem : startCell ∈ spectrum.cells
  start_weight_positive : 0 < spectrum.representationWeight startCell
  forbids_permanent_holonomy :
    SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy spectrum

/-- A tensor-irreducible confinement rule generates a positive-weight
zero-residual cell. -/
theorem exists_zeroCell_of_tensorIrreducibleSpectrumConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7TensorIrreducibleSpectrumConfinementRule C n) :
    ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
      Z ∈ R.spectrum.cells ∧
        0 < R.spectrum.representationWeight Z ∧
          tensorIrreducibleBranchingSpectrumResidual Z = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
      B ∈ R.spectrum.cells ->
        0 < R.spectrum.representationWeight B ->
          tensorIrreducibleBranchingSpectrumResidualEnergy B = e ->
            ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
              Z ∈ R.spectrum.cells ∧
                0 < R.spectrum.representationWeight Z ∧
                  tensorIrreducibleBranchingSpectrumResidual Z = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih B hmem hwt henergy
    by_cases hzero : tensorIrreducibleBranchingSpectrumResidual B = 0
    · exact ⟨B, hmem, hwt, hzero⟩
    · rcases
        tensorIrreducible_lowerEnergyCell_of_noPermanentHolonomy
          R.forbids_permanent_holonomy B hmem hwt hzero with
        ⟨next, hnext_mem, hnext_wt, hnext_lt⟩
      exact ih (tensorIrreducibleBranchingSpectrumResidualEnergy next)
        (by simpa [henergy] using hnext_lt)
        next hnext_mem hnext_wt rfl
  have hstart :
      motive
        (tensorIrreducibleBranchingSpectrumResidualEnergy R.startCell) :=
    Nat.strong_induction_on
      (tensorIrreducibleBranchingSpectrumResidualEnergy R.startCell) hstep
  exact hstart R.startCell R.start_mem R.start_weight_positive rfl

/-- A tensor-irreducible confinement rule computes a trace-zero prime-edge
loop through P906's non-storing tensor projection. -/
def traceZeroPrimeEdgeLoop_of_tensorIrreducibleSpectrumConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7TensorIrreducibleSpectrumConfinementRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  let Z := Classical.choose
    (exists_zeroCell_of_tensorIrreducibleSpectrumConfinementRule R)
  let hZ := Classical.choose_spec
    (exists_zeroCell_of_tensorIrreducibleSpectrumConfinementRule R)
  traceZeroPrimeEdgeLoop_of_tensorIrreducibleCell Z hZ.2.2

/-! ## Fiberwise confinement and Goldbach readout -/

/-- Every even fiber carries a tensor-irreducible finite-spectrum confinement
rule. -/
def SU7TensorIrreducibleSpectrumConfinementRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7TensorIrreducibleSpectrumConfinementRule C n)

/-- Fiberwise tensor-irreducible confinement computes trace-zero prime-edge
loops on every even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_tensorIrreducibleSpectrumConfinement
    {C : SU7WeightTensorCoding}
    (H : SU7TensorIrreducibleSpectrumConfinementRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact
    traceZeroPrimeEdgeLoop_of_tensorIrreducibleSpectrumConfinementRule
      (Classical.choice (H n hn))

/-- A trace-zero prime-edge loop is exactly an additive Goldbach pair on its
even fiber. -/
theorem hasPrimeAdditiveDecomposition_of_traceZeroPrimeEdgeLoop
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    HasPrimeAdditiveDecomposition (2 * n) := by
  refine ⟨Z.leftPrime, Z.rightPrime, ?_⟩
  exact
    (primeEdgeColorLoop_trace_zero_iff n Z.leftPrime Z.rightPrime).mp
      Z.trace_zero

/-- Trace-zero prime-edge loops on every even fiber give ordinary even
Goldbach. -/
theorem evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (H : ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n) :
    EvenGoldbachStatement := by
  intro n hn
  exact hasPrimeAdditiveDecomposition_of_traceZeroPrimeEdgeLoop (H n hn)

/-- Tensor-irreducible spectrum confinement on every even fiber gives ordinary
even Goldbach, without storing primes or a Goldbach pair in the branch cells. -/
theorem evenGoldbach_of_tensorIrreducibleSpectrumConfinement
    {C : SU7WeightTensorCoding}
    (H : SU7TensorIrreducibleSpectrumConfinementRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_tensorIrreducibleSpectrumConfinement
      H)

/-! ## Certificate -/

/-- P907 certificate: tensor-irreducible finite-spectrum confinement computes
zero residual cells, then P906 projects them to prime-edge trace-zero loops. -/
structure SU7TensorIrreducibleSpectrumConfinementProducerCertificate where
  residual_energy_zero_iff :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7TensorIrreducibleBranchingSpectrumCell C n),
      tensorIrreducibleBranchingSpectrumResidualEnergy B = 0 ↔
        tensorIrreducibleBranchingSpectrumResidual B = 0
  no_permanent_holonomy_to_lower_energy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7TensorIrreducibleBranchingSpectrum C n},
      SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy S ->
        ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
          B ∈ S.cells ->
            0 < S.representationWeight B ->
              tensorIrreducibleBranchingSpectrumResidual B ≠ 0 ->
                ∃ next : SU7TensorIrreducibleBranchingSpectrumCell C n,
                  next ∈ S.cells ∧
                    0 < S.representationWeight next ∧
                      tensorIrreducibleBranchingSpectrumResidualEnergy next <
                        tensorIrreducibleBranchingSpectrumResidualEnergy B
  confinement_to_zero_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      (R : SU7TensorIrreducibleSpectrumConfinementRule C n) ->
        ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
          Z ∈ R.spectrum.cells ∧
            0 < R.spectrum.representationWeight Z ∧
              tensorIrreducibleBranchingSpectrumResidual Z = 0
  confinement_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7TensorIrreducibleSpectrumConfinementRule C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding},
      SU7TensorIrreducibleSpectrumConfinementRuleEveryEvenFiber C ->
        ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7TensorIrreducibleSpectrumConfinementRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P907 producer certificate. -/
def su7TensorIrreducibleSpectrumConfinementProducerCertificate :
    SU7TensorIrreducibleSpectrumConfinementProducerCertificate where
  residual_energy_zero_iff :=
    tensorIrreducibleBranchingSpectrumResidualEnergy_eq_zero_iff
  no_permanent_holonomy_to_lower_energy :=
    tensorIrreducible_lowerEnergyCell_of_noPermanentHolonomy
  confinement_to_zero_cell := by
    intro C n R
    exact exists_zeroCell_of_tensorIrreducibleSpectrumConfinementRule R
  confinement_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_tensorIrreducibleSpectrumConfinementRule
  every_fiber_to_trace_zero :=
    traceZeroPrimeEdgeLoopEveryEvenFiber_of_tensorIrreducibleSpectrumConfinement
  every_fiber_to_goldbach :=
    evenGoldbach_of_tensorIrreducibleSpectrumConfinement


end
end StandardModelConstraint
end SaturationMonoid
