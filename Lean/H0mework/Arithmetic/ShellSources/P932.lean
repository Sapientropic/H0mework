import H0mework.Physics.BranchSources.P909
import H0mework.Physics.AlphaSpectrum.P931

/-!
# Proposition 932: no-prime SU(7) branch cells project to prime edges

P873 named the physical throat:

```lean
SU7Atom
SU7PhysicalBranchCell
physicalResidual
```

and P906/P909 proved that tensor-irreducible cells generate prime-edge
readouts locally.  This file pins the exact interface requested by the hard
route: a SU(7) branching-spectrum cell whose data contain no `Nat.Prime`,
no `PrimeExponent`, and no Goldbach pair.

The only arithmetic projection is the theorem:

```lean
SU7TensorIrreducible C weight -> Nat.Prime weight.code
```

inherited from P905.  Thus primality is produced by the representation/tensor
irreducibility proof at the projection boundary; it is not stored in the cell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## No-prime branch atoms and cells -/

/-- A SU(7) branch atom below prime-edge coding.

The field `tensor_irreducible` is representation/tensor data.  The structure
does not store a `Nat.Prime` proof for `weight.code`. -/
structure SU7NoPrimeBranchingAtom
    (C : SU7WeightTensorCoding) where
  weight : SU7WeightLattice
  tensor_irreducible : SU7TensorIrreducible C weight
  sector : ColorWeakHyperchargeSector

/-- Forget a no-prime branch atom to P906's tensor-irreducible atom shape. -/
def SU7NoPrimeBranchingAtom.toTensorIrreducibleAtom
    {C : SU7WeightTensorCoding}
    (a : SU7NoPrimeBranchingAtom C) :
    SU7TensorIrreducibleAtom C where
  weight := a.weight
  tensor_irreducible := a.tensor_irreducible
  sector := a.sector

/-- Forget a no-prime branch atom to the P873 physical SU(7) atom. -/
def SU7NoPrimeBranchingAtom.toSU7Atom
    {C : SU7WeightTensorCoding}
    (a : SU7NoPrimeBranchingAtom C) :
    SU7Atom :=
  a.toTensorIrreducibleAtom.toSU7Atom

@[simp] theorem noPrimeBranchingAtom_toSU7Atom_atomCode
    {C : SU7WeightTensorCoding}
    (a : SU7NoPrimeBranchingAtom C) :
    atomCode a.toSU7Atom = a.weight.code := rfl

/-- Projection theorem: no-prime branch atoms code to primes because their
weights are tensor-irreducible, not because prime data are stored in the atom.
-/
theorem noPrimeBranchingAtom_atomCode_prime
    {C : SU7WeightTensorCoding}
    (a : SU7NoPrimeBranchingAtom C) :
    Nat.Prime (atomCode a.toSU7Atom) := by
  simpa [SU7NoPrimeBranchingAtom.toSU7Atom,
    SU7NoPrimeBranchingAtom.toTensorIrreducibleAtom] using
    (tensorIrreducibleAtom_atomCode_prime
      a.toTensorIrreducibleAtom)

/-- A SU(7) branching-spectrum cell below prime-edge coding.

Only branch and tensor-irreducible endpoint atoms are stored.  There is no
prime pair field and no trace-zero witness field. -/
structure SU7NoPrimeBranchingSpectrumCell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  branch : SU3FlagSchubertCell
  leftAtom : SU7NoPrimeBranchingAtom C
  rightAtom : SU7NoPrimeBranchingAtom C

/-- Forget a no-prime branch cell to P906's tensor-irreducible branch cell. -/
def SU7NoPrimeBranchingSpectrumCell.toTensorIrreducibleCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    SU7TensorIrreducibleBranchingSpectrumCell C n where
  branch := B.branch
  leftAtom := B.leftAtom.toTensorIrreducibleAtom
  rightAtom := B.rightAtom.toTensorIrreducibleAtom

/-- Forget a no-prime branch cell to the physical P873 branch cell. -/
def physicalBranchCell_of_noPrimeBranchingCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    SU7PhysicalBranchCell n :=
  physicalBranchCell_of_tensorIrreducibleCell
    B.toTensorIrreducibleCell

/-- Raw physical residual of a no-prime branch cell. -/
def noPrimeBranchingResidual
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) : ℤ :=
  physicalResidual (physicalBranchCell_of_noPrimeBranchingCell B)

/-- The no-prime residual is the tensor-irreducible residual after forgetting.
-/
theorem noPrimeBranchingResidual_eq_tensorResidual
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    noPrimeBranchingResidual B =
      tensorIrreducibleBranchingSpectrumResidual
        B.toTensorIrreducibleCell := by
  unfold noPrimeBranchingResidual
  simpa [physicalBranchCell_of_noPrimeBranchingCell] using
    physicalResidual_tensorIrreducibleCell_eq
      B.toTensorIrreducibleCell

/-! ## Projection to prime-edge readouts -/

/-- Prime-edge projection computed from tensor irreducibility.

The returned `SU7PrimeEdgeBranchCell` contains prime subtypes, but those prime
proofs are produced here from `tensor_irreducible`; they are not stored in the
source cell. -/
def primeEdgeBranchCell_of_noPrimeBranchingCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    SU7PrimeEdgeBranchCell n :=
  primeEdgeBranchCell_of_tensorIrreducibleCell
    B.toTensorIrreducibleCell

@[simp] theorem primeEdgeBranchCell_of_noPrimeBranchingCell_left
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    (primeEdgeBranchCell_of_noPrimeBranchingCell B).leftPrime.1 =
      atomCode B.leftAtom.toSU7Atom := rfl

@[simp] theorem primeEdgeBranchCell_of_noPrimeBranchingCell_right
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    (primeEdgeBranchCell_of_noPrimeBranchingCell B).rightPrime.1 =
      atomCode B.rightAtom.toSU7Atom := rfl

/-- The generated prime-edge projection preserves the residual. -/
theorem branchWeightResidual_noPrimeProjection_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n) :
    branchWeightResidual (primeEdgeBranchCell_of_noPrimeBranchingCell B) =
      noPrimeBranchingResidual B := by
  rw [noPrimeBranchingResidual_eq_tensorResidual B]
  exact
    branchWeightResidual_tensorIrreducibleProjection_eq
      B.toTensorIrreducibleCell

/-- Zero residual in a no-prime branch cell computes arithmetic balance only
after applying `atomCode`. -/
theorem noPrimeBranchingResidual_zero_to_sum
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hzero : noPrimeBranchingResidual B = 0) :
    atomCode B.leftAtom.toSU7Atom +
        atomCode B.rightAtom.toSU7Atom =
      2 * n := by
  exact
    physicalResidual_zero_to_sum
      (physicalBranchCell_of_noPrimeBranchingCell B)
      hzero

/-- A no-prime residual-zero branch cell computes a trace-zero prime-edge loop.
-/
def traceZeroPrimeEdgeLoop_of_noPrimeBranchingCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hzero : noPrimeBranchingResidual B = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_tensorIrreducibleCell
    B.toTensorIrreducibleCell
    (by
      simpa [noPrimeBranchingResidual_eq_tensorResidual B] using hzero)

/-! ## No-prime confinement producer -/

/-- A confinement producer stated directly over no-prime branch cells.

The dynamics produces zero residual branch-spectrum cells in each even fiber;
it does not store prime edges. -/
structure SU7NoPrimeBranchingConfinementDynamics
    (C : SU7WeightTensorCoding) where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  zeroCell :
    ∀ n : ℕ, 2 ≤ n -> SU7NoPrimeBranchingSpectrumCell C n
  zeroCell_residual_zero :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      noPrimeBranchingResidual (zeroCell n hn) = 0

/-- Fiberwise no-prime confinement computes trace-zero prime-edge loops only
through the final projection theorem. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_noPrimeConfinement
    {C : SU7WeightTensorCoding}
    (D : SU7NoPrimeBranchingConfinementDynamics C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact
    traceZeroPrimeEdgeLoop_of_noPrimeBranchingCell
      (D.zeroCell n hn)
      (D.zeroCell_residual_zero n hn)

/-- No-prime confinement gives ordinary even Goldbach only after the generated
prime-edge projection has been applied fiberwise. -/
theorem evenGoldbach_of_noPrimeConfinement
    {C : SU7WeightTensorCoding}
    (D : SU7NoPrimeBranchingConfinementDynamics C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_noPrimeConfinement D)

/-! ## Certificate -/

/-- P932 certificate: the SU(7) branch-spectrum producer stores no primes; its
prime-edge readout is generated at projection time from tensor irreducibility.
-/
structure SU7NoPrimeBranchingSpectrumProjectionCertificate where
  atom_to_physical :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeBranchingAtom C -> SU7Atom
  atom_projection_prime :
    ∀ {C : SU7WeightTensorCoding}
      (a : SU7NoPrimeBranchingAtom C),
      Nat.Prime (atomCode a.toSU7Atom)
  cell_to_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7NoPrimeBranchingSpectrumCell C n ->
        SU7PhysicalBranchCell n
  cell_to_prime_edge :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7NoPrimeBranchingSpectrumCell C n ->
        SU7PrimeEdgeBranchCell n
  projection_preserves_residual :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      branchWeightResidual (primeEdgeBranchCell_of_noPrimeBranchingCell B) =
        noPrimeBranchingResidual B
  zero_to_sum :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      noPrimeBranchingResidual B = 0 ->
        atomCode B.leftAtom.toSU7Atom +
            atomCode B.rightAtom.toSU7Atom =
          2 * n
  zero_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      noPrimeBranchingResidual B = 0 -> TraceZeroPrimeEdgeLoop n
  no_prime_confinement_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeBranchingConfinementDynamics C ->
        EvenGoldbachStatement

/-- Canonical no-prime branch-spectrum projection certificate. -/
def su7NoPrimeBranchingSpectrumProjectionCertificate :
    SU7NoPrimeBranchingSpectrumProjectionCertificate where
  atom_to_physical := SU7NoPrimeBranchingAtom.toSU7Atom
  atom_projection_prime := noPrimeBranchingAtom_atomCode_prime
  cell_to_physical := physicalBranchCell_of_noPrimeBranchingCell
  cell_to_prime_edge := primeEdgeBranchCell_of_noPrimeBranchingCell
  projection_preserves_residual := branchWeightResidual_noPrimeProjection_eq
  zero_to_sum := noPrimeBranchingResidual_zero_to_sum
  zero_to_trace_zero := traceZeroPrimeEdgeLoop_of_noPrimeBranchingCell
  no_prime_confinement_to_goldbach := evenGoldbach_of_noPrimeConfinement


end
end StandardModelConstraint
end SaturationMonoid
