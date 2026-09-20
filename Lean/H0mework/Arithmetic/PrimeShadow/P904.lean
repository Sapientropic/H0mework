import H0mework.Arithmetic.PrimeShadow.P903

/-!
# Proposition 904: multiplicative atomicity produces prime SU(7) atom codes

P903 proves the raw atom-code projection chain assuming the representation
producer throat

```text
SU7IrreducibleCodePrimeProducerLaw
```

This file pushes that throat one layer lower.  Instead of assuming primality,
the new producer law says an irreducible SU(7) weight code is multiplicatively
atomic: it is at least `2`, and every factorization has a unit factor.  Lean
then proves that this non-prime-storing atomicity is exactly the arithmetic
content needed to produce prime atom codes.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Multiplicative atomicity without `Nat.Prime` in the definition -/

/-- A natural code is multiplicatively atomic when it is nontrivial and has no
non-unit factorization.  The definition intentionally does not mention
`Nat.Prime`. -/
def NatMultiplicativelyAtomic (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ a b : ℕ, n = a * b -> a = 1 ∨ b = 1

/-- Multiplicative atomicity implies `Nat.Prime`. -/
theorem Nat.Prime.of_multiplicativelyAtomic
    {n : ℕ} (h : NatMultiplicativelyAtomic n) :
    Nat.Prime n := by
  rw [Nat.prime_def_lt]
  constructor
  · exact h.1
  · intro m hm hdvd
    rcases hdvd with ⟨k, hk⟩
    rcases h.2 m k hk with hm1 | hk1
    · exact hm1
    · subst k
      omega

/-- Prime naturals are multiplicatively atomic. -/
theorem Nat.Prime.multiplicativelyAtomic
    {n : ℕ} (hp : Nat.Prime n) :
    NatMultiplicativelyAtomic n := by
  constructor
  · exact hp.two_le
  · intro a b hmul
    have hdiv : a ∣ n := ⟨b, hmul⟩
    rcases hp.eq_one_or_self_of_dvd a hdiv with ha1 | han
    · exact Or.inl ha1
    · right
      have hn0 : n ≠ 0 := Nat.ne_of_gt hp.pos
      have hmul' : n * b = n := by
        simpa [han] using hmul.symm
      exact (Nat.mul_eq_left hn0).mp hmul'

/-- Multiplicative atomicity is equivalent to primality, but its forward use
lets producer statements avoid storing `Nat.Prime` directly. -/
theorem natMultiplicativelyAtomic_iff_prime
    {n : ℕ} :
    NatMultiplicativelyAtomic n ↔ Nat.Prime n := by
  constructor
  · exact Nat.Prime.of_multiplicativelyAtomic
  · exact Nat.Prime.multiplicativelyAtomic

/-! ## SU(7) irreducible-code atomic producer -/

/-- The lower SU(7) representation-code producer law: irreducible weights have
multiplicatively atomic raw codes.  This law contains no `Nat.Prime` field. -/
def SU7IrreducibleCodeAtomicProducerLaw : Prop :=
  ∀ w : SU7WeightLattice,
    IsIrreducibleRepresentation w ->
      NatMultiplicativelyAtomic w.code

/-- Atomic irreducible-code production gives the prime-code producer throat
used by P903. -/
theorem SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw
    (H : SU7IrreducibleCodeAtomicProducerLaw) :
    SU7IrreducibleCodePrimeProducerLaw := by
  intro w hirr
  exact Nat.Prime.of_multiplicativelyAtomic (H w hirr)

/-- Conversely, the prime-code producer gives multiplicative atomicity. -/
theorem atomicProducerLaw_of_SU7IrreducibleCodePrimeProducerLaw
    (H : SU7IrreducibleCodePrimeProducerLaw) :
    SU7IrreducibleCodeAtomicProducerLaw := by
  intro w hirr
  exact Nat.Prime.multiplicativelyAtomic (H w hirr)

/-- The atomic producer law is exactly equivalent to the P878 prime producer,
while being stated without `Nat.Prime` in its own definition. -/
theorem SU7IrreducibleCodeAtomicProducerLaw_iff_primeProducerLaw :
    SU7IrreducibleCodeAtomicProducerLaw ↔
      SU7IrreducibleCodePrimeProducerLaw := by
  constructor
  · exact SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw
  · exact atomicProducerLaw_of_SU7IrreducibleCodePrimeProducerLaw

/-- Atomic production gives the P873 atom-code prime projection law. -/
theorem SU7AtomCodePrimeProjectionLaw_of_atomicProducerLaw
    (H : SU7IrreducibleCodeAtomicProducerLaw) :
    SU7AtomCodePrimeProjectionLaw :=
  SU7AtomCodePrimeProjectionLaw_of_irreducibleCodePrimeProducerLaw
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H)

/-! ## Raw P903 projection driven by atomicity -/

/-- Raw physical cell projection driven by atomic irreducible-code production.
-/
def rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell_atomic
    (H : SU7IrreducibleCodeAtomicProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    SU7PrimeEdgeBranchCell n :=
  rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H) C

/-- Atomic raw projection preserves raw physical residual. -/
theorem branchWeightResidual_rawPhysicalProjection_atomic_eq
    (H : SU7IrreducibleCodeAtomicProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    branchWeightResidual
        (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell_atomic H C) =
      rawAtomCodePhysicalBranchingSpectrumResidual C :=
  branchWeightResidual_rawPhysicalProjection_eq
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H) C

/-- Zero raw physical residual computes a trace-zero prime-edge loop from
atomic irreducible-code production. -/
def traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual_atomic
    (H : SU7IrreducibleCodeAtomicProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : rawAtomCodePhysicalBranchingSpectrumResidual C = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H) C hzero

/-- Raw branching-decomposition projection driven by atomicity. -/
def rawPrimeEdgeBranchCell_of_branchingDecompositionCell_atomic
    (H : SU7IrreducibleCodeAtomicProducerLaw)
    {n : ℕ} (C : SU7BranchingDecompositionCell n) :
    SU7PrimeEdgeBranchCell n :=
  rawPrimeEdgeBranchCell_of_branchingDecompositionCell
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H) C

/-- Atomic raw branching-decomposition projection preserves raw residual. -/
theorem branchWeightResidual_rawBranchingDecompositionProjection_atomic_eq
    (H : SU7IrreducibleCodeAtomicProducerLaw)
    {n : ℕ} (C : SU7BranchingDecompositionCell n) :
    branchWeightResidual
        (rawPrimeEdgeBranchCell_of_branchingDecompositionCell_atomic H C) =
      rawAtomCodeBranchingDecompositionResidual C :=
  branchWeightResidual_rawBranchingDecompositionProjection_eq
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H) C

/-- Zero raw branching-decomposition residual computes a trace-zero prime-edge
loop from atomic irreducible-code production. -/
def traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual_atomic
    (H : SU7IrreducibleCodeAtomicProducerLaw)
    {n : ℕ} (C : SU7BranchingDecompositionCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual C = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual
    (SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw H) C hzero

/-! ## Certificate -/

/-- P904 certificate: the prime-code throat is produced by a lower
multiplicative-atomicity law, whose statement itself contains no prime-valued
field. -/
structure SU7AtomicCodeProducerCertificate where
  nat_atomic_iff_prime :
    ∀ n : ℕ, NatMultiplicativelyAtomic n ↔ Nat.Prime n
  atomic_to_prime_producer :
    SU7IrreducibleCodeAtomicProducerLaw ->
      SU7IrreducibleCodePrimeProducerLaw
  prime_to_atomic_producer :
    SU7IrreducibleCodePrimeProducerLaw ->
      SU7IrreducibleCodeAtomicProducerLaw
  atomic_iff_prime_producer :
    SU7IrreducibleCodeAtomicProducerLaw ↔
      SU7IrreducibleCodePrimeProducerLaw
  atomic_to_atom_projection :
    SU7IrreducibleCodeAtomicProducerLaw ->
      SU7AtomCodePrimeProjectionLaw
  atomic_raw_physical_residual_to_trace_zero :
    ∀ (_H : SU7IrreducibleCodeAtomicProducerLaw)
      {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      rawAtomCodePhysicalBranchingSpectrumResidual C = 0 ->
        TraceZeroPrimeEdgeLoop n
  atomic_raw_decomposition_residual_to_trace_zero :
    ∀ (_H : SU7IrreducibleCodeAtomicProducerLaw)
      {n : ℕ} (C : SU7BranchingDecompositionCell n),
      rawAtomCodeBranchingDecompositionResidual C = 0 ->
        TraceZeroPrimeEdgeLoop n

def su7AtomicCodeProducerCertificate :
    SU7AtomicCodeProducerCertificate where
  nat_atomic_iff_prime := by
    intro n
    exact natMultiplicativelyAtomic_iff_prime
  atomic_to_prime_producer :=
    SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw
  prime_to_atomic_producer :=
    atomicProducerLaw_of_SU7IrreducibleCodePrimeProducerLaw
  atomic_iff_prime_producer :=
    SU7IrreducibleCodeAtomicProducerLaw_iff_primeProducerLaw
  atomic_to_atom_projection :=
    SU7AtomCodePrimeProjectionLaw_of_atomicProducerLaw
  atomic_raw_physical_residual_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual_atomic
  atomic_raw_decomposition_residual_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual_atomic


end
end StandardModelConstraint
end SaturationMonoid
