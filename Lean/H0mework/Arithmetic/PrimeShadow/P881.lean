import H0mework.Arithmetic.PrimeShadow.P880

/-!
# Proposition 881: prime-coded branching-spectrum projection

P870 pushed SU(7) branching-spectrum cells below `PrimeExponent`, but it still
needed a per-cell `SU7SpectrumCellPrimeProjection` proof.

P879 supplied a canonical prime-coded readout for physical SU(7) atoms.  This
file applies that readout to branching-spectrum cells:

* a spectrum cell stores only a Schubert branch plus two physical SU(7) atoms;
* its prime-edge projection is computed by `Nat.nth Nat.Prime`;
* primality is produced by P879, not stored in the cell and not passed as an
  external projection law;
* zero prime-coded spectrum residual projects to a trace-neutral prime-edge
  branch cell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Prime-coded branching-spectrum cells -/

/-- A SU(7) branching-spectrum cell that stores no prime edge.

The two edges are physical SU(7) atoms.  Prime natural labels are computed only
by the canonical P879 readout. -/
structure SU7PrimeCodedBranchingSpectrumCell (n : ℕ) where
  branch : SU3FlagSchubertCell
  leftAtom : SU7Atom
  rightAtom : SU7Atom

namespace SU7PrimeCodedBranchingSpectrumCell

/-- Prime-coded left edge generated from the physical atom. -/
def leftPrime {n : ℕ}
    (C : SU7PrimeCodedBranchingSpectrumCell n) : PrimeExponent :=
  ⟨su7PrimeCodedAtomCode C.leftAtom,
    su7PrimeCodedAtomCode_prime C.leftAtom⟩

/-- Prime-coded right edge generated from the physical atom. -/
def rightPrime {n : ℕ}
    (C : SU7PrimeCodedBranchingSpectrumCell n) : PrimeExponent :=
  ⟨su7PrimeCodedAtomCode C.rightAtom,
    su7PrimeCodedAtomCode_prime C.rightAtom⟩

/-- Prime-coded branch weight. -/
def primeCodedWeight {n : ℕ}
    (C : SU7PrimeCodedBranchingSpectrumCell n) : ℕ :=
  su7PrimeCodedAtomCode C.leftAtom +
    su7PrimeCodedAtomCode C.rightAtom

/-- Prime-coded integer residual against the even fiber target `2n`. -/
def primeCodedResidual {n : ℕ}
    (C : SU7PrimeCodedBranchingSpectrumCell n) : ℤ :=
  (C.primeCodedWeight : ℤ) - ((2 * n : ℕ) : ℤ)

end SU7PrimeCodedBranchingSpectrumCell

/-! ## Projection to prime-edge branch cells -/

/-- THEOREM 1: a prime-coded SU(7) spectrum cell computes a prime-edge branch
cell without any stored primality field or external projection law. -/
def primeEdgeBranchCell_of_primeCodedSpectrumCell
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    SU7PrimeEdgeBranchCell n where
  branch := C.branch
  leftPrime := C.leftPrime
  rightPrime := C.rightPrime

@[simp] theorem primeEdgeBranchCell_of_primeCodedSpectrumCell_left
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    (primeEdgeBranchCell_of_primeCodedSpectrumCell C).leftPrime.1 =
      su7PrimeCodedAtomCode C.leftAtom := rfl

@[simp] theorem primeEdgeBranchCell_of_primeCodedSpectrumCell_right
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    (primeEdgeBranchCell_of_primeCodedSpectrumCell C).rightPrime.1 =
      su7PrimeCodedAtomCode C.rightAtom := rfl

/-- THEOREM 2: the prime-edge branch weight is exactly the generated
prime-coded spectrum weight. -/
theorem primeEdgeBranchCell_of_primeCodedSpectrumCell_weight
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    (primeEdgeBranchCell_of_primeCodedSpectrumCell C).branchWeight =
      C.primeCodedWeight := rfl

/-- THEOREM 3: prime-edge projection preserves the prime-coded residual. -/
theorem branchWeightResidual_primeCodedProjection_eq
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    branchWeightResidual
        (primeEdgeBranchCell_of_primeCodedSpectrumCell C) =
      C.primeCodedResidual := by
  rfl

/-- THEOREM 4: zero prime-coded spectrum residual gives a trace-neutral
prime-edge branch cell. -/
theorem traceNeutral_of_primeCodedSpectrumResidual_zero
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n)
    (hzero : C.primeCodedResidual = 0) :
    (primeEdgeBranchCell_of_primeCodedSpectrumCell C).traceNeutral := by
  exact
    (branchWeightResidual_eq_zero_iff_traceNeutral
      (primeEdgeBranchCell_of_primeCodedSpectrumCell C)).mp
      (by simpa [branchWeightResidual_primeCodedProjection_eq C] using hzero)

/-- THEOREM 5: zero prime-coded spectrum residual computes a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_primeCodedSpectrumResidual
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n)
    (hzero : C.primeCodedResidual = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    (primeEdgeBranchCell_of_primeCodedSpectrumCell C)
    (traceNeutral_of_primeCodedSpectrumResidual_zero C hzero)

/-! ## Projection to physical branch cells -/

/-- The physical branch cell carried by a prime-coded spectrum cell.  This
still stores no prime edge; it stores only the physical atoms and gauge loop. -/
def physicalBranchCell_of_primeCodedSpectrumCell
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    SU7PhysicalBranchCell n where
  leftAtom := C.leftAtom
  rightAtom := C.rightAtom
  colorLoop :=
    { fiber := n
      leftAtom := C.leftAtom
      rightAtom := C.rightAtom }
  allowed := by trivial
  loop_fiber := rfl
  loop_left := rfl
  loop_right := rfl

/-- THEOREM 6: the P879 physical residual of the projected physical cell is
the same prime-coded residual computed on the spectrum cell. -/
theorem primeCodedPhysicalResidual_of_primeCodedSpectrumCell_eq
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    primeCodedPhysicalResidual
        (physicalBranchCell_of_primeCodedSpectrumCell C) =
      C.primeCodedResidual := by
  rfl

/-! ## Fiberwise prime-coded spectrum generators -/

/-- A finite prime-coded spectrum family.  It stores no prime edges. -/
structure SU7PrimeCodedBranchingSpectrumFamily (n : ℕ) where
  spectrumCells : List (SU7PrimeCodedBranchingSpectrumCell n)
  representationWeight : SU7PrimeCodedBranchingSpectrumCell n -> ℕ

/-- A raw prime-coded spectrum generator over one even fiber.

The support cell is still below prime-edge data; the zero residual is checked
through the canonical prime-coded readout. -/
structure SU7PrimeCodedBranchingSpectrumGenerator (n : ℕ) where
  family : SU7PrimeCodedBranchingSpectrumFamily n
  supportCell : SU7PrimeCodedBranchingSpectrumCell n
  support_mem : supportCell ∈ family.spectrumCells
  support_weight_positive : 0 < family.representationWeight supportCell
  support_primeCodedResidual_zero :
    supportCell.primeCodedResidual = 0

/-- THEOREM 7: a prime-coded spectrum generator computes a physical branch
cell with zero P879 residual. -/
theorem primeCodedPhysicalResidual_zero_of_spectrumGenerator
    {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n) :
    primeCodedPhysicalResidual
        (physicalBranchCell_of_primeCodedSpectrumCell G.supportCell) = 0 := by
  simpa [primeCodedPhysicalResidual_of_primeCodedSpectrumCell_eq]
    using G.support_primeCodedResidual_zero

/-- Every even fiber carries a prime-coded spectrum generator. -/
def SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7PrimeCodedBranchingSpectrumGenerator n)

/-- THEOREM 8: fiberwise prime-coded spectrum generators produce P879's
prime-coded well-founded zero-cell readout directly, without an external
atom-code prime law. -/
theorem evenGoldbach_of_primeCodedSpectrumGenerator
    (H : SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber) :
    EvenGoldbachStatement := by
  intro n hn
  rcases H n hn with ⟨G⟩
  let cell := physicalBranchCell_of_primeCodedSpectrumCell G.supportCell
  refine
    ⟨⟨su7PrimeCodedAtomCode cell.leftAtom,
        su7PrimeCodedAtomCode_prime cell.leftAtom⟩,
      ⟨su7PrimeCodedAtomCode cell.rightAtom,
        su7PrimeCodedAtomCode_prime cell.rightAtom⟩,
      ?_⟩
  exact
    (primeCodedPhysicalResidual_zero_to_sum cell
      (primeCodedPhysicalResidual_zero_of_spectrumGenerator G)).symm

/-! ## Certificate -/

/-- P881 certificate: branching-spectrum cells can stay below `PrimeExponent`;
prime-edge projection is produced by the canonical prime-coded atom readout. -/
structure SU7PrimeCodedBranchingSpectrumProjectionCertificate where
  project_cell :
    ∀ {n : ℕ}, SU7PrimeCodedBranchingSpectrumCell n ->
      SU7PrimeEdgeBranchCell n
  projection_preserves_residual :
    ∀ {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n),
      branchWeightResidual
          (primeEdgeBranchCell_of_primeCodedSpectrumCell C) =
        C.primeCodedResidual
  residual_zero_to_trace_neutral :
    ∀ {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n),
      C.primeCodedResidual = 0 ->
        (primeEdgeBranchCell_of_primeCodedSpectrumCell C).traceNeutral
  residual_zero_to_physical_zero :
    ∀ {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n),
      primeCodedPhysicalResidual
          (physicalBranchCell_of_primeCodedSpectrumCell G.supportCell) = 0
  every_fiber_to_goldbach :
    SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber ->
      EvenGoldbachStatement

def su7PrimeCodedBranchingSpectrumProjectionCertificate :
    SU7PrimeCodedBranchingSpectrumProjectionCertificate where
  project_cell := primeEdgeBranchCell_of_primeCodedSpectrumCell
  projection_preserves_residual :=
    branchWeightResidual_primeCodedProjection_eq
  residual_zero_to_trace_neutral :=
    traceNeutral_of_primeCodedSpectrumResidual_zero
  residual_zero_to_physical_zero :=
    primeCodedPhysicalResidual_zero_of_spectrumGenerator
  every_fiber_to_goldbach :=
    evenGoldbach_of_primeCodedSpectrumGenerator


end
end StandardModelConstraint
end SaturationMonoid
