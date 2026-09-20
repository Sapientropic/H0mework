import H0mework.Arithmetic.PrimeShadow.P869

/-!
# Proposition 870: SU(7) branching-spectrum cells before prime-edge projection

P869 proved that P868's current `SU7RepresentationBranchWeightGenerator` is
exactly Goldbach-strength, because every branch cell already stores

`leftPrime/rightPrime : PrimeExponent`.

This file defines the next lower object.  A SU(7) branching-spectrum cell stores
only:

* a Schubert branch cell;
* two raw natural representation weights.

It does not store primes.  A separate representation-spectrum projection law
proves that positive-weight spectrum cells project to prime exponents.  Only
after that law is applied do we build a `SU7PrimeEdgeBranchCell`.

Thus the prime-edge data becomes an output of the spectrum projection, not an
input hidden in the producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Raw SU(7) branching-spectrum cells -/

/-- A SU(7) branching-spectrum cell over the even fiber `2n`.

This is deliberately below `PrimeExponent`: the two edge labels are raw natural
representation weights, not prime subtypes. -/
structure SU7BranchingSpectrumCell (n : ℕ) where
  branch : SU3FlagSchubertCell
  leftWeight : ℕ
  rightWeight : ℕ
  deriving DecidableEq, Repr

namespace SU7BranchingSpectrumCell

/-- Raw branch weight before prime-edge projection. -/
def rawWeight {n : ℕ} (C : SU7BranchingSpectrumCell n) : ℕ :=
  C.leftWeight + C.rightWeight

/-- The target weight of the even fiber `2n`. -/
def evenFiberWeight (n : ℕ) : ℕ :=
  2 * n

/-- Raw integer residual before prime-edge projection. -/
def rawResidual {n : ℕ} (C : SU7BranchingSpectrumCell n) : ℤ :=
  (C.rawWeight : ℤ) - (evenFiberWeight n : ℤ)

end SU7BranchingSpectrumCell

/-! ## Projection from spectrum cells to prime-edge cells -/

/-- A proof that one raw spectrum cell projects to two prime exponents. -/
def SU7SpectrumCellPrimeProjection
    {n : ℕ} (C : SU7BranchingSpectrumCell n) : Prop :=
  Nat.Prime C.leftWeight ∧ Nat.Prime C.rightWeight

/-- THEOREM 1: once the SU(7) spectrum projection proves primality, a raw
spectrum cell produces a prime-edge branch cell. -/
def primeEdgeBranchCell_of_spectrumCell
    {n : ℕ} (C : SU7BranchingSpectrumCell n)
    (hC : SU7SpectrumCellPrimeProjection C) :
    SU7PrimeEdgeBranchCell n where
  branch := C.branch
  leftPrime := ⟨C.leftWeight, hC.1⟩
  rightPrime := ⟨C.rightWeight, hC.2⟩

/-- THEOREM 2: prime-edge projection preserves the left raw weight. -/
@[simp] theorem primeEdgeBranchCell_of_spectrumCell_left
    {n : ℕ} (C : SU7BranchingSpectrumCell n)
    (hC : SU7SpectrumCellPrimeProjection C) :
    (primeEdgeBranchCell_of_spectrumCell C hC).leftPrime.1 =
      C.leftWeight := rfl

/-- THEOREM 3: prime-edge projection preserves the right raw weight. -/
@[simp] theorem primeEdgeBranchCell_of_spectrumCell_right
    {n : ℕ} (C : SU7BranchingSpectrumCell n)
    (hC : SU7SpectrumCellPrimeProjection C) :
    (primeEdgeBranchCell_of_spectrumCell C hC).rightPrime.1 =
      C.rightWeight := rfl

/-- THEOREM 4: prime-edge projection preserves the raw branch residual. -/
theorem branchWeightResidual_projected_eq_rawResidual
    {n : ℕ} (C : SU7BranchingSpectrumCell n)
    (hC : SU7SpectrumCellPrimeProjection C) :
    branchWeightResidual (primeEdgeBranchCell_of_spectrumCell C hC) =
      C.rawResidual := by
  rfl

/-! ## Spectrum families and projection law -/

/-- A finite raw SU(7) branching-spectrum family over one even fiber. -/
structure SU7BranchingSpectrumFamily (n : ℕ) where
  spectrumCells : List (SU7BranchingSpectrumCell n)
  representationWeight : SU7BranchingSpectrumCell n -> ℕ

/-- A spectrum projection law: every positive-weight cell in the raw SU(7)
family projects to prime edges.  Primality is proved here, not stored in the
cell. -/
def SU7BranchingSpectrumPrimeProjectionLaw
    {n : ℕ} (F : SU7BranchingSpectrumFamily n) : Prop :=
  ∀ C : SU7BranchingSpectrumCell n,
    C ∈ F.spectrumCells ->
      0 < F.representationWeight C ->
        SU7SpectrumCellPrimeProjection C

/-- A raw SU(7) branching-spectrum generator over one even fiber.

The support cell is still raw: its zero residual is stated before any
prime-edge projection. -/
structure SU7BranchingSpectrumGenerator (n : ℕ) where
  family : SU7BranchingSpectrumFamily n
  primeProjectionLaw : SU7BranchingSpectrumPrimeProjectionLaw family
  supportCell : SU7BranchingSpectrumCell n
  support_mem : supportCell ∈ family.spectrumCells
  support_weight_positive : 0 < family.representationWeight supportCell
  support_rawResidual_zero : supportCell.rawResidual = 0

/-- THEOREM 5: the support cell of a raw spectrum generator projects to prime
edges. -/
theorem supportCell_primeProjection
    {n : ℕ} (G : SU7BranchingSpectrumGenerator n) :
    SU7SpectrumCellPrimeProjection G.supportCell :=
  G.primeProjectionLaw
    G.supportCell G.support_mem G.support_weight_positive

/-- THEOREM 6: a raw spectrum generator computes the P868 branch-weight
generator.  This is the first point where `PrimeExponent` appears, and it
appears as a theorem output of the spectrum projection law. -/
def branchWeightGenerator_of_spectrumGenerator
    {n : ℕ} (G : SU7BranchingSpectrumGenerator n) :
    SU7RepresentationBranchWeightGenerator n :=
  let hprime := supportCell_primeProjection G
  let B := primeEdgeBranchCell_of_spectrumCell G.supportCell hprime
  { branchFamily := { branchCells := [B] }
    representationWeight := fun _ => 1
    supportCell := B
    support_mem := by simp
    support_weight_positive := by simp
    support_residual_zero := by
      rw [branchWeightResidual_projected_eq_rawResidual]
      exact G.support_rawResidual_zero }

/-! ## Fiberwise spectrum generators give the old P868 throat -/

/-- Every even fiber carries a raw SU(7) branching-spectrum generator. -/
def SU7BranchingSpectrumGeneratorEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7BranchingSpectrumGenerator n)

/-- THEOREM 7: raw SU(7) branching-spectrum generators produce the P868
branch-weight generator on every even fiber. -/
theorem branchWeightGeneratorEveryEvenFiber_of_spectrumGenerator
    (H : SU7BranchingSpectrumGeneratorEveryEvenFiber) :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨G⟩
  exact ⟨branchWeightGenerator_of_spectrumGenerator G⟩

/-- THEOREM 8: raw SU(7) branching-spectrum generators produce the full
downstream no-gap / unit-bracket / Goldbach chain through P868/P869. -/
theorem evenGoldbach_of_spectrumGenerator
    (H : SU7BranchingSpectrumGeneratorEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_branchWeightGenerator
    (branchWeightGeneratorEveryEvenFiber_of_spectrumGenerator H)

/-! ## Certificate -/

/-- P870 certificate: the producer input has been pushed below `PrimeExponent`.
The remaining hard theorem is now the actual SU(7) spectrum statement
`SU7BranchingSpectrumGeneratorEveryEvenFiber`. -/
structure SU7BranchingSpectrumProjectionProducerCertificate where
  project_cell :
    ∀ {n : ℕ} (C : SU7BranchingSpectrumCell n),
      SU7SpectrumCellPrimeProjection C ->
        SU7PrimeEdgeBranchCell n
  projected_residual :
    ∀ {n : ℕ} (C : SU7BranchingSpectrumCell n)
      (hC : SU7SpectrumCellPrimeProjection C),
      branchWeightResidual (primeEdgeBranchCell_of_spectrumCell C hC) =
        C.rawResidual
  support_projects :
    ∀ {n : ℕ} (G : SU7BranchingSpectrumGenerator n),
      SU7SpectrumCellPrimeProjection G.supportCell
  spectrum_to_branch_weight :
    ∀ {n : ℕ}, SU7BranchingSpectrumGenerator n ->
      SU7RepresentationBranchWeightGenerator n
  every_fiber_to_branch_weight :
    SU7BranchingSpectrumGeneratorEveryEvenFiber ->
      SU7RepresentationBranchWeightGeneratorEveryEvenFiber
  every_fiber_to_goldbach :
    SU7BranchingSpectrumGeneratorEveryEvenFiber ->
      EvenGoldbachStatement

def su7BranchingSpectrumProjectionProducerCertificate :
    SU7BranchingSpectrumProjectionProducerCertificate where
  project_cell := primeEdgeBranchCell_of_spectrumCell
  projected_residual := branchWeightResidual_projected_eq_rawResidual
  support_projects := supportCell_primeProjection
  spectrum_to_branch_weight := branchWeightGenerator_of_spectrumGenerator
  every_fiber_to_branch_weight :=
    branchWeightGeneratorEveryEvenFiber_of_spectrumGenerator
  every_fiber_to_goldbach := evenGoldbach_of_spectrumGenerator


end
end StandardModelConstraint
end SaturationMonoid
