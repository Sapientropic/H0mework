import H0mework.Arithmetic.AtomicCodes.P1008

/-!
# Proposition 1009: finite endpoint-indexed generators cannot be complete

P1008 proved that any globally bounded endpoint-code spectrum cannot be the
same-carrier tensor producer.  This file proves the finite-index version that
targets the current SU(7) danger directly:

if the endpoint codes of a purported all-fiber producer factor through one
fixed finite index type, then the codes are automatically bounded, so the
producer cannot cover every active fiber.

This keeps the conclusion upstream of the arithmetic throat.  It only talks
about same-carrier endpoint codes and finite index readouts.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Finite endpoint-indexed producer shapes -/

/-- A concrete same-carrier producer whose endpoint codes factor through one
fixed finite index type. -/
def FiniteEndpointIndexedConcreteProducer
    (ι : Type*) [Fintype ι]
    (leftCode rightCode : ι -> ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ i : ι,
      ∃ cell : SU7SameCarrierAtomicCell n,
        sameCarrierAtomCode cell.leftAtom = leftCode i ∧
          sameCarrierAtomCode cell.rightAtom = rightCode i ∧
            SameCarrierConcreteAtomicZero cell

/-- A tensor same-carrier producer whose endpoint codes factor through one
fixed finite index type. -/
def FiniteEndpointIndexedTensorProducer
    (C : SameCarrierWeightTensorCoding)
    (ι : Type*) [Fintype ι]
    (leftCode rightCode : ι -> ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ i : ι,
      ∃ cell : SU7SameCarrierAtomicCell n,
        sameCarrierAtomCode cell.leftAtom = leftCode i ∧
          sameCarrierAtomCode cell.rightAtom = rightCode i ∧
            SameCarrierTensorAtomicZero C cell

/-! ## Finite endpoint readouts are bounded -/

/-- The uniform endpoint-code bound induced by a finite endpoint-index type. -/
def finiteEndpointIndexBound
    (ι : Type*) [Fintype ι]
    (leftCode rightCode : ι -> ℕ) : ℕ :=
  Finset.univ.sup leftCode + Finset.univ.sup rightCode

/-- Any concrete cell whose endpoint codes factor through the finite index is
bounded by `finiteEndpointIndexBound`. -/
theorem endpointCodesBounded_of_finiteEndpointIndex
    {ι : Type*} [Fintype ι]
    (leftCode rightCode : ι -> ℕ)
    {n : ℕ} {cell : SU7SameCarrierAtomicCell n} {i : ι}
    (hleft : sameCarrierAtomCode cell.leftAtom = leftCode i)
    (hright : sameCarrierAtomCode cell.rightAtom = rightCode i) :
    SameCarrierEndpointCodesBounded
      (finiteEndpointIndexBound ι leftCode rightCode) cell := by
  unfold SameCarrierEndpointCodesBounded finiteEndpointIndexBound
  constructor
  · rw [hleft]
    have hle :
        leftCode i ≤ Finset.univ.sup leftCode := by
      exact Finset.le_sup (s := Finset.univ) (f := leftCode) (b := i)
        (by simp)
    omega
  · rw [hright]
    have hle :
        rightCode i ≤ Finset.univ.sup rightCode := by
      exact Finset.le_sup (s := Finset.univ) (f := rightCode) (b := i)
        (by simp)
    omega

/-! ## No finite endpoint-indexed producer can be complete -/

/-- No concrete all-fiber producer can have endpoint codes factoring through
one fixed finite index type. -/
theorem no_finiteEndpointIndexedConcreteProducer
    (ι : Type*) [Fintype ι]
    (leftCode rightCode : ι -> ℕ) :
    ¬ FiniteEndpointIndexedConcreteProducer ι leftCode rightCode := by
  intro hproducer
  let bound := finiteEndpointIndexBound ι leftCode rightCode
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases hproducer n hn with ⟨i, cell, hleft, hright, hzero⟩
  have hbounded :
      SameCarrierEndpointCodesBounded bound cell :=
    endpointCodesBounded_of_finiteEndpointIndex leftCode rightCode
      hleft hright
  exact not_concreteAtomicZero_of_endpointCodesBounded
    hbounded hgt hzero

/-- No tensor all-fiber producer can have endpoint codes factoring through
one fixed finite index type. -/
theorem no_finiteEndpointIndexedTensorProducer
    (C : SameCarrierWeightTensorCoding)
    (ι : Type*) [Fintype ι]
    (leftCode rightCode : ι -> ℕ) :
    ¬ FiniteEndpointIndexedTensorProducer C ι leftCode rightCode := by
  intro hproducer
  let bound := finiteEndpointIndexBound ι leftCode rightCode
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases hproducer n hn with ⟨i, cell, hleft, hright, hzero⟩
  have hbounded :
      SameCarrierEndpointCodesBounded bound cell :=
    endpointCodesBounded_of_finiteEndpointIndex leftCode rightCode
      hleft hright
  exact not_tensorAtomicZero_of_endpointCodesBounded C
    hbounded hgt hzero


end StandardModelConstraint
end SaturationMonoid
