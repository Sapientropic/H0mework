import H0mework.Physics.BranchSources.P873

/-!
# Proposition 905 Core: SU(7) tensor-coding language

This core file contains only the representation-side tensor language needed by
upstream producer files:

* tensor coding of SU(7) weights;
* tensor irreducibility;
* the raw code tensor normal form;
* realization of the placeholder representation predicate by tensor
  irreducibility.

It intentionally contains no downstream primality predicate, no prime-edge
loop, and no Goldbach projection.  Those downstream projections live in
`Proposition905`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Tensor coding of SU(7) weights -/

/-- A tensor-coding certificate for raw SU(7) weight codes.

The `lift_factorization` field is the faithful-pullback part: numerical
factorizations of the code are not allowed to float outside representation
theory; they must lift to tensor decompositions in the carrier. -/
structure SU7WeightTensorCoding where
  tensor : SU7WeightLattice -> SU7WeightLattice -> SU7WeightLattice
  tensor_code_mul :
    ∀ u v : SU7WeightLattice,
      (tensor u v).code = u.code * v.code
  lift_factorization :
    ∀ (w : SU7WeightLattice) (a b : ℕ),
      w.code = a * b ->
        ∃ u v : SU7WeightLattice,
          u.code = a ∧
            v.code = b ∧
              (tensor u v).code = w.code

/-- The raw code carrier has a canonical tensor coding by multiplying codes.
This is not the physical SU(7) theorem by itself; it is the carrier normal
form used by a physical representation model. -/
def rawCodeTensorCoding : SU7WeightTensorCoding where
  tensor u v := { code := u.code * v.code }
  tensor_code_mul := by
    intro u v
    rfl
  lift_factorization := by
    intro w a b hfactor
    refine ⟨{ code := a }, { code := b }, rfl, rfl, ?_⟩
    simpa using hfactor.symm

/-! ## Tensor irreducibility -/

/-- Tensor irreducibility of a weight relative to a tensor coding.

The definition says the weight is nontrivial and every tensor decomposition
has a unit-code factor.  It deliberately does not mention the downstream
primality predicate. -/
def SU7TensorIrreducible
    (C : SU7WeightTensorCoding) (w : SU7WeightLattice) : Prop :=
  2 ≤ w.code ∧
    ∀ u v : SU7WeightLattice,
      (C.tensor u v).code = w.code ->
        u.code = 1 ∨ v.code = 1

/-! ## Realizing the existing irreducibility predicate by tensor irreducibility -/

/-- A concrete representation model realizes the existing irreducibility
predicate when every `IsIrreducibleRepresentation` proof entails tensor
irreducibility for the chosen coding. -/
def SU7TensorCodingRealizesIrreducibility
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ w : SU7WeightLattice,
    IsIrreducibleRepresentation w ->
      SU7TensorIrreducible C w

/-! ## Certificate -/

/-- Core certificate for the upstream tensor-coding language. -/
structure SU7TensorCodingCoreCertificate where
  raw_tensor_coding : SU7WeightTensorCoding
  tensor_irreducible :
    SU7WeightTensorCoding -> SU7WeightLattice -> Prop
  tensor_realization :
    SU7WeightTensorCoding -> Prop

def su7TensorCodingCoreCertificate :
    SU7TensorCodingCoreCertificate where
  raw_tensor_coding := rawCodeTensorCoding
  tensor_irreducible := SU7TensorIrreducible
  tensor_realization := SU7TensorCodingRealizesIrreducibility


end
end StandardModelConstraint
end SaturationMonoid
