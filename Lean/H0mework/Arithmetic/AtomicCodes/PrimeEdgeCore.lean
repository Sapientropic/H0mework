import H0mework.Arithmetic.AtomicCodes.TensorIrreducibilityCore

/-!
# Proposition 906 Core: SU(7) tensor-irreducible atoms

This core file contains only the upstream atom shape used by the same-carrier
producer chain.  It does not project those atoms to downstream primality,
prime-edge cells, or trace-zero arithmetic loops.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Tensor-irreducible atoms -/

/-- A SU(7) atom whose irreducibility is witnessed by tensor
indecomposability relative to a tensor-coding carrier. -/
structure SU7TensorIrreducibleAtom
    (C : SU7WeightTensorCoding) where
  weight : SU7WeightLattice
  tensor_irreducible : SU7TensorIrreducible C weight
  sector : ColorWeakHyperchargeSector

/-- Forget the tensor witness to the existing physical atom shape.  The old
`irreducible` field is still the project-wide placeholder, so the tensor proof
is intentionally kept in the refined atom and not hidden there. -/
def SU7TensorIrreducibleAtom.toSU7Atom
    {C : SU7WeightTensorCoding}
    (a : SU7TensorIrreducibleAtom C) : SU7Atom where
  weight := a.weight
  irreducible := trivial
  sector := a.sector

@[simp] theorem tensorIrreducibleAtom_toSU7Atom_atomCode
    {C : SU7WeightTensorCoding}
    (a : SU7TensorIrreducibleAtom C) :
    atomCode a.toSU7Atom = a.weight.code := rfl

/-! ## Certificate -/

/-- Core atom certificate for upstream producer files. -/
structure SU7TensorIrreducibleAtomCoreCertificate where
  tensor_atom :
    SU7WeightTensorCoding -> Type
  tensor_atom_to_physical :
    ∀ {C : SU7WeightTensorCoding},
      SU7TensorIrreducibleAtom C -> SU7Atom
  tensor_atom_code :
    ∀ {C : SU7WeightTensorCoding}
      (a : SU7TensorIrreducibleAtom C),
      atomCode a.toSU7Atom = a.weight.code

def su7TensorIrreducibleAtomCoreCertificate :
    SU7TensorIrreducibleAtomCoreCertificate where
  tensor_atom := SU7TensorIrreducibleAtom
  tensor_atom_to_physical := SU7TensorIrreducibleAtom.toSU7Atom
  tensor_atom_code := tensorIrreducibleAtom_toSU7Atom_atomCode


end
end StandardModelConstraint
end SaturationMonoid
