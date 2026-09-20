import H0mework.Physics.BranchSources.P876
import H0mework.Physics.AlphaSpectrum.P877

/-!
# Proposition 878: the atom-code producer throat cannot be skipped

P873 correctly moved `Nat.Prime` out of `SU7Atom` and `SU7PhysicalBranchCell`.
This file proves the sharp consequence: with the current placeholder
irreducibility predicate

```lean
IsIrreducibleRepresentation weight := True
```

the faithful atom-code projection law is not derivable.  There is a concrete
irreducible atom with code `4`.

So the next producer is not another wrapper around `SU7AtomCodePrimeProjectionLaw`.
It must be a genuine SU(7) representation-coding theorem:

```lean
∀ w, IsIrreducibleRepresentation w -> Nat.Prime w.code
```

Lean proves that this theorem is exactly equivalent to the atom-code projection
law required downstream.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## A concrete obstruction in the current placeholder atom model -/

/-- The weight with raw code `4`. -/
def compositeCodeFourWeight : SU7WeightLattice where
  code := 4

/-- Under the current placeholder irreducibility predicate, code `4` is
irreducible.  This is the exact point that must be replaced by real SU(7)
representation theory. -/
theorem compositeCodeFourWeight_irreducible :
    IsIrreducibleRepresentation compositeCodeFourWeight := by
  trivial

/-- A physical atom with composite code `4`. -/
def compositeCodeFourAtom : SU7Atom where
  weight := compositeCodeFourWeight
  irreducible := compositeCodeFourWeight_irreducible
  sector := ColorWeakHyperchargeSector.color

/-- THEOREM 1: the concrete composite atom has code `4`. -/
theorem atomCode_compositeCodeFourAtom_eq_four :
    atomCode compositeCodeFourAtom = 4 := rfl

/-- THEOREM 2: the concrete composite atom does not project to a prime code. -/
theorem not_prime_atomCode_compositeCodeFourAtom :
    ¬ Nat.Prime (atomCode compositeCodeFourAtom) := by
  rw [atomCode_compositeCodeFourAtom_eq_four]
  norm_num

/-- THEOREM 3: with the current placeholder irreducibility predicate, the
faithful atom-code prime projection law is false. -/
theorem not_SU7AtomCodePrimeProjectionLaw_currentModel :
    ¬ SU7AtomCodePrimeProjectionLaw := by
  intro h
  exact not_prime_atomCode_compositeCodeFourAtom (h compositeCodeFourAtom)

/-! ## The real producer throat -/

/-- The representation-theoretic producer law needed below P873: irreducible
SU(7) weights project to prime natural codes.  This statement contains no
prime field inside `SU7Atom`; it is a theorem about the representation-code
projection. -/
def SU7IrreducibleCodePrimeProducerLaw : Prop :=
  ∀ w : SU7WeightLattice,
    IsIrreducibleRepresentation w -> Nat.Prime w.code

/-- THEOREM 4: the irreducible-code producer law gives the P873 atom-code
prime projection law. -/
theorem SU7AtomCodePrimeProjectionLaw_of_irreducibleCodePrimeProducerLaw
    (H : SU7IrreducibleCodePrimeProducerLaw) :
    SU7AtomCodePrimeProjectionLaw := by
  intro a
  exact H a.weight a.irreducible

/-- THEOREM 5: the P873 atom-code projection law gives the irreducible-code
producer law. -/
theorem irreducibleCodePrimeProducerLaw_of_SU7AtomCodePrimeProjectionLaw
    (H : SU7AtomCodePrimeProjectionLaw) :
    SU7IrreducibleCodePrimeProducerLaw := by
  intro w hirr
  let a : SU7Atom :=
    { weight := w
      irreducible := hirr
      sector := ColorWeakHyperchargeSector.singlet }
  simpa [a, atomCode] using H a

/-- THEOREM 6: the real representation-coding throat is exactly equivalent to
the atom-code projection law used by the color-loop producer chain. -/
theorem SU7IrreducibleCodePrimeProducerLaw_iff_atomCodeProjection :
    SU7IrreducibleCodePrimeProducerLaw ↔
      SU7AtomCodePrimeProjectionLaw := by
  constructor
  · exact SU7AtomCodePrimeProjectionLaw_of_irreducibleCodePrimeProducerLaw
  · exact irreducibleCodePrimeProducerLaw_of_SU7AtomCodePrimeProjectionLaw

/-- THEOREM 7: the current placeholder representation model also refutes the
irreducible-code producer law. -/
theorem not_SU7IrreducibleCodePrimeProducerLaw_currentModel :
    ¬ SU7IrreducibleCodePrimeProducerLaw := by
  intro h
  exact not_prime_atomCode_compositeCodeFourAtom
    (by
      change Nat.Prime compositeCodeFourWeight.code
      exact h compositeCodeFourWeight compositeCodeFourWeight_irreducible)

/-! ## Certificate -/

/-- P878 certificate: the atom-code prime projection is the real remaining
producer throat, and the current placeholder `True` irreducibility model cannot
prove it. -/
structure SU7AtomCodeProducerThroatCertificate : Prop where
  composite_atom_code :
    atomCode compositeCodeFourAtom = 4
  composite_atom_not_prime :
    ¬ Nat.Prime (atomCode compositeCodeFourAtom)
  current_atom_projection_false :
    ¬ SU7AtomCodePrimeProjectionLaw
  producer_iff_projection :
    SU7IrreducibleCodePrimeProducerLaw ↔
      SU7AtomCodePrimeProjectionLaw
  current_producer_false :
    ¬ SU7IrreducibleCodePrimeProducerLaw

/-- THEOREM 8: canonical P878 atom-code producer throat certificate. -/
def su7AtomCodeProducerThroatCertificate :
    SU7AtomCodeProducerThroatCertificate where
  composite_atom_code := atomCode_compositeCodeFourAtom_eq_four
  composite_atom_not_prime := not_prime_atomCode_compositeCodeFourAtom
  current_atom_projection_false :=
    not_SU7AtomCodePrimeProjectionLaw_currentModel
  producer_iff_projection :=
    SU7IrreducibleCodePrimeProducerLaw_iff_atomCodeProjection
  current_producer_false :=
    not_SU7IrreducibleCodePrimeProducerLaw_currentModel


end
end StandardModelConstraint
end SaturationMonoid
