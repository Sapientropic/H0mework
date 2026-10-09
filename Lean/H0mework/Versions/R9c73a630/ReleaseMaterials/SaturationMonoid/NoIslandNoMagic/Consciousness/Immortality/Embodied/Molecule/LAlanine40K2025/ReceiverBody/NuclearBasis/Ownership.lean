import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.SourceData

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
noncomputable section

/-- Original primitive address within its registered AO row. -/
abbrev Primitive (i : Basis) := Fin (sourceTerms i).length

def primitive (i : Basis) (p : Primitive i) : Term := (sourceTerms i).get p

def rawPrimitive (i : Basis) (p : Primitive i) : RawTerm := (rawTerms[i.val]!)[p.val]!

theorem raw_source_length (i : Basis) : (sourceTerms i).length=(rawTerms[i.val]!).size := by
  unfold sourceTerms orbitalRead
  rw [List.length_map,Array.length_toList]
  rfl

theorem primitive_atom_bound : ∀ (i : Basis) (p : Primitive i), (rawPrimitive i p).atom<13 := by
  decide +kernel

/-- The owner is the source atom label at the same address, not a centre-matching choice. -/
def owner (i : Basis) (p : Primitive i) : Fin 13 :=
  ⟨(rawPrimitive i p).atom,primitive_atom_bound i p⟩

theorem owner_label (i : Basis) (p : Primitive i) : (owner i p).val=(rawPrimitive i p).atom := rfl

theorem primitive_centre : ∀ (i : Basis) (p : Primitive i),
    (primitive i p).centre=UnifiedOrbitals.Attraction.Precise.nucleus (owner i p) := by
  decide +kernel

theorem primitive_weight : ∀ (i : Basis) (p : Primitive i),
    (primitive i p).weight=ratRead (rawPrimitive i p).weight := by
  decide +kernel

theorem primitive_exponent : ∀ (i : Basis) (p : Primitive i),
    (primitive i p).exponent=ratRead (rawPrimitive i p).exponent := by
  decide +kernel

theorem primitive_powers : ∀ (i : Basis) (p : Primitive i) (k : Fin 3),
    (primitive i p).powers k=(rawPrimitive i p).powers[k.val]! := by
  decide +kernel

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
