import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.TwoBody

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix Kronecker BigOperators
noncomputable section

theorem two_body_left_exchange (x₁ x₂ y₁ y₂ : SpinBasis) :
    twoBodyContraction x₂ x₁ y₁ y₂ = -twoBodyContraction x₁ x₂ y₁ y₂ := by
  rw [two_body_wick,two_body_wick]
  ring

theorem two_body_right_exchange (x₁ x₂ y₁ y₂ : SpinBasis) :
    twoBodyContraction x₁ x₂ y₂ y₁ = -twoBodyContraction x₁ x₂ y₁ y₂ := by
  rw [two_body_wick,two_body_wick]
  ring

theorem two_body_same_spin_orbital (x y₁ y₂ : SpinBasis) :
    twoBodyContraction x x y₁ y₂ = 0 := by
  rw [two_body_wick]
  ring

private theorem spin_projector_entry (i j : Basis) (s t : Bool) :
    spinProjector (i,s) (j,t) = if s = t then projector24 i j else 0 := by
  rw [spin_projector_factorizes]
  simp [Matrix.one_apply]

def spinSummedTwoBody (i j k l : Basis) : ℂ :=
  ∑ s : Bool, ∑ t : Bool,
    twoBodyContraction (i,s) (j,t) (k,s) (l,t)

theorem spin_summed_two_body (i j k l : Basis) :
    spinSummedTwoBody i j k l =
      (4 : ℂ) * projector24 i k * projector24 j l -
        (2 : ℂ) * projector24 i l * projector24 j k := by
  simp only [spinSummedTwoBody,two_body_source_projector,spin_projector_entry]
  simp
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
