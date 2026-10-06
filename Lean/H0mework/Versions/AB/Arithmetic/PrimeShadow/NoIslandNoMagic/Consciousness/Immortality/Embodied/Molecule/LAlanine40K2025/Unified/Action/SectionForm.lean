import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionDerivative

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9DEF
open BasinRefinement SourceGaussianModel SourceFiniteData
open YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

def connectionVector (p : BasePoint) (direction : LorentzianIndex) : Hilbert :=
  operator (Compatibility.covariantAction direction) (prepared p)

def connectionPair (p : BasePoint) (direction : LorentzianIndex) : ℂ :=
  inner ℂ (prepared p) (connectionVector p direction)

def connectionSquare (p : BasePoint) (direction : LorentzianIndex) : ℂ :=
  inner ℂ (connectionVector p direction) (connectionVector p direction)

theorem full_section_form (b c : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) :
    inner ℂ (sectionCovariant b scale p direction) (sectionCovariant c scale p direction) =
      star (fieldDirectionalDerivative (orbitalWeight b scale) p direction) *
        fieldDirectionalDerivative (orbitalWeight c scale) p direction +
      star (fieldDirectionalDerivative (orbitalWeight b scale) p direction) * orbitalWeight c scale p *
        connectionPair p direction +
      star (orbitalWeight b scale p) * fieldDirectionalDerivative (orbitalWeight c scale) p direction *
        star (connectionPair p direction) +
      star (orbitalWeight b scale p) * orbitalWeight c scale p * connectionSquare p direction := by
  rw [section_covariant_expansion,section_covariant_expansion]
  have unit : inner ℂ (prepared p) (prepared p) = 1 := by
    simp [inner_self_eq_norm_sq_to_K,prepared_norm]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,unit,mul_one]
  unfold connectionPair connectionSquare connectionVector
  have swapped : inner ℂ (operator (Compatibility.covariantAction direction) (prepared p)) (prepared p) =
      star (inner ℂ (prepared p) (operator (Compatibility.covariantAction direction) (prepared p))) :=
    (inner_conj_symm _ _).symm
  rw [swapped]
  have conjugate : (starRingEnd ℂ : ℂ → ℂ) = star := rfl
  rw [conjugate]
  ring

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
