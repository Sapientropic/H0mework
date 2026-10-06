import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Matrix
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
open scoped InnerProductSpace BigOperators
noncomputable section

/-- The normalized section is fixed by the original U matter, in its original full exterior coordinates. -/
def scalarSection (b : Basis) (scale : ℝ) (p : BasePoint) : YangMills.FullPairing.Hilbert :=
  orbitalWeight b scale p • YangMills.FullPairing.prepared p

theorem original_section_coordinates (b : Basis) (scale : ℝ) (p : BasePoint) :
    YangMills.FullPairing.naturalCoordinates ((orbitalTest b scale).matter p) =
      (2 : ℂ) • scalarSection b scale p := by
  change YangMills.FullPairing.naturalCoordinates
    (orbitalWeight b scale p • Stage10.Runtime.configuration.matter p) = _
  rw [map_smul,Stage10.Runtime.configuration_eq,YangMills.FullPairing.actual_eq_twice_prepared]
  unfold scalarSection
  module

theorem scalarSection_pair (b c : Basis) (scale : ℝ) (p : BasePoint) :
    inner ℂ (scalarSection b scale p) (scalarSection c scale p) =
      star (orbitalWeight b scale p)*orbitalWeight c scale p := by
  simp [scalarSection,inner_self_eq_norm_sq_to_K,
    YangMills.FullPairing.prepared_norm,mul_comm]

def sectionDensity (scale : ℝ) (p : BasePoint) : ℂ :=
  ∑ b : Basis, ∑ c : Basis, (densityMatrix b c : ℂ)*inner ℂ (scalarSection b scale p) (scalarSection c scale p)

/-- The same original D3 contraction of the U-generated sections is exactly the original scalar density. -/
theorem original_D3_section_density (scale : ℝ) (p : BasePoint) :
    sectionDensity scale p = (sourceDensity (spatialPoint scale p) : ℂ) := by
  simp only [sectionDensity,scalarSection_pair,orbitalWeight,Complex.star_def,Complex.conj_ofReal,
    sourceDensity,SourceGaussianModel.density,bilinear,Complex.ofReal_sum,Complex.ofReal_mul,
    Complex.ofReal_ratCast,mul_assoc]
  rfl

def spatialSlice (time : ℝ) (x : Point) : BasePoint := WithLp.toLp 2 (Fin.cons time x)

theorem slice_coordinates (time : ℝ) (x : Point) : spatialPoint 1 (spatialSlice time x) = x := by
  funext a
  simp [spatialPoint,spatialSlice]

theorem slice_pair (time : ℝ) (b c : Basis) (x : Point) :
    inner ℂ (scalarSection b 1 (spatialSlice time x)) (scalarSection c 1 (spatialSlice time x)) =
      (UnifiedOrbitals.ao b x * UnifiedOrbitals.ao c x : ℝ) := by
  rw [scalarSection_pair]
  simp only [orbitalWeight,slice_coordinates,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,
    UnifiedOrbitals.ao]

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
