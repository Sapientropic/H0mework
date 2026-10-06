import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Sections

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open BasinRefinement SourceGaussianModel SourceFiniteData UnifiedAction YangMills.FullPairing
open scoped InnerProductSpace BigOperators ContDiff
noncomputable section

def normalizedWeight (b : Basis) (scale : ℝ) (p : BasePoint) : ℂ :=
  ∑ i : Basis, (normalizedSourceFrame i b : ℂ)*orbitalWeight i scale p

theorem normalizedWeight_smooth (b : Basis) (scale : ℝ) : ContDiff ℝ ∞ (normalizedWeight b scale) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (orbitalWeight_smooth i scale)

theorem normalized_weight_slice (b : Basis) (time : ℝ) (x : Point) :
    normalizedWeight b 1 (spatialSlice time x) = (normalizedOrbital b x : ℂ) := by
  simp only [normalizedWeight,orbitalWeight,slice_coordinates,normalizedOrbital,expansion,ao,
    Complex.ofReal_sum,Complex.ofReal_mul]

def normalizedTest (b : Basis) (scale : ℝ) : StageNineHolonomicConfiguration := weighted (normalizedWeight b scale)

def normalizedCovariant (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) : Hilbert :=
  operator (normalizedWeight b scale p • Stage9DEF.Compatibility.covariantAction direction+
    fieldDirectionalDerivative (normalizedWeight b scale) p direction • LinearMap.id) (prepared p)

theorem normalized_actual_covariant (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) :
    naturalCoordinates (holonomicMatterCovariantDerivative (normalizedTest b scale) p direction) =
      (2 : ℂ) • normalizedCovariant b scale p direction := by
  have derivative := weighted_covariant_derivative (normalizedWeight b scale) p
    ((normalizedWeight_smooth b scale).differentiable (by simp) p) direction
  have original : holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction =
      Stage9DEF.Compatibility.covariantAction direction (Stage10.Runtime.configuration.matter p) := by
    rw [Stage10.Runtime.configuration_eq]
    exact (Stage9DEF.Compatibility.actual_covariantAction p direction).symm
  change naturalCoordinates (holonomicMatterCovariantDerivative (weighted (normalizedWeight b scale)) p direction) = _
  rw [derivative,original]
  have action : normalizedWeight b scale p • Stage9DEF.Compatibility.covariantAction direction
        (Stage10.Runtime.configuration.matter p)+fieldDirectionalDerivative (normalizedWeight b scale) p direction •
        Stage10.Runtime.configuration.matter p =
      (normalizedWeight b scale p • Stage9DEF.Compatibility.covariantAction direction+
        fieldDirectionalDerivative (normalizedWeight b scale) p direction • LinearMap.id : Mother)
          (Stage10.Runtime.configuration.matter p) := rfl
  rw [action,← operator_coordinates,Stage10.Runtime.configuration_eq,actual_eq_twice_prepared,map_smul]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
