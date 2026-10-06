import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionForm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9C.Material.SpinPair
open BasinRefinement SourceGaussianModel SourceFiniteData
open YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

theorem original_prepared_slice (uTime : ℝ) (x : Point) :
    prepared (spatialSlice uTime x) = prepared (spatialSlice uTime 0) := by
  have same : Source.vector (spatialSlice uTime x) = Source.vector (spatialSlice uTime 0) := by
    funext i
    simp [Source.vector,Source.amplitude,upperPhase,lowerPhase,phase,spatialSlice]
  simp only [prepared,same]

theorem connection_pair_slice (uTime : ℝ) (x : Point) (direction : LorentzianIndex) :
    connectionPair (spatialSlice uTime x) direction = connectionPair (spatialSlice uTime 0) direction := by
  simp only [connectionPair,connectionVector,original_prepared_slice]

theorem connection_square_slice (uTime : ℝ) (x : Point) (direction : LorentzianIndex) :
    connectionSquare (spatialSlice uTime x) direction = connectionSquare (spatialSlice uTime 0) direction := by
  simp only [connectionSquare,connectionVector,original_prepared_slice]

theorem spatial_section_form (uTime : ℝ) (b c : Basis) (x : Point) (axis : Fin 3) :
    inner ℂ (sectionCovariant b 1 (spatialSlice uTime x) axis.succ)
      (sectionCovariant c 1 (spatialSlice uTime x) axis.succ) =
      (UnifiedOrbitals.derivative b axis x * UnifiedOrbitals.derivative c axis x : ℝ) +
      (UnifiedOrbitals.derivative b axis x * UnifiedOrbitals.ao c x : ℝ) *
        connectionPair (spatialSlice uTime 0) axis.succ +
      (UnifiedOrbitals.ao b x * UnifiedOrbitals.derivative c axis x : ℝ) *
        star (connectionPair (spatialSlice uTime 0) axis.succ) +
      (UnifiedOrbitals.ao b x * UnifiedOrbitals.ao c x : ℝ) *
        connectionSquare (spatialSlice uTime 0) axis.succ := by
  rw [full_section_form]
  simp only [original_orbital_spatial_derivative,orbitalWeight,slice_coordinates,one_mul,
    Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,connection_pair_slice,connection_square_slice,
    UnifiedOrbitals.derivative,UnifiedOrbitals.ao]

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
