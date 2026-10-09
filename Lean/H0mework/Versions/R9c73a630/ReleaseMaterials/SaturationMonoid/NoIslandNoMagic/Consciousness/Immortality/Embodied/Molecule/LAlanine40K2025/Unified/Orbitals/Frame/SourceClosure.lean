import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open BasinRefinement SourceGaussianModel SourceFiniteData MeasureTheory UnifiedAction YangMills.FullPairing
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

structure FrameMaterial where
  original : Matrix Basis Basis ℝ
  gram : Matrix Basis Basis ℝ
  normalized : Matrix Basis Basis ℝ
  dual : Matrix Basis Basis ℝ
  orbitals : Basis → Point → ℝ
  densityMatrix : Matrix Basis Basis ℝ
  density : Point → ℝ
  sections : Basis → ℝ → Point → Hilbert
  covariant : Basis → ℝ → BasePoint → LorentzianIndex → Hilbert
  coulomb : Basis → Basis → Basis → Basis → ℝ
  pairs : Basis → Basis → Point × Point → ℝ
  pairEnergy : Basis → Basis → ℝ
  registeredState : Matrix Basis Basis ℂ

def frameMaterial : FrameMaterial where
  original := originalMetric
  gram := actualGram
  normalized := normalizedSourceFrame
  dual := sourceDualFrame
  orbitals := normalizedOrbital
  densityMatrix := normalizedDensityMatrix
  density := normalizedDensity
  sections := normalizedSection
  covariant := normalizedCovariant
  coulomb := normalizedRepulsion
  pairs := fermionPair
  pairEnergy := fermionPairCoulomb
  registeredState := registeredState Reentry.Source.targetRealized

structure FrameClosure : Prop where
  original_metric_positive : frameMaterial.original.PosDef
  original_gram_positive : frameMaterial.gram.PosDef
  original_gram_error : type_of% actual_gram_entry_error
  dual_recovers : sourceDualFrame*normalizedSourceFrame = 1
  frame_recovers : normalizedSourceFrame*sourceDualFrame = 1
  original_expansion : ∀ v x, ∑ b : Basis, (sourceDualFrame*ᵥv) b*normalizedOrbital b x = expansion v x
  orbital_metric : type_of% actual_normalized_orbitals
  density_preserved : type_of% actual_original_D3_preserved
  original_registered_expansion : ∀ v x, ∑ b : Basis, (registeredCoordinates*ᵥv) b*normalizedOrbital b x =
    expansion (realInverse*ᵥv) x
  full_Gamma : type_of% actual_Gamma_spatial_preservation
  original_error : type_of% actual_registered_state_error
  U_metric : type_of% actual_normalized_U_section_integral
  U_full_preparation : ∀ A B b c time, (∫ x : Point, inner ℂ (normalizedPreparedSection A b time x)
    (normalizedPreparedSection B c time x)) = (if b=c then 1 else 0)*
      Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer (spatialSlice time 0))
        (Stage9DEF.Compatibility.responseMatrix (pairedMother A B))
  U_covariant : type_of% normalized_actual_covariant
  Hamiltonian : type_of% actual_Hamiltonian_response
  joint_unitary : type_of% actual_joint_unitary_spatial
  Coulomb_transform : type_of% actual_coulomb_transformation
  pair_exchange : type_of% fermion_pair_exchange
  pair_normalization : type_of% actual_fermion_pair_normalized
  pair_Coulomb_integrable : type_of% fermion_pair_coulomb_integrable
  pair_Coulomb : type_of% fermion_pair_coulomb_direct_exchange

theorem sourceGeneratedFrameClosure : FrameClosure :=
  ⟨actual_original_metric_positive,actual_gram_positive,actual_gram_entry_error,
    dual_mul_frame actual_gram_positive,frame_mul_dual actual_gram_positive,
    original_expansion_recovered actual_gram_positive,actual_normalized_orbitals,
    actual_original_D3_preserved,registered_expansion_preserved actual_gram_positive,
    actual_Gamma_spatial_preservation,actual_registered_state_error,actual_normalized_U_section_integral,
    normalized_full_U_preparation actual_gram_positive,normalized_actual_covariant,
    actual_Hamiltonian_response,actual_joint_unitary_spatial,actual_coulomb_transformation,
    fermion_pair_exchange,actual_fermion_pair_normalized,fermion_pair_coulomb_integrable,
    fermion_pair_coulomb_direct_exchange⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
