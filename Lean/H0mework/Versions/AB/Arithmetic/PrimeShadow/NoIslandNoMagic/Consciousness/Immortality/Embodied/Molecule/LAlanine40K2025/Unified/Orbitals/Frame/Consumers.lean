import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Producer
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Density
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.FermionPair
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Wave
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Derivative
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Registered
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerElectronic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory UnifiedAction YangMills.FullPairing
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Reentry.Source.targetRealized Reentry.Source.hamiltonian Reentry.Producer.sourceJointUnitary sourceWave normalizedSection normalizedSourceFrame

theorem actual_normalized_orbitals (b c : Basis) :
    (∫ x : Point, normalizedOrbital b x*normalizedOrbital c x) = if b=c then 1 else 0 :=
  normalized_pair actual_gram_positive b c

theorem actual_normalized_U_section_integral (b c : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (normalizedSection b time x) (normalizedSection c time x)) =
      if b=c then 1 else 0 := normalized_U_section_integral actual_gram_positive b c time

theorem actual_original_D3_preserved (x : Point) : normalizedDensity x = sourceDensity x :=
  actual_density_preserved actual_gram_positive x

theorem actual_gram_norm_error : ‖complexMatrix actualGram-1‖ ≤ (196/10^9 : ℝ) := by
  have bound := gram_norm_from_entries (2/10^9) (by norm_num) actual_gram_entry_error
  convert bound using 1
  norm_num

theorem actual_registered_state_error (D : Matrix Basis Basis ℂ) :
    ‖registeredState D-D‖ ≤ (4/10^7 : ℝ)*‖D‖ := by
  have bound := registered_state_error actual_gram_positive D
  have near := actual_gram_norm_error
  calc
    _ ≤ _ := bound
    _ ≤ ((196/10^9 : ℝ)*‖D‖)*(2+196/10^9) := by gcongr
    _ ≤ _ := by nlinarith [norm_nonneg D]

/-- The entire original complex Gamma, including its imaginary channel, enters the same spatial frame. -/
theorem actual_Gamma_spatial_preservation :
    complexFrame * registeredState Reentry.Source.targetRealized * star complexFrame =
      registeredAOState Reentry.Source.targetRealized :=
  registered_state_spatially_preserved actual_gram_positive _

theorem actual_Hamiltonian_response (v w : Basis → ℂ) (uTime : ℝ) :
    (∫ x : Point, inner ℂ (sourceWave v uTime x)
      (sourceWave (Reentry.Source.hamiltonian*ᵥw) uTime x)) =
        star v ⬝ᵥ (Reentry.Source.hamiltonian*ᵥw) :=
  source_matrix_response actual_gram_positive Reentry.Source.hamiltonian v w uTime

theorem actual_joint_unitary_spatial (v w : Basis → ℂ) (uTime : ℝ) :
    (∫ x : Point, inner ℂ
      (sourceWave ((Reentry.Producer.sourceJointUnitary : Matrix Basis Basis ℂ)*ᵥv) uTime x)
      (sourceWave ((Reentry.Producer.sourceJointUnitary : Matrix Basis Basis ℂ)*ᵥw) uTime x)) =
        star v ⬝ᵥ w := source_unitary_preserves actual_gram_positive Reentry.Producer.sourceJointUnitary v w uTime

theorem actual_fermion_pair_normalized (i j : Basis) (different : i ≠ j) :
    (∫ z : Point × Point, (fermionPair i j z)^2) = 1 :=
  fermion_pair_normalized actual_gram_positive i j different

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
