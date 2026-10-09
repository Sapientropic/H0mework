import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spin
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section

structure Material where
  parent : Occupation.Material
  originalGamma : Matrix Basis Basis ℂ
  sourceFactor : Matrix Basis OccupiedSlot ℂ
  normalizedFactor : Matrix Basis OccupiedSlot ℂ
  spatialProjector : Matrix Basis Basis ℂ
  spinFactor : Matrix SpinBasis SpinSlot ℂ
  spinProjector : Matrix SpinBasis SpinBasis ℂ
  spinSummed : Matrix Basis Basis ℂ
  electronCount : ℕ
  wave : OccupiedSlot → ℝ → Point → Hilbert

def material : Material where
  parent := Occupation.material
  originalGamma := Occupation.gamma
  sourceFactor := factor
  normalizedFactor := normalizedFactor
  spatialProjector := projector24
  spinFactor := spinFactor
  spinProjector := spinProjector
  spinSummed := spinSummed
  electronCount := Reification.sourceElectronCount
  wave := wave24

theorem source_parent : material.parent = Occupation.material := rfl
theorem source_density : material.originalGamma = material.parent.gamma := rfl
theorem source_electron_identity : material.electronCount = Fintype.card SpinSlot :=
  source_spin_count
theorem source_closed_shell : Reification.densityInterpretation =
    "closed-shell spin-summed D; D_alpha = D_beta = D / 2" := rfl

structure Closure : Prop where
  parent : Occupation.Closure
  parent_identity : type_of% source_parent
  gamma_identity : type_of% source_density
  source_count : type_of% source_electron_identity
  source_method : type_of% source_closed_shell
  gram_bound : type_of% gram_norm_bound
  gamma_bound : type_of% gamma_norm_bound
  gram_positive : type_of% gram_positive
  factor_isometry : type_of% normalized_isometry
  projector_positive : type_of% projector24_positive
  projector_idempotent : type_of% projector24_idempotent
  projector_trace : type_of% projector24_trace
  spin_isometry : type_of% spin_isometry
  spin_positive : type_of% spin_projector_positive
  spin_idempotent : type_of% spin_projector_idempotent
  spin_trace : material.spinProjector.trace = (material.electronCount : ℂ)
  spin_summed : material.spinSummed = (2 : ℂ) • material.spatialProjector
  gamma_source_error : type_of% source_projection_error_small
  gamma_U_error : ‖material.originalGamma - material.spinSummed‖ < (1 / 10^5 : ℝ)
  U_wave : ∀ a b time,
    (∫ x : Point, inner ℂ (material.wave a time x) (material.wave b time x)) =
      if a = b then 1 else 0
  U_response : type_of% actual_U_gamma_response

theorem sourceGeneratedClosure : Closure :=
  ⟨Occupation.sourceGeneratedClosure,source_parent,source_density,source_electron_identity,
    source_closed_shell,gram_norm_bound,gamma_norm_bound,gram_positive,normalized_isometry,
    projector24_positive,projector24_idempotent,projector24_trace,spin_isometry,
    spin_projector_positive,spin_projector_idempotent,
    (by
      change spinProjector.trace = (Reification.sourceElectronCount : ℂ)
      rw [show Reification.sourceElectronCount = 48 by decide]
      exact spin_projector_trace),
    (by simpa only [material] using spin_summed_projector),
    source_projection_error_small,
    (by simpa only [material] using actual_U_spin_density_error),
    (by intro a b time; exact wave24_orthonormal a b time),actual_U_gamma_response⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
