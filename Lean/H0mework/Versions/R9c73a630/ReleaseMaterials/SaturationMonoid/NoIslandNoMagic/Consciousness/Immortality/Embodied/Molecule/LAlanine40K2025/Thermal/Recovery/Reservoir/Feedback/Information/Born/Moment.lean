import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.SpectralReservoir

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

open Collision Quantum Work.Capacity Propagation.Producer
open scoped Matrix ComplexOrder BigOperators

noncomputable section

/-- The pure trace identity used inside `Spectrum.energy_spectral_bounds`. -/
theorem spectral_first_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observable state : Matrix ι ι ℂ) (hermitian : observable.IsHermitian) :
    (∑ i, (conjugation (star hermitian.eigenvectorUnitary) state i i).re *
      hermitian.eigenvalues i) = energy observable state := by
  symm
  rw [← energy_unitary_conjugation observable state (star hermitian.eigenvectorUnitary),
    hermitian.conjStarAlgAut_star_eigenvectorUnitary]
  change energy (Matrix.diagonal (fun i => (hermitian.eigenvalues i : ℂ)))
    (conjugation (star hermitian.eigenvectorUnitary) state) = _
  simp [energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.mul_re, mul_comm]

theorem block_spectral_first_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observable : Matrix ι ι ℂ) (hermitian : observable.IsHermitian)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (∑ i, (conjugation (blockUnitary (star hermitian.eigenvectorUnitary)
      (star hermitian.eigenvectorUnitary)) joint i i).re *
      Sum.elim hermitian.eigenvalues hermitian.eigenvalues i) =
      energy observable (bodyRead joint) := by
  rw [Fintype.sum_sum_type]
  let rotated := conjugation (blockUnitary (star hermitian.eigenvectorUnitary)
    (star hermitian.eigenvectorUnitary)) joint
  change (∑ i, (rotated.toBlocks₁₁ i i).re *
      hermitian.eigenvalues i) +
    (∑ i, (rotated.toBlocks₂₂ i i).re *
      hermitian.eigenvalues i) = _
  have left : rotated.toBlocks₁₁ =
      conjugation (star hermitian.eigenvectorUnitary) joint.toBlocks₁₁ := by
    simp only [rotated, conjugation_apply, blockUnitary_conjugation_diagonal_left]
  have right : rotated.toBlocks₂₂ =
      conjugation (star hermitian.eigenvectorUnitary) joint.toBlocks₂₂ := by
    simp only [rotated, conjugation_apply, blockUnitary_conjugation_diagonal_right]
  rw [left, right, spectral_first_moment, spectral_first_moment]
  exact (Load.Producer.HeatProbability.energy_add_right _ _ _).symm

theorem first_moment (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) :
    (∑ i, (distribution observable hermitian current i).toReal * outcome observable hermitian i) =
      energy observable (bodyRead current.joint) := by
  simp only [distribution_toReal]
  exact block_spectral_first_moment observable hermitian current.joint

theorem first_moment_response (observable : Current.FullJoint)
    (hermitian : observable.IsHermitian) :
    (∑ i, (distribution observable hermitian firstState i).toReal * outcome observable hermitian i) =
      energy observable (conjugation (Current.loadPulse (nativeClockStep : ℝ))
        receivedState.joint.toBlocks₁₁) +
      energy observable (conjugation (freePhase (nativeClockStep : ℝ) •
        Current.pulse (nativeClockStep : ℝ)) receivedState.joint.toBlocks₂₂) :=
  (first_moment observable hermitian firstState).trans
    (respondNext_observable observable receivedState)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
