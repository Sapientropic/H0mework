import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Physical
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev SpinSlot := OccupiedSlot × Bool
abbrev SpinBasis := Basis × Bool

def spinFactor : Matrix SpinBasis SpinSlot ℂ :=
  normalizedFactor ⊗ₖ (1 : Matrix Bool Bool ℂ)

theorem spin_isometry : spinFactor.conjTranspose * spinFactor = 1 := by
  unfold spinFactor
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul]
  rw [Matrix.conjTranspose_one,Matrix.one_mul,normalized_isometry]
  exact Matrix.one_kronecker_one

def spinProjector : Matrix SpinBasis SpinBasis ℂ :=
  spinFactor * spinFactor.conjTranspose

theorem spin_projector_positive : spinProjector.PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose spinFactor

theorem spin_projector_idempotent : spinProjector * spinProjector = spinProjector := by
  unfold spinProjector
  calc
    _ = spinFactor * (spinFactor.conjTranspose * spinFactor) *
        spinFactor.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [spin_isometry,Matrix.mul_one]

theorem spin_projector_trace : spinProjector.trace = (48 : ℂ) := by
  rw [spinProjector,Matrix.trace_mul_comm,spin_isometry]
  simp [Matrix.trace_one,Fintype.card_prod,Fintype.card_fin]

theorem source_spin_count : Reification.sourceElectronCount = Fintype.card SpinSlot := by
  rw [source_electron_count]
  decide

theorem spin_projector_factorizes :
    spinProjector = projector24 ⊗ₖ (1 : Matrix Bool Bool ℂ) := by
  unfold spinProjector spinFactor
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul]
  rw [Matrix.conjTranspose_one,Matrix.one_mul]
  rfl

theorem spin_summed (i j : Basis) :
    (∑ s : Bool, spinProjector (i,s) (j,s)) = (2 : ℂ) * projector24 i j := by
  rw [spin_projector_factorizes]
  simp

def spinSummed : Matrix Basis Basis ℂ :=
  fun i j => ∑ s : Bool, spinProjector (i,s) (j,s)

theorem spin_summed_projector : spinSummed = (2 : ℂ) • projector24 := by
  ext i j
  exact spin_summed i j

theorem actual_U_spin_density_error :
    ‖Occupation.gamma - spinSummed‖ < (1 / 10^5 : ℝ) := by
  rw [spin_summed_projector]
  exact actual_U_gamma_projection_error

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
