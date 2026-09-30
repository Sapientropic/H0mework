import H0mework.Chemistry.LAlanineHeldForce.SourceSourceBoundLAlanineHeldForce
import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedSCFTransportSeparation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def realizationDelta (i j : Basis) : Int := Source.gammaNumerator i j - ElectronicFrame.Producer.heldNumerator i j
def realizationDeltaMagnitude : Nat := ∑ i : Basis, ∑ j : Basis, (realizationDelta i j).natAbs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem realizationDeltaMagnitude_exact : realizationDeltaMagnitude = 242 := by decide

theorem realized_delta_entry (i j : Basis) :
    (Source.realizedHeld - ElectronicFrame.Producer.heldMatrix) i j = (realizationDelta i j : ℂ) / 1000000000000 := by
  simp only [Source.realizedHeld, realizationDelta, ElectronicFrame.Producer.held_entry, Matrix.sub_apply, Int.cast_sub, sub_div]

theorem realized_delta_norm :
    ‖Source.realizedHeld - ElectronicFrame.Producer.heldMatrix‖ ≤ (242 : ℝ) / 1000000000000 := by
  have bound := Propagation.Dynamics.NativeDuration.matrixOperator_norm_le_entrySum
    (Source.realizedHeld - ElectronicFrame.Producer.heldMatrix)
  change ‖Source.realizedHeld - ElectronicFrame.Producer.heldMatrix‖ ≤ _ at bound
  have entries : (∑ i : Basis, ∑ j : Basis, ‖(Source.realizedHeld - ElectronicFrame.Producer.heldMatrix) i j‖) =
      (realizationDeltaMagnitude : ℝ) / 1000000000000 := by
    simp only [realizationDeltaMagnitude, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [realized_delta_entry]
    norm_num [norm_div, Complex.norm_intCast, Nat.cast_natAbs]
  rw [entries, realizationDeltaMagnitude_exact] at bound
  exact bound

theorem sourceUnitary_close_identity :
    ‖ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix - 1‖ < (372 : ℝ) / 10 ^ 12 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix)
    ElectronicFrame.Source.crossMatrix 1
  have residual := ElectronicFrame.Polar.projectionResidual_norm_le_gram
    ElectronicFrame.Source.crossMatrix ElectronicFrame.Source.crossMatrix_close
  have gram := ElectronicFrame.Source.gram_norm_small
  have cross := ElectronicFrame.Source.crossMatrix_norm_bound
  change ‖ElectronicFrame.Source.crossMatrix - ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix‖ ≤ _ at residual
  rw [norm_sub_rev] at residual
  linarith

theorem conjugation_displacement (U X : Matrix Basis Basis ℂ) (unitary : U ∈ Matrix.unitaryGroup Basis ℂ) :
    ‖U * X * star U - X‖ ≤ 2 * ‖U - 1‖ * ‖X‖ := by
  have unitNorm : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary unitary
  have factor : U * X * star U - X = (U - 1) * X * star U + X * star (U - 1) := by
    simp only [star_sub, star_one]
    noncomm_ring
  rw [factor]
  calc
    _ ≤ ‖(U - 1) * X * star U‖ + ‖X * star (U - 1)‖ := norm_add_le _ _
    _ ≤ ‖U - 1‖ * ‖X‖ * ‖star U‖ + ‖X‖ * ‖star (U - 1)‖ :=
      add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_mul_le _ _)
    _ = _ := by rw [norm_star, norm_star, unitNorm]; ring

def exactHeld : Matrix Basis Basis ℂ := ElectronicFrame.Source.heldStateTransport ElectronicFrame.Producer.heldMatrix
def realizationResidual : Matrix Basis Basis ℂ := Source.realizedHeld - exactHeld

theorem realized_held_reconstruction : Source.realizedHeld = exactHeld + realizationResidual := by
  simp only [realizationResidual, add_sub_cancel]

theorem realized_held_error : ‖realizationResidual‖ < (8 : ℝ) / 10 ^ 9 := by
  have movement := conjugation_displacement (ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix)
    ElectronicFrame.Producer.heldMatrix (ElectronicFrame.Polar.matrix_mem_unitary _ ElectronicFrame.Source.crossMatrix_close)
  have unitClose := sourceUnitary_close_identity
  have inputNorm := ElectronicFrame.Producer.heldMatrix_norm_le_ten
  have delta := realized_delta_norm
  have triangle := norm_sub_le_norm_sub_add_norm_sub Source.realizedHeld ElectronicFrame.Producer.heldMatrix exactHeld
  rw [norm_sub_rev ElectronicFrame.Producer.heldMatrix exactHeld] at triangle
  change ‖exactHeld - ElectronicFrame.Producer.heldMatrix‖ ≤ _ at movement
  have moveBound : ‖exactHeld - ElectronicFrame.Producer.heldMatrix‖ < (7440 : ℝ) / 10 ^ 12 := by
    have product : 2 * ‖ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix - 1‖ *
        ‖ElectronicFrame.Producer.heldMatrix‖ ≤ 20 * ‖ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix - 1‖ := by
      nlinarith [norm_nonneg (ElectronicFrame.Polar.matrix ElectronicFrame.Source.crossMatrix - 1)]
    linarith
  change ‖Source.realizedHeld - exactHeld‖ < _
  linarith

end
end LAlanine40K2025.HeldForce.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
