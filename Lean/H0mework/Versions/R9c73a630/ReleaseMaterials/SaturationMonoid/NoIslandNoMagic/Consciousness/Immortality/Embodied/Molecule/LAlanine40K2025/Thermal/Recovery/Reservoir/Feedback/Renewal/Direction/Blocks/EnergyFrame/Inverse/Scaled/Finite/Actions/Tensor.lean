import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Product
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Free

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def reframeUnitary (W U : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup ι ℂ := W*U*star W

omit [Fintype κ] [DecidableEq κ] in
theorem reframe_value (W U : Matrix.unitaryGroup ι ℂ) :
    (reframeUnitary W U : Matrix ι ι ℂ)=Quantum.conjugation W (U : Matrix ι ι ℂ) := rfl

omit [Fintype κ] [DecidableEq κ] in
theorem reframe_mul (W U V : Matrix.unitaryGroup ι ℂ) :
    reframeUnitary W (U*V)=reframeUnitary W U*reframeUnitary W V := by
  simp only [reframeUnitary,mul_assoc,← mul_assoc (star W) W,Unitary.star_mul_self,one_mul]

theorem reframe_spectator (W U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    (reframeUnitary (spectatorFrame W) (Load.Quantum.localUnitary U V) : Matrix (ι × κ) (ι × κ) ℂ)=
      Matrix.kronecker (reframeUnitary W U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) := by
  rw [reframe_value]
  exact spectator_conjugation W (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)

theorem approximated_tensor_error [Nonempty ι] [Nonempty κ]
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (d e : ℝ)
    (left : ‖(U : Matrix ι ι ℂ)-A‖ ≤ d) (right : ‖(V : Matrix κ κ ℂ)-B‖ ≤ e) :
    ‖Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)-Matrix.kronecker A B‖ ≤ d+(1+d)*e := by
  have split : Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)-Matrix.kronecker A B=
      Matrix.kronecker ((U : Matrix ι ι ℂ)-A) (V : Matrix κ κ ℂ)+Matrix.kronecker A ((V : Matrix κ κ ℂ)-B) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.add_apply,Matrix.sub_apply]
    ring
  rw [split]
  apply (norm_add_le _ _).trans
  apply (add_le_add (kronecker_norm_le _ _) (kronecker_norm_le _ _)).trans
  rw [CStarRing.norm_coe_unitary,mul_one]
  apply add_le_add left
  exact mul_le_mul (Input.approximated_unitary_norm U A d left) right (norm_nonneg _)
    (by linarith [norm_nonneg A,Input.approximated_unitary_norm U A d left])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
