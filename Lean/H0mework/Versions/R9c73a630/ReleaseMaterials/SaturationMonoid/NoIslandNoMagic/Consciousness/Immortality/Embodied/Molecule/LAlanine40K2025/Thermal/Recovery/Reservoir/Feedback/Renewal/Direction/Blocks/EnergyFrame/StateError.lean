import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Pulse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conjugation_action_error (U V : Matrix.unitaryGroup ι ℂ) (rho : Matrix ι ι ℂ) :
    ‖Quantum.conjugation U rho-Quantum.conjugation V rho‖ ≤ 2*‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖*‖rho‖ := by
  have split : Quantum.conjugation U rho-Quantum.conjugation V rho =
      ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ))*rho*star (U : Matrix ι ι ℂ)+
      (V : Matrix ι ι ℂ)*rho*star ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)) := by
    simp only [Quantum.conjugation_apply,star_sub]
    noncomm_ring
  rw [split]
  have first : ‖((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ))*rho*star (U : Matrix ι ι ℂ)‖ ≤
      ‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖*‖rho‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.property)]
    exact norm_mul_le _ _
  have second : ‖(V : Matrix ι ι ℂ)*rho*star ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ))‖ ≤
      ‖rho‖*‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖ := by
    rw [Matrix.mul_assoc,CStarRing.norm_coe_unitary_mul]
    simpa only [norm_star] using norm_mul_le rho (star ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)))
  exact (norm_add_le _ _).trans (by linarith)

/-- Incoming correlations remain arbitrary; action and input errors are separately paid. -/
theorem action_and_input_error (U V : Matrix.unitaryGroup ι ℂ) (rho sigma : Matrix ι ι ℂ) :
    ‖Quantum.conjugation U rho-Quantum.conjugation V sigma‖ ≤
      ‖rho-sigma‖+2*‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖*‖sigma‖ := by
  have split : Quantum.conjugation U rho-Quantum.conjugation V sigma =
      Quantum.conjugation U (rho-sigma)+(Quantum.conjugation U sigma-Quantum.conjugation V sigma) := by
    rw [map_sub]
    abel
  rw [split]
  have exactInput : ‖Quantum.conjugation U (rho-sigma)‖ = ‖rho-sigma‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) _
  exact (norm_add_le _ _).trans (by rw [exactInput]; exact add_le_add le_rfl (conjugation_action_error U V sigma))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
