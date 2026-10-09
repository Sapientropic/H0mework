import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Suffix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paid original flow responds through its actual Hamiltonian commutator. -/
theorem flow_observable_response (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (time : ℝ) (O : ControllerJoint ι) :
    ‖Quantum.conjugation (star (flowUnitary H gap V hH hV time)) O-O‖ ≤
      |time| * ‖totalHamiltonian H gap V*O-O*totalHamiltonian H gap V‖ := by
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := -time)
    (fun t _ => (coupledNext_hasDerivAt H gap V hH hV t O).hasDerivWithinAt)
    (fun t _ => by
      rw [coupledNext,conjugation_norm,norm_smul,norm_neg,Complex.norm_I,one_mul])
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ 0) (Set.mem_univ (-time))
  simpa only [Quantum.conjugation_apply,coupledNext,flowUnitary_neg,flowUnitary_zero,Unitary.conjStarAlgAut_apply,OneMemClass.coe_one,star_one,Matrix.one_mul,Matrix.mul_one,
    sub_zero,Real.norm_eq_abs,abs_neg,mul_comm] using estimate

theorem bare_system_commutator (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι) :
    totalHamiltonian H gap V*Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ)-
      Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ)*totalHamiltonian H gap V=
    V*Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ)-
      Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ)*V := by
  have commute := (one_tensor_commutes H (controllerHamiltonian gap)).eq
  simp only [totalHamiltonian,bareHamiltonian,add_mul,mul_add]
  rw [commute]
  abel

theorem load_PC_response (time : ℝ) :
    ‖Quantum.conjugation (star (Load.Source.loadUnitary time))
      (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ))-
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
    |time| * ‖Load.Source.loadInteraction*Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)-
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)*Load.Source.loadInteraction‖ := by
  have paid := flow_observable_response Powered.Producer.poweredTotalHamiltonian 2 Load.Source.loadInteraction
    Powered.Producer.poweredTotalHamiltonian_hermitian Load.Source.loadInteraction_hermitian time
    (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ))
  rw [bare_system_commutator] at paid
  exact paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
