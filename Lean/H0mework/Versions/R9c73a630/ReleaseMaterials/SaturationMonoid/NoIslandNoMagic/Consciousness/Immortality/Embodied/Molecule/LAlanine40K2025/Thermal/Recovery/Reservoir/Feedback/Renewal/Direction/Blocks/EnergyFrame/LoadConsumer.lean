import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.LoadFlow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Propagation.Interface Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def mappedLoadUnitary (time : ℝ) : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  installedLoadFrame*loadUnitary time*star installedLoadFrame

def numericLoadUnitary (time : ℝ) : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  ⟨hamiltonianFlow numericLoadHamiltonian time,hamiltonianFlow_unitary _ actual_numeric_load_hermitian time⟩

theorem mapped_load_value (time : ℝ) : (mappedLoadUnitary time : LoadedJoint) =
    Quantum.conjugation installedLoadFrame (loadUnitary time : LoadedJoint) := by
  simp only [mappedLoadUnitary,Submonoid.coe_mul,Unitary.coe_star,Quantum.conjugation_apply]

theorem original_load_native_error :
    ‖(mappedLoadUnitary (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint)-
      (numericLoadUnitary (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint)‖ ≤ (55/10^15 : ℝ) := by
  rw [mapped_load_value]
  have bound := actual_load_action_error (Propagation.Producer.nativeClockStep : ℝ)
  apply bound.trans
  rw [Propagation.Producer.nativeClockStep_exact]
  norm_num

theorem original_load_joint_error (rho : LoadedJoint) :
    ‖Quantum.conjugation (mappedLoadUnitary (Propagation.Producer.nativeClockStep : ℝ)) rho-
      Quantum.conjugation (numericLoadUnitary (Propagation.Producer.nativeClockStep : ℝ)) rho‖ ≤
        (11/10^14 : ℝ)*‖rho‖ := by
  have bound := conjugation_action_error (mappedLoadUnitary (Propagation.Producer.nativeClockStep : ℝ))
    (numericLoadUnitary (Propagation.Producer.nativeClockStep : ℝ)) rho
  exact bound.trans (by nlinarith [original_load_native_error,norm_nonneg rho])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
