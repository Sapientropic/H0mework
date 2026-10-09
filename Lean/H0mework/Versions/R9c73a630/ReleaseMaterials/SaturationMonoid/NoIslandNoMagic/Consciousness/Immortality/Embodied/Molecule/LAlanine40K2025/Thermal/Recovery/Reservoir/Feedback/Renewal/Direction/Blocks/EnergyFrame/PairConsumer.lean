import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.StateError

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def mappedPairUnitary (time : ℝ) : Matrix.unitaryGroup (Load.Source.PairController × Load.Source.PairController) ℂ :=
  Quantum.localUnitary (mappedPCUnitary time) (mappedPCUnitary time)*Exchange.exchangeUnitary (Native.sourceCoupling*time)

theorem mapped_pair_value (time : ℝ) :
    Quantum.localConjugation installedPCFrame installedPCFrame (Native.pairFlow time : JointMatrix Load.Source.PairController) =
      (mappedPairUnitary time : JointMatrix Load.Source.PairController) := by
  rw [Native.pairFlow_factor,mapped_pair_pulse]
  rfl

theorem actual_pair_native_error :
    ‖(mappedPairUnitary (Propagation.Producer.nativeClockStep : ℝ) : JointMatrix Load.Source.PairController)-
      (numericPairPulse (Propagation.Producer.nativeClockStep : ℝ) : JointMatrix Load.Source.PairController)‖ ≤
        (11/10^14 : ℝ) := by
  rw [← mapped_pair_value]
  apply (original_pair_pulse_error (Propagation.Producer.nativeClockStep : ℝ)).trans
  rw [Propagation.Producer.nativeClockStep_exact]
  norm_num

theorem actual_pair_joint_error (rho : JointMatrix Load.Source.PairController) :
    ‖Quantum.conjugation (mappedPairUnitary (Propagation.Producer.nativeClockStep : ℝ)) rho-
      Quantum.conjugation (numericPairPulse (Propagation.Producer.nativeClockStep : ℝ)) rho‖ ≤
        (22/10^14 : ℝ)*‖rho‖ := by
  have bound := conjugation_action_error (mappedPairUnitary (Propagation.Producer.nativeClockStep : ℝ))
    (numericPairPulse (Propagation.Producer.nativeClockStep : ℝ)) rho
  exact bound.trans (by nlinarith [actual_pair_native_error,norm_nonneg rho])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
