import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Frame

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem original_PC_polynomial_error :
    ‖Quantum.conjugation installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ) : Matrix PairController PairController ℂ)-
      Phase.pcPolynomial‖ ≤ (56/10^15 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ) : Matrix PairController PairController ℂ))
    (numericPCFree : Matrix PairController PairController ℂ) Phase.pcPolynomial
  have source : ‖Quantum.conjugation installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ) : Matrix PairController PairController ℂ)-
      (numericPCFree : Matrix PairController PairController ℂ)‖ ≤ (55/10^15 : ℝ) := actual_native_PC_error
  linarith [Phase.pc_polynomial_error]

def fullLoadPolynomial : Current.FullJoint := localMatrix Actions.loadPolynomial Phase.pcPolynomial

def calculatedLoad : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Actions.reframeUnitary Supply.installedFullFrame (Current.loadPulse (nativeClockStep : ℝ))

theorem original_full_load_polynomial_error :
    ‖(calculatedLoad : Current.FullJoint)-fullLoadPolynomial‖ ≤ (113/10^15 : ℝ) := by
  rw [calculatedLoad,Actions.reframe_value,Supply.installed_full_frame_local,Current.loadPulse,local_lift_matrix_covariance]
  exact (local_matrix_error (Actions.reframeUnitary installedLoadFrame (loadUnitary (nativeClockStep : ℝ)))
    (Actions.reframeUnitary installedPCFrame (Native.freePCUnitary (nativeClockStep : ℝ)))
    Actions.loadPolynomial Phase.pcPolynomial (56/10^15) (56/10^15)
    Actions.original_load_polynomial_error original_PC_polynomial_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
