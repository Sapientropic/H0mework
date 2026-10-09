import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailMass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix.Norms.L2Operator
noncomputable section

theorem original_tail_action_budget :
    ‖LoadExecution.loadedNet‖*‖LoadExecution.receivedWord‖^2*(tailPairQ : ℝ) < (1/10^6 : ℝ) := by
  have mass : (tailPairQ : ℝ) ≤ (2/10^7 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 (le_of_lt original_tail_pair_bound)
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using h
  have nonnegative : (0 : ℝ) ≤ (tailPairQ : ℝ) := by
    exact_mod_cast original_tail_pair_nonnegative
  calc
    _ ≤ (2 : ℝ)*(1001/1000 : ℝ)^2*(2/10^7 : ℝ) := by
      gcongr
      · exact source_loaded_net_norm_two
      · exact source_received_word_norm_sharp
    _ < 1/10^6 := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
