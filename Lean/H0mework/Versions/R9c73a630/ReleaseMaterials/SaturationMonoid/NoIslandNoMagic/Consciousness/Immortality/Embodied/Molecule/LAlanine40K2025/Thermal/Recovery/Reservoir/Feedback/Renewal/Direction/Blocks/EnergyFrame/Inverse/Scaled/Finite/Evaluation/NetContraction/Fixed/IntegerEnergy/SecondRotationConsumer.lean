import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondRotationCertificate
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem second_literal_free_actual :
    ‖value (fromTable literalSecondFree nativeFin nativeFin)-
      qvalue (qkron (onePCQ (0 : Basis) (2 : Basis) (by decide))
        freeEnvironmentQ)‖ ≤ (1/10^25 : ℝ) := by
  rw [second_free_original]
  exact ordinary_free_quantize_error 0 2 (by decide)

theorem second_literal_rotated_actual :
    ‖value (fromTable literalSecondRotatedPlus nativeFin nativeFin)-
      qvalue (ordinaryRootRotatedQ (0 : Basis) (2 : Basis) (by decide))‖ ≤
        (1/10^18 : ℝ) ∧
    ‖value (fromTable literalSecondRotatedMinus nativeFin nativeFin)-
      qvalue (ordinaryComplementRotatedQ (0 : Basis) (2 : Basis) (by decide))‖ ≤
        (1/10^18 : ℝ) := by
  rw [second_rotated_original.1,second_rotated_original.2]
  exact source_ordinary_rotated_errors 0 2 (by decide)

theorem second_literal_rotated_distinct :
    (literalSecondRotatedPlusRe.get (0 : Fin 8)).get (0 : Fin 8) ≠
      (literalSecondRotatedMinusRe.get (0 : Fin 8)).get (0 : Fin 8) := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
