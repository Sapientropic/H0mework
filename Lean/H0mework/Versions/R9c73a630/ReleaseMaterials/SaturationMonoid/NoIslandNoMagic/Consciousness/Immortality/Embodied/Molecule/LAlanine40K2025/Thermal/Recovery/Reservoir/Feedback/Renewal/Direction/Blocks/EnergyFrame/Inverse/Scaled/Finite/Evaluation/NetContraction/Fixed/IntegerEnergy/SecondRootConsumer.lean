import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondRootCertificate
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem second_literal_roots_actual :
    ‖value (fromTable literalSecondRootPlus nativeFin nativeFin)-
      SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.orbitPCE (0 : Basis) 2)
        (Scaled.Order.orbitPCE (0 : Basis) 2)‖ ≤ (1/10^25 : ℝ) ∧
    ‖value (fromTable literalSecondRootMinus nativeFin nativeFin)-
      SquareRoot.Full.sourceComplement.submatrix
        (Scaled.Order.orbitPCE (0 : Basis) 2)
        (Scaled.Order.orbitPCE (0 : Basis) 2)‖ ≤ (1/10^25 : ℝ) := by
  rw [second_roots_original.1,second_roots_original.2]
  exact source_ordinary_roots_actual 0 2 (by decide)

theorem second_literal_roots_distinct :
    (literalSecondRootPlusRe.get (0 : Fin 8)).get (0 : Fin 8) ≠
      (literalSecondRootMinusRe.get (0 : Fin 8)).get (0 : Fin 8) := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
