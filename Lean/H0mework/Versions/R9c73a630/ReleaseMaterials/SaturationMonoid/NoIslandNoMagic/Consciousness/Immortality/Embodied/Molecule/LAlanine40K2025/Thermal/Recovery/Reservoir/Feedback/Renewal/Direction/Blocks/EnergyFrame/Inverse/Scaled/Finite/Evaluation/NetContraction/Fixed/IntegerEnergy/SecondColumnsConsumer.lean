import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondColumnsCertificate
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ColumnsLiteral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem literal_second_columns_not_first :
    literalSecondColumnsRe.get (2 : Fin 64) ≠
      literalFirstColumnsRe.get (2 : Fin 64) := by decide +kernel

theorem literal_second_columns_actual :
    ‖value (fromTable literalSecondColumnsTable pointerFin nativeFin) -
      sourceColumns (s((0 : Basis),2))
        (ordinaryFullEquiv (0 : Basis) 2 (by decide)) ordinaryInjection‖ ≤
      (3/10^16 : ℝ) := by
  rw [literal_second_columns_original]
  exact source_ordinary_columns_actual_error 0 2 (by decide)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
