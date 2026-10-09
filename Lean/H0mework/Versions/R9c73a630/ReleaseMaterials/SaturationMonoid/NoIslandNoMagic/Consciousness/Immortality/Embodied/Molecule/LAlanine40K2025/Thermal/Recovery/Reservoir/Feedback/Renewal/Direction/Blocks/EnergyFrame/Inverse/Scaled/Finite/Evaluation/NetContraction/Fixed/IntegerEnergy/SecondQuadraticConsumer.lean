import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondNineQuadraticLiteral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondElevenQuadraticLiteral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

theorem literal_second_nine_quadratic_table :
    stagedSecondNineQuadraticTable = literalSecondNineQuadraticTable :=
  int_table_ext literal_second_nine_quadratic_re literal_second_nine_quadratic_im

theorem literal_second_eleven_quadratic_table :
    stagedSecondElevenQuadraticTable = literalSecondElevenQuadraticTable :=
  int_table_ext literal_second_eleven_quadratic_re literal_second_eleven_quadratic_im

theorem literal_second_nine_quadratic_original :
    fromTable literalSecondNineQuadraticTable pairFin pairFin =
      multiply
        (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (2 : Basis)
          (by decide))) (sourceOrdinaryPCInt (0 : Basis) (2 : Basis)))
        (sourceOrdinaryNineSelectedInt (0 : Basis) (2 : Basis) (by decide)) := by
  rw [← literal_second_nine_quadratic_table]
  exact staged_second_nine_quadratic_original

theorem literal_second_eleven_quadratic_original :
    fromTable literalSecondElevenQuadraticTable pairFin pairFin =
      multiply
        (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (2 : Basis)
          (by decide))) (sourceOrdinaryPCInt (0 : Basis) (2 : Basis)))
        (sourceOrdinaryElevenSelectedInt (0 : Basis) (2 : Basis) (by decide)) := by
  rw [← literal_second_eleven_quadratic_table]
  exact staged_second_eleven_quadratic_original

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
