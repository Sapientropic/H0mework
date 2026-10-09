import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ElevenQuadraticLiteral
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

theorem literal_nine_quadratic_table :
    stagedFirstNineQuadraticTable=literalNineQuadraticTable :=
  int_table_ext literal_nine_quadratic_re literal_nine_quadratic_im

theorem literal_eleven_quadratic_table :
    stagedFirstElevenQuadraticTable=literalElevenQuadraticTable :=
  int_table_ext literal_eleven_quadratic_re literal_eleven_quadratic_im

theorem literal_nine_quadratic_original :
    fromTable literalNineQuadraticTable pairFin pairFin =
      multiply (multiply (adjoint sourceFirstNineSelectedInt) sourceFirstPCInt)
        sourceFirstNineSelectedInt := by
  rw [← literal_nine_quadratic_table]
  exact staged_first_nine_quadratic_original

theorem literal_eleven_quadratic_original :
    fromTable literalElevenQuadraticTable pairFin pairFin =
      multiply (multiply (adjoint sourceFirstElevenSelectedInt) sourceFirstPCInt)
        sourceFirstElevenSelectedInt := by
  rw [← literal_eleven_quadratic_table]
  exact staged_first_eleven_quadratic_original

def literalFirstNetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub (fromTable literalElevenQuadraticTable pairFin pairFin)
    (fromTable literalNineQuadraticTable pairFin pairFin)

theorem literal_first_net_original : literalFirstNetInt=sourceFirstNetInt := by
  rw [literalFirstNetInt,literal_eleven_quadratic_original,
    literal_nine_quadratic_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
