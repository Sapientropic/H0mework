import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondBodyStage
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def literalSecondBodyRe : Vector (Vector Int 4) 4 := ⟨#[
  (⟨#[11869453934258438524599310877,0,5328,0],by decide⟩ : Vector Int 4),
  (⟨#[0,1606355910056792619561462251,0,721],by decide⟩ : Vector Int 4),
  (⟨#[5328,0,6738752585338123133670585040,0],by decide⟩ : Vector Int 4),
  (⟨#[0,721,0,911990989798190934208657323],by decide⟩ : Vector Int 4)
  ],by decide⟩

theorem literal_second_body_re :
    stagedSecondBodyTable.re = literalSecondBodyRe := by decide +kernel

def literalSecondBodyIm : Vector (Vector Int 4) 4 := ⟨#[
  (⟨#[0,0,-8739346145299629610788214786,0],by decide⟩ : Vector Int 4),
  (⟨#[0,0,0,-1182741885876924710003996305],by decide⟩ : Vector Int 4),
  (⟨#[8739346145299629610788214786,0,0,0],by decide⟩ : Vector Int 4),
  (⟨#[0,1182741885876924710003996305,0,0],by decide⟩ : Vector Int 4)
  ],by decide⟩

theorem literal_second_body_im :
    stagedSecondBodyTable.im = literalSecondBodyIm := by decide +kernel

def literalSecondBodyTable : IntTable 4 4 :=
  ⟨literalSecondBodyRe,literalSecondBodyIm⟩

theorem literal_second_body_table :
    stagedSecondBodyTable = literalSecondBodyTable :=
  int_table_ext literal_second_body_re literal_second_body_im

theorem literal_second_body_original :
    fromTable literalSecondBodyTable pairFin pairFin =
      sourceOrdinaryBodyInt (0 : Basis) (2 : Basis) := by
  rw [← literal_second_body_table]
  exact staged_second_body_original

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
