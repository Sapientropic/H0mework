import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.WeightedSource
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def assembleRows (U L : MatrixInt OrdinaryFull (Fin 2 × Fin 2)) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  ⟨fun i j => match i with | .inl x => U.re x j | .inr x => L.re x j,
   fun i j => match i with | .inl x => U.im x j | .inr x => L.im x j⟩

def assembleColumns (U L : MatrixInt (Fin 2 × Fin 2) OrdinaryFull) :
    MatrixInt (Fin 2 × Fin 2) (OrdinaryFull ⊕ OrdinaryFull) :=
  ⟨fun i j => match j with | .inl x => U.re i x | .inr x => L.re i x,
   fun i j => match j with | .inl x => U.im i x | .inr x => L.im i x⟩

def nineSelectedStage03 : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  assembleRows
    (submatrix (fromTable upperNineTable ordinaryFullFin nativeFin) id chargedInjection)
    (submatrix (fromTable lowerNineTable ordinaryFullFin nativeFin) id chargedInjection)

def elevenSelectedStage03 : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  assembleRows
    (submatrix (fromTable upperElevenTable ordinaryFullFin nativeFin) id chargedInjection)
    (submatrix (fromTable lowerElevenTable ordinaryFullFin nativeFin) id chargedInjection)

def nineWeightedStage03 : MatrixInt (Fin 2 × Fin 2) (OrdinaryFull ⊕ OrdinaryFull) :=
  assembleColumns
    (fromTable upperNineWeightedTable pairFin ordinaryFullFin)
    (fromTable lowerNineWeightedTable pairFin ordinaryFullFin)

def elevenWeightedStage03 : MatrixInt (Fin 2 × Fin 2) (OrdinaryFull ⊕ OrdinaryFull) :=
  assembleColumns
    (fromTable upperElevenWeightedTable pairFin ordinaryFullFin)
    (fromTable lowerElevenWeightedTable pairFin ordinaryFullFin)

def nineEnergyStage03 := multiply nineWeightedStage03 nineSelectedStage03
def elevenEnergyStage03 := multiply elevenWeightedStage03 elevenSelectedStage03

def nineEnergyTable : IntTable 4 4 := ⟨
  ⟨#[
    (⟨#[9280256616618851859289795628399,5972558987184191384897,1254966772958186231682008,-5972558987183765421848],by decide⟩ : Vector Int 4),
    (⟨#[5972558987184191384897,9280258470472230575268985255600,5972558987183731788874,1254959634235969099329993],by decide⟩ : Vector Int 4),
    (⟨#[1254966772958186231682008,5972558987183731788875,9280256616618851859303595401862,-5972558987183305825825],by decide⟩ : Vector Int 4),
    (⟨#[-5972558987183765421847,1254959634235969099329993,-5972558987183305825825,9280258470472230575269312988968],by decide⟩ : Vector Int 4)
  ],by decide⟩,
  ⟨#[
    (⟨#[0,-4222239761323862106868,35699002,4222239761323860630490],by decide⟩ : Vector Int 4),
    (⟨#[4222239761323862106868,0,4222239761323862763900,778650],by decide⟩ : Vector Int 4),
    (⟨#[-35699002,-4222239761323862763900,0,4222239761323861287529],by decide⟩ : Vector Int 4),
    (⟨#[-4222239761323860630490,-778650,-4222239761323861287529,-1],by decide⟩ : Vector Int 4)
  ],by decide⟩⟩

def elevenEnergyTable : IntTable 4 4 := ⟨
  ⟨#[
    (⟨#[9280272002086338108802556451323,3444807952552997163174,627440308258486240339483,-3444807952552571251678],by decide⟩ : Vector Int 4),
    (⟨#[3444807952552997163174,9280277389378341220339069611615,3444807952552661424284,627431486897712950881111],by decide⟩ : Vector Int 4),
    (⟨#[627440308258486240339483,3444807952552661424284,9280272002086338108811960439685,-3444807952552235512783],by decide⟩ : Vector Int 4),
    (⟨#[-3444807952552571251678,627431486897712950881111,-3444807952552235512782,9280277389378341220339404746658],by decide⟩ : Vector Int 4)
  ],by decide⟩,
  ⟨#[
    (⟨#[0,-3621876581586416594810,24397796,3621876581586415086900],by decide⟩ : Vector Int 4),
    (⟨#[3621876581586416594810,0,3621876581586417143139,751283],by decide⟩ : Vector Int 4),
    (⟨#[-24397795,-3621876581586417143139,0,3621876581586415635237],by decide⟩ : Vector Int 4),
    (⟨#[-3621876581586415086900,-751283,-3621876581586415635236,0],by decide⟩ : Vector Int 4)
  ],by decide⟩⟩

theorem third_nineEnergy_staged_literal :
    toTable nineEnergyStage03 pairFin pairFin = nineEnergyTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

theorem third_elevenEnergy_staged_literal :
    toTable elevenEnergyStage03 pairFin pairFin = elevenEnergyTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
