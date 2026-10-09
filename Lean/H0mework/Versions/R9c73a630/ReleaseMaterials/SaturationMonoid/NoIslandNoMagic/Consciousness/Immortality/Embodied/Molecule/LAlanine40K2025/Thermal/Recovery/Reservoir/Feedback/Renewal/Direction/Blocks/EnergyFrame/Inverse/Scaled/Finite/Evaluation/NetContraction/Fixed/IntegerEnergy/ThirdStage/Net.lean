import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.QuadraticSource
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators

def netStage03 : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub (fromTable elevenEnergyTable pairFin pairFin)
    (fromTable nineEnergyTable pairFin pairFin)

def netTable : IntTable 4 4 := ⟨
  ⟨#[
    (⟨#[15385467486249512760822924,-2527751034631194221723,-627526464699699991342525,2527751034631194170170],by decide⟩ : Vector Int 4),
    (⟨#[-2527751034631194221723,18918906110645070084356015,-2527751034631070364590,-627528147338256148448882],by decide⟩ : Vector Int 4),
    (⟨#[-627526464699699991342525,-2527751034631070364591,15385467486249508365037823,2527751034631070313042],by decide⟩ : Vector Int 4),
    (⟨#[2527751034631194170169,-627528147338256148448882,2527751034631070313043,18918906110645070091757690],by decide⟩ : Vector Int 4)
  ],by decide⟩,
  ⟨#[
    (⟨#[0,600363179737445512058,-11301206,-600363179737445543590],by decide⟩ : Vector Int 4),
    (⟨#[-600363179737445512058,0,-600363179737445620761,-27367],by decide⟩ : Vector Int 4),
    (⟨#[11301207,600363179737445620761,0,-600363179737445652292],by decide⟩ : Vector Int 4),
    (⟨#[600363179737445543590,27367,600363179737445652293,1],by decide⟩ : Vector Int 4)
  ],by decide⟩⟩

def bodyTable : IntTable 4 4 := ⟨
  ⟨#[
    (⟨#[11800122136501257127452399666,0,-6983,0],by decide⟩ : Vector Int 4),
    (⟨#[0,1596972871570020926595072582,0,-945],by decide⟩ : Vector Int 4),
    (⟨#[-6983,0,6615051960282739199226366091,0],by decide⟩ : Vector Int 4),
    (⟨#[0,-945,0,895249930669774520883670790],by decide⟩ : Vector Int 4)
  ],by decide⟩,
  ⟨#[
    (⟨#[0,0,-8831954927015797108357425370,0],by decide⟩ : Vector Int 4),
    (⟨#[0,0,0,-1195275121580679877097813425],by decide⟩ : Vector Int 4),
    (⟨#[8831954927015797108357425370,0,0,0],by decide⟩ : Vector Int 4),
    (⟨#[0,1195275121580679877097813425,0,0],by decide⟩ : Vector Int 4)
  ],by decide⟩⟩

theorem third_net_staged_literal :
    toTable netStage03 pairFin pairFin = netTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

theorem third_body_actual_literal :
    toTable (sourceOrdinaryBodyInt (0 : Basis) (3 : Basis)) pairFin pairFin =
      bodyTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

theorem third_energy_numerator_literal :
    (∑ i : Fin 2 × Fin 2,
      (multiply (fromTable netTable pairFin pairFin)
        (fromTable bodyTable pairFin pairFin)).re i i) =
      330476191522077830856882 := by decide +kernel

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
