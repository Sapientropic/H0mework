import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.BodyConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ElevenConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source
open scoped BigOperators

def stagedFirstGainNumeratorInt : Int := Id.run do
  let actions := (literalFirstNineTable,literalFirstElevenTable)
  let nine := fromTable actions.1 pointerFin nativeFin
  let eleven := fromTable actions.2 pointerFin nativeFin
  let pcTable := toTable literalFirstPCInt pointerFin pointerFin
  let pc := fromTable pcTable pointerFin pointerFin
  let bodyTable := literalFirstBodyTable
  let body := fromTable bodyTable pairFin pairFin
  let nineTable := toTable (submatrix nine id chargedInjection) pointerFin pairFin
  let elevenTable := toTable (submatrix eleven id chargedInjection) pointerFin pairFin
  let nineSelected := fromTable nineTable pointerFin pairFin
  let elevenSelected := fromTable elevenTable pointerFin pairFin
  let nineWeightedTable := toTable (multiply (adjoint nineSelected) pc) pairFin pointerFin
  let elevenWeightedTable := toTable (multiply (adjoint elevenSelected) pc) pairFin pointerFin
  let nineWeighted := fromTable nineWeightedTable pairFin pointerFin
  let elevenWeighted := fromTable elevenWeightedTable pairFin pointerFin
  let nineEnergyTable := toTable (multiply nineWeighted nineSelected) pairFin pairFin
  let elevenEnergyTable := toTable (multiply elevenWeighted elevenSelected) pairFin pairFin
  let nineEnergy := fromTable nineEnergyTable pairFin pairFin
  let elevenEnergy := fromTable elevenEnergyTable pairFin pairFin
  let netTable := toTable (sub elevenEnergy nineEnergy) pairFin pairFin
  let net := fromTable netTable pairFin pairFin
  let energyProduct := multiply net body
  return ∑ i : Fin 2 × Fin 2, energyProduct.re i i

theorem staged_first_gain_original :
    stagedFirstGainNumeratorInt=sourceFirstGainNumeratorInt := by
  simp [stagedFirstGainNumeratorInt,from_to_table,
    sourceFirstGainNumeratorInt,sourceFirstEnergyProductInt,sourceFirstNetInt,
    sourceFirstNineSelectedInt,sourceFirstElevenSelectedInt]
  rw [literal_first_nine_original,literal_first_eleven_original,
    literal_first_pc_original,literal_first_body_original]

def stagedFirstGainIntQ : ℚ := (stagedFirstGainNumeratorInt : ℚ) / (scale : ℚ)

theorem staged_first_gain_q_original : stagedFirstGainIntQ=sourceFirstGainIntQ := by
  rw [stagedFirstGainIntQ,staged_first_gain_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
