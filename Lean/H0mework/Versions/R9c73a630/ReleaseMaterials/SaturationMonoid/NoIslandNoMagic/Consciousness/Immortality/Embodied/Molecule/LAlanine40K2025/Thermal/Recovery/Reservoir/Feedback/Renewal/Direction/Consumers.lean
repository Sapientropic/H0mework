import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Runtime.Consumers

/-! # Direction and remaining-resource readouts of the already installed renewal current

The fixed facade supplies the actual eight-q material and nine-q execution. This bounded readout
exposes their source direction coordinate and near-return bound without changing the root program.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction

open Resource
noncomputable section

theorem actual_second_transfer_direction :
    type_of% (Runtime.face_factorizes Runtime.seed .next) ∧
    pcEnergyOf (suppliedBlock (Runtime.readNext Runtime.seed)) -
      pcEnergyOf (suppliedBlock (Runtime.currentState Runtime.seed.state.current)) =
      secondDirection := by
  refine ⟨Runtime.face_factorizes Runtime.seed .next, ?_⟩
  change supplyTransfer received = secondDirection
  exact second_transfer_exact

theorem actual_execution_remaining_bound :
    type_of% (Runtime.face_factorizes Runtime.afterFirst .next) ∧
    |donorRemainingOf (suppliedBlock (Runtime.readNext Runtime.afterFirst)) -
      donorRemainingOf (suppliedBlock receivedState)| ≤ returnBudget := by
  refine ⟨Runtime.face_factorizes Runtime.afterFirst .next, ?_⟩
  exact executed_remaining_return

/-- Exact numerical return mouth over original source contractions, not a gain premise. -/
theorem actual_positive_iff_source_direction :
    0 < pcEnergyOf (suppliedBlock (Runtime.readNext Runtime.seed)) -
      pcEnergyOf (suppliedBlock (Runtime.currentState Runtime.seed.state.current)) ↔
      0 < secondDirection := by
  rw [actual_second_transfer_direction.2]

theorem actual_negative_iff_source_direction :
    pcEnergyOf (suppliedBlock (Runtime.readNext Runtime.seed)) -
      pcEnergyOf (suppliedBlock (Runtime.currentState Runtime.seed.state.current)) < 0 ↔
      secondDirection < 0 := by
  rw [actual_second_transfer_direction.2]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
