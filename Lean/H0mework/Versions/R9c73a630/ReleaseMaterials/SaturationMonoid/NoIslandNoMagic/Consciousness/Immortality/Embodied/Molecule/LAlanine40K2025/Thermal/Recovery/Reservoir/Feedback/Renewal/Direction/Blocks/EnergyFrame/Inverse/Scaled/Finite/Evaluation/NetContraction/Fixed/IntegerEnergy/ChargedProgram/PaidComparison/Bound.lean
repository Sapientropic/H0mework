import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.PaidComparison.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

theorem paid_delta_source_error (slot : Fin 2) :
    ‖value (paidDeltaInt slot) -
      (sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) -
        sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide))‖ ≤
      (12/10^9 : ℝ) := by
  rw [paidDeltaInt,value_sub,paid_net_original]
  have first := source_ordinary_net_error (0 : Basis) (paidB slot) (paid_ordered slot)
  have third := source_ordinary_net_error (0 : Basis) (3 : Basis) (by decide)
  rw [third_source_net_matrix] at third
  change ‖value thirdNetInt - sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)‖ ≤ _ at third
  have rearrange :
      (value (sourceOrdinaryNetInt (0 : Basis) (paidB slot) (paid_ordered slot))-
        value thirdNetInt)-
      (sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot)-
        sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)) =
      (value (sourceOrdinaryNetInt (0 : Basis) (paidB slot) (paid_ordered slot))-
        sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot))-
      (value thirdNetInt-sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)) := by
    abel
  rw [rearrange]
  exact (norm_sub_le _ _).trans ((add_le_add first third).trans (by norm_num))

theorem paid_qdelta_centered_norm (slot : Fin 2) :
    ‖(sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot)-
        sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)) -
      paidCenter slot • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (112/10^9 : ℝ) := by
  have source := paid_delta_source_error slot
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot)-
      sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide))
    (value (paidDeltaInt slot))
    (paidCenter slot • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have sourceReverse :
      ‖(sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot)-
          sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide))-
        value (paidDeltaInt slot)‖ ≤ (12/10^9 : ℝ) := by
    simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add sourceReverse (paid_centered_norm slot)).trans (by norm_num))

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
