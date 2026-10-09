import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.PaidComparison.Bound

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

theorem paid_qdelta_lower (slot : Fin 2) :
    (paidCenter slot-112/10^9) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot)-
        sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) := by
  apply hermitian_lower_from_center
  · exact (ordinary_qnet_hermitian (0 : Basis) (paidB slot) (paid_ordered slot)).sub
      (ordinary_qnet_hermitian (0 : Basis) (3 : Basis) (by decide))
  · exact paid_qdelta_centered_norm slot

theorem paid_qnet_dominates_third (slot : Fin 2) :
    sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)+
      (paidCenter slot-112/10^9) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) := by
  have h := paid_qdelta_lower slot
  calc
    sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)+
        (paidCenter slot-112/10^9) •
          (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
        (paidCenter slot-112/10^9) • 1+
          sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) := by abel
    _ ≤ (sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot)-
          sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide))+
        sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) :=
      add_le_add_left h _
    _ = sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) := by abel

theorem paid_qnet_uniform_floor (slot : Fin 2) :
    (16/10^6 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) := by
  have third := third_qnet_strict_floor
  have raised := paid_qnet_dominates_third slot
  have sum : ((138/10^7 : ℝ)+(paidCenter slot-112/10^9)) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) := by
    rw [add_smul]
    exact (add_le_add_left third _).trans raised
  have compare : (16/10^6 : ℝ) ≤
      (138/10^7 : ℝ)+(paidCenter slot-112/10^9) := by
    fin_cases slot <;> norm_num [paidCenter]
  exact (smul_le_smul_of_nonneg_right compare (zero_le_one :
    (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)).trans sum

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
