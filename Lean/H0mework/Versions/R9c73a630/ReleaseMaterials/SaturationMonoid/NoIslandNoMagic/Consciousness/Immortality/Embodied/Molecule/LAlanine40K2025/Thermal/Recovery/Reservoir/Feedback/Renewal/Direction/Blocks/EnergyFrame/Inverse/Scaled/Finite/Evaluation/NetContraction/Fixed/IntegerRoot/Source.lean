import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerRoot.Core
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem source_first_plus_factor_entries :
    ∀ i j : Fin 8,
      |((SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).1.realPart i j)|+
      |((SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).1.imagPart i j)| ≤
      (1 : ℚ) := by
  decide +kernel

theorem source_first_minus_factor_entries :
    ∀ i j : Fin 8,
      |((SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).2.realPart i j)|+
      |((SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).2.imagPart i j)| ≤
      (1 : ℚ) := by
  decide +kernel

theorem source_donor_plus_factor_entries :
    ∀ i j : Fin 4,
      |SquareRoot.Full.paidDonor.1.realPart i j|+
      |SquareRoot.Full.paidDonor.1.imagPart i j| ≤ (1 : ℚ) := by
  decide +kernel

theorem source_donor_minus_factor_entries :
    ∀ i j : Fin 4,
      |SquareRoot.Full.paidDonor.2.realPart i j|+
      |SquareRoot.Full.paidDonor.2.imagPart i j| ≤ (1 : ℚ) := by
  decide +kernel

theorem source_first_ordinary_root_int_error :
    ‖value (submatrix
        (gramInt (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).1)
        tripleIndex tripleIndex)-
      qvalue (rootOrdinaryQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^25 : ℝ) := by
  let G := (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).1
  change ‖value (submatrix (gramInt G) tripleIndex tripleIndex)-
    qvalue ((rootGramQ G).submatrix tripleIndex tripleIndex)‖ ≤ _
  exact gram_int_reindex_error G tripleIndex (by decide) source_first_plus_factor_entries

theorem source_first_ordinary_complement_int_error :
    ‖value (submatrix
        (gramInt (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).2)
        tripleIndex tripleIndex)-
      qvalue (complementOrdinaryQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^25 : ℝ) := by
  let G := (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).2
  change ‖value (submatrix (gramInt G) tripleIndex tripleIndex)-
    qvalue ((rootGramQ G).submatrix tripleIndex tripleIndex)‖ ≤ _
  exact gram_int_reindex_error G tripleIndex (by decide) source_first_minus_factor_entries

theorem source_donor_root_int_error :
    ‖value (submatrix (gramInt SquareRoot.Full.paidDonor.1)
        SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)-qvalue rootDonorQ‖ ≤
      (1/10^25 : ℝ) := by
  let G := SquareRoot.Full.paidDonor.1
  change ‖value (submatrix (gramInt G) SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)-
    qvalue ((rootGramQ G).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)‖ ≤ _
  exact gram_int_reindex_error G SquareRoot.Full.pairIndex (by decide)
    source_donor_plus_factor_entries

theorem source_donor_complement_int_error :
    ‖value (submatrix (gramInt SquareRoot.Full.paidDonor.2)
        SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)-qvalue complementDonorQ‖ ≤
      (1/10^25 : ℝ) := by
  let G := SquareRoot.Full.paidDonor.2
  change ‖value (submatrix (gramInt G) SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)-
    qvalue ((rootGramQ G).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)‖ ≤ _
  exact gram_int_reindex_error G SquareRoot.Full.pairIndex (by decide)
    source_donor_minus_factor_entries


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
