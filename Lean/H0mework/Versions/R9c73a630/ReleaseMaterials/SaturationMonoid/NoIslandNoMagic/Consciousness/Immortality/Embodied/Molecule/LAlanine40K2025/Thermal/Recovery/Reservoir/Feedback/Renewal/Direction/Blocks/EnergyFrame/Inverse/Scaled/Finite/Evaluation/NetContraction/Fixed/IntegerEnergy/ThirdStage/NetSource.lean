import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.Net
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondGainConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators

private theorem third_nine_energy_matrix :
    multiply (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)))
      (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) =
      fromTable nineEnergyTable pairFin pairFin := by
  calc
    _ = fromTable (toTable (multiply (multiply
      (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)))
      (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide))) pairFin pairFin)
      pairFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_energy_actual_literal]

private theorem third_eleven_energy_matrix :
    multiply (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)))
      (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) =
      fromTable elevenEnergyTable pairFin pairFin := by
  calc
    _ = fromTable (toTable (multiply (multiply
      (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)))
      (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide))) pairFin pairFin)
      pairFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [third_eleven_energy_actual_literal]

private theorem third_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (3 : Basis) (by decide) =
      fromTable netTable pairFin pairFin := by
  have staged : sourceOrdinaryNetInt (0 : Basis) (3 : Basis) (by decide) =
      netStage03 := by
    unfold sourceOrdinaryNetInt netStage03
    rw [third_eleven_energy_matrix, third_nine_energy_matrix]
  calc
    _ = netStage03 := staged
    _ = fromTable (toTable netStage03 pairFin pairFin) pairFin pairFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_net_staged_literal]

theorem third_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (3 : Basis) (by decide) =
      fromTable netTable pairFin pairFin := third_net_matrix

private theorem third_body_matrix :
    sourceOrdinaryBodyInt (0 : Basis) (3 : Basis) =
      fromTable bodyTable pairFin pairFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryBodyInt (0 : Basis) (3 : Basis)) pairFin pairFin)
      pairFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [third_body_actual_literal]

/-- The original address, not a diagnostic table, owns this complete integer gain. -/
theorem third_original_integer_gain :
    sourceOrdinaryGainNumeratorInt (0 : Basis) (3 : Basis) (by decide) =
      330476191522077830856882 := by
  rw [sourceOrdinaryGainNumeratorInt, sourceOrdinaryEnergyProductInt,
    third_net_matrix, third_body_matrix]
  exact third_energy_numerator_literal

theorem third_original_gain_positive :
    0 < smallGainQ (s((0 : Basis),(3 : Basis))) := by
  have err := source_ordinary_integer_gain_error (0 : Basis) (3 : Basis) (by decide)
  have sourceMargin : (3/10^7 : ℝ) <
      (sourceOrdinaryGainIntQ (0 : Basis) (3 : Basis) (by decide) : ℝ) := by
    rw [sourceOrdinaryGainIntQ, third_original_integer_gain]
    norm_num [scale]
  have bound := (abs_le.mp err).2
  have positive : (0 : ℝ) < (smallGainQ (s((0 : Basis),(3 : Basis))) : ℝ) := by
    linarith only [sourceMargin, bound]
  exact_mod_cast positive

theorem third_gain_distinct_from_first :
    sourceOrdinaryGainNumeratorInt (0 : Basis) (3 : Basis) (by decide) ≠
      sourceOrdinaryGainNumeratorInt (0 : Basis) (1 : Basis) (by decide) := by
  rw [third_original_integer_gain]
  change 330476191522077830856882 ≠ sourceFirstGainNumeratorInt
  rw [source_first_gain_exact]
  decide

theorem third_gain_distinct_from_second :
    sourceOrdinaryGainNumeratorInt (0 : Basis) (3 : Basis) (by decide) ≠
      sourceOrdinaryGainNumeratorInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [third_original_integer_gain, source_second_gain_exact]
  decide

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
