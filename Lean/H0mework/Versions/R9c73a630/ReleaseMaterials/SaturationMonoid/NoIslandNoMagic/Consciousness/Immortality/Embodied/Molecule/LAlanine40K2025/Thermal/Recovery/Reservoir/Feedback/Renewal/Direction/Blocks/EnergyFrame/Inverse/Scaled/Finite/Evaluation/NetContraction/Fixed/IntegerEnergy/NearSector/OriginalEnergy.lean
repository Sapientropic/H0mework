import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.Mass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.OriginalEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.PaidComparison.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A004.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A005.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A102.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A103.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A104.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A105.Spectrum
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

/-! Complete original near-sector gain, with its own nine source numerators. -/

def nearFloorQ (k : Fin 9) : ℚ :=
  ![16/10^6,16/10^6,138/10^7,13389/10^9,13355/10^9,15807/10^9,
    13385/10^9,13378/10^9,13345/10^9] k

theorem near_qnet_floor (k : Fin 9) :
    (nearFloorQ k : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (nearA k) (nearB k) (near_ordered k) := by
  fin_cases k
  · simpa [nearFloorQ,nearA,nearB,nearSlot,paidB] using paid_qnet_uniform_floor 0
  · simpa [nearFloorQ,nearA,nearB,nearSlot,paidB] using paid_qnet_uniform_floor 1
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using third_qnet_strict_floor
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using nearA004_qnet_floor
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using nearA005_qnet_floor
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using nearA102_qnet_floor
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using nearA103_qnet_floor
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using nearA104_qnet_floor
  · simpa [nearFloorQ,nearA,nearB,nearSlot] using nearA105_qnet_floor

def nearNumerator (k : Fin 9) : Int :=
  ![865472606752044193520814,384740080297673072456313,330476191522077830856882,330328811825492468326306,329644013816162796026642,377710089890276459527946,324349392455403565612519,324204642469388051403452,323532065318655270167163] k

theorem near_integer_gain (k : Fin 9) :
    sourceOrdinaryGainNumeratorInt (nearA k) (nearB k) (near_ordered k) = nearNumerator k := by
  fin_cases k
  · exact source_first_gain_exact
  · exact source_second_gain_exact
  · exact third_original_integer_gain
  · exact nearA004_original_integer_gain
  · exact nearA005_original_integer_gain
  · exact nearA102_original_integer_gain
  · exact nearA103_original_integer_gain
  · exact nearA104_original_integer_gain
  · exact nearA105_original_integer_gain

def nearStagedGain : ℚ :=
  ∑ k : Fin 9, stagedOrdinaryGainIntQ (nearA k) (nearB k) (near_ordered k)

theorem near_staged_gain_literal : nearStagedGain =
    3590457894347173707898037 / 10^30 := by
  simp only [nearStagedGain,staged_ordinary_gain_same,sourceOrdinaryGainIntQ,near_integer_gain]
  norm_num [nearNumerator,Fin.sum_univ_succ,scale]

def nearOriginalGain : ℝ :=
  ∑ k : Fin 9, (smallGainQ (s(nearA k,nearB k)) : ℝ)

theorem near_computed_mass_upper : nearComputedMass < (213/1000 : ℝ) := by
  have part : (fullPairMassQ : ℝ) =
      (nearMassQ : ℝ)+(midMassQ : ℝ)+(diag2MassQ : ℝ)+(restMassQ : ℝ) := by
    exact_mod_cast full_pair_mass_partition
  have full : (fullPairMassQ : ℝ) < 100001/100000 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 full_pair_mass_upper
  have mid : (74581/100000 : ℝ) < (midMassQ : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 mid_mass_lower
  have diag : (4143/100000 : ℝ) < (diag2MassQ : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 diag2_mass_lower
  have ne := computed_sector_source_error (fun p => nearCond p.1 p.2)
  rw [near_source_sector] at ne
  have re := computed_sector_source_error (fun p => restCond p.1 p.2)
  rw [rest_source_sector] at re
  have nh := (abs_lt.mp ne).2
  have rh := (abs_lt.mp re).2
  change nearComputedMass-(nearMassQ : ℝ) < (1/10^15 : ℝ) at nh
  change restComputedMass-(restMassQ : ℝ) < (1/10^15 : ℝ) at rh
  have rn := rest_computed_mass_nonnegative
  linarith only [part,full,mid,diag,nh,rh,rn]

theorem near_original_staged_error :
    |(nearStagedGain : ℝ)-nearOriginalGain| < (107/10^10 : ℝ) := by
  have point (k : Fin 9) :
      |(stagedOrdinaryGainIntQ (nearA k) (nearB k) (near_ordered k) : ℝ)-
        (smallGainQ (s(nearA k,nearB k)) : ℝ)| ≤
        (5/10^8 : ℝ)*(nearSectorBody k).trace.re+1/10^20 := by
    rw [near_sector_body_trace]
    exact staged_ordinary_gain_error_by_mass _ _ (near_ordered k)
  have bound : |(nearStagedGain : ℝ)-nearOriginalGain| ≤
      ∑ k : Fin 9, ((5/10^8 : ℝ)*(nearSectorBody k).trace.re+1/10^20) := by
    simp only [nearStagedGain,nearOriginalGain,Rat.cast_sum,← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => point k))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,near_sector_body_mass_sum] at bound
  have mass := near_computed_mass_upper
  linarith only [bound,mass]

theorem near_original_gain_lower :
    (3579/10^9 : ℝ) < nearOriginalGain := by
  have exactStage : (nearStagedGain : ℝ) =
      (3590457894347173707898037 / 10^30 : ℝ) := by
    rw [near_staged_gain_literal]
    norm_num
  have error := (abs_lt.mp near_original_staged_error).2
  rw [exactStage] at error
  linarith only [error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
