import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.Mass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A007.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A008.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A106.Spectrum
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section


/-! A first source-certified family in both anchor rows of the original mid-sector. -/

def midPaidSlot : Fin 4 → Fin 2 × Fin 18
  | 0 => (0,0)
  | 1 => (0,1)
  | 2 => (0,2)
  | 3 => (1,0)

def midPaidA (k : Fin 4) : Basis := midAnchor (midPaidSlot k).1
def midPaidB (k : Fin 4) : Basis := midPartner (midPaidSlot k).2

theorem mid_paid_ordered (k : Fin 4) : midPaidA k < midPaidB k :=
  mid_address_ordered _ _

theorem mid_paid_original_positive (k : Fin 4) :
    0 < smallGainQ (s(midPaidA k,midPaidB k)) := by
  fin_cases k
  · exact mid_original_gain_positive
  · exact midA007_original_gain_positive
  · exact midA008_original_gain_positive
  · exact midA106_original_gain_positive

theorem mid_paid_qnet_floor (k : Fin 4) :
    (826/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (midPaidA k) (midPaidB k) (mid_paid_ordered k) := by
  fin_cases k
  · refine le_trans ?_ mid_qnet_floor
    exact smul_le_smul_of_nonneg_right (by norm_num)
      (zero_le_one : (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  · refine le_trans ?_ midA007_qnet_floor
    exact smul_le_smul_of_nonneg_right (by norm_num)
      (zero_le_one : (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  · refine le_trans ?_ midA008_qnet_floor
    exact smul_le_smul_of_nonneg_right (by norm_num)
      (zero_le_one : (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  · refine le_trans ?_ midA106_qnet_floor
    exact smul_le_smul_of_nonneg_right (by norm_num)
      (zero_le_one : (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)

def midPaidBody (k : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  midSectorBody (midPaidSlot k).1 (midPaidSlot k).2

theorem mid_paid_body_positive (k : Fin 4) : (midPaidBody k).PosSemidef :=
  mid_sector_body_positive _ _

theorem mid_paid_source_pair_mass (k : Fin 4) : (1/50 : ℚ) <
    (pairQ (midPaidA k,midPaidB k) (midPaidA k,midPaidB k)).1+
    (pairQ (midPaidB k,midPaidA k) (midPaidB k,midPaidA k)).1 := by
  fin_cases k <;> decide +kernel

theorem mid_paid_body_mass (k : Fin 4) :
    (199/10000 : ℝ) < (midPaidBody k).trace.re := by
  have source : (1/50 : ℝ) <
      ((pairQ (midPaidA k,midPaidB k) (midPaidA k,midPaidB k)).1 : ℝ)+
      ((pairQ (midPaidB k,midPaidA k) (midPaidB k,midPaidA k)).1 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 (mid_paid_source_pair_mass k)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have e0 := (abs_le.mp (source_pair_entry_error (midPaidA k,midPaidB k))).1
  have e1 := (abs_le.mp (source_pair_entry_error (midPaidB k,midPaidA k))).1
  have q0 := pair_mass_entry_source (midPaidA k) (midPaidB k)
  have q1 := pair_mass_entry_source (midPaidB k) (midPaidA k)
  have trace : (midPaidBody k).trace.re =
      (Field.computedPair (midPaidA k,midPaidB k) (midPaidA k,midPaidB k)).re+
      (Field.computedPair (midPaidB k,midPaidA k) (midPaidB k,midPaidA k)).re := by
    rw [midPaidBody,mid_sector_body_trace]
    simp [midSectorPair,Matrix.trace,Matrix.diag,Fin.sum_univ_two,pairAddress,midPaidA,midPaidB]
  rw [trace]
  rw [←q0] at e0
  rw [←q1] at e1
  linarith only [source,e0,e1]

theorem mid_paid_energy_floor (k : Fin 4) :
    (826/10^8 : ℝ)*(midPaidBody k).trace.re ≤
      (sourceOrdinaryQNet (midPaidA k) (midPaidB k) (mid_paid_ordered k) *
        midPaidBody k).trace.re :=
  energy_lower_from_order _ _ (mid_paid_body_positive k) _ (mid_paid_qnet_floor k)

theorem mid_paid_energy_positive (k : Fin 4) :
    0 < (sourceOrdinaryQNet (midPaidA k) (midPaidB k) (mid_paid_ordered k) *
      midPaidBody k).trace.re := by
  have floor := mid_paid_energy_floor k
  have mass := mid_paid_body_mass k
  nlinarith only [floor,mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
