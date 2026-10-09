import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdEnergy

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def midPhysicalPair : Matrix (Fin 2) (Fin 2) ℂ :=
  Field.computedPair.submatrix (pairAddress (0 : Basis) (6 : Basis))
    (pairAddress (0 : Basis) (6 : Basis))

def midPhysicalBody : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker midPhysicalPair environmentState

theorem mid_physical_body_positive : midPhysicalBody.PosSemidef :=
  (computed_pair_positive.submatrix _).kronecker environmentState_positive

theorem mid_source_pair_mass : (1/50 : ℚ) <
    (pairQ ((0 : Basis),(6 : Basis)) ((0 : Basis),(6 : Basis))).1+
    (pairQ ((6 : Basis),(0 : Basis)) ((6 : Basis),(0 : Basis))).1 := by
  decide +kernel

theorem mid_physical_pair_mass :
    (199/10000 : ℝ) < midPhysicalPair.trace.re := by
  have source : (1/50 : ℝ) <
      ((pairQ ((0 : Basis),(6 : Basis)) ((0 : Basis),(6 : Basis))).1 : ℝ)+
      ((pairQ ((6 : Basis),(0 : Basis)) ((6 : Basis),(0 : Basis))).1 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 mid_source_pair_mass
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have e0 := (abs_le.mp (source_pair_entry_error ((0 : Basis),(6 : Basis)))).1
  have e1 := (abs_le.mp (source_pair_entry_error ((6 : Basis),(0 : Basis)))).1
  have q0 := pair_mass_entry_source (0 : Basis) (6 : Basis)
  have q1 := pair_mass_entry_source (6 : Basis) (0 : Basis)
  have trace : midPhysicalPair.trace.re =
      (Field.computedPair ((0 : Basis),(6 : Basis))
        ((0 : Basis),(6 : Basis))).re+
      (Field.computedPair ((6 : Basis),(0 : Basis))
        ((6 : Basis),(0 : Basis))).re := by
    simp [midPhysicalPair,Matrix.trace,Matrix.diag,Fin.sum_univ_two,pairAddress]
  rw [trace]
  rw [←q0] at e0
  rw [←q1] at e1
  linarith only [source,e0,e1]

theorem mid_physical_body_mass :
    (199/10000 : ℝ) < midPhysicalBody.trace.re := by
  rw [midPhysicalBody]
  simp only [Matrix.kronecker,Matrix.trace_kronecker,environmentState_trace]
  simpa using mid_physical_pair_mass

theorem mid_physical_energy_floor :
    (837/10^8 : ℝ)*midPhysicalBody.trace.re ≤
      (sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide) *
        midPhysicalBody).trace.re :=
  energy_lower_from_order _ _ mid_physical_body_positive _ mid_qnet_floor

theorem mid_physical_energy_positive :
    0 < (sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide) *
      midPhysicalBody).trace.re := by
  have floor := mid_physical_energy_floor
  have mass := mid_physical_body_mass
  nlinarith only [floor,mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
