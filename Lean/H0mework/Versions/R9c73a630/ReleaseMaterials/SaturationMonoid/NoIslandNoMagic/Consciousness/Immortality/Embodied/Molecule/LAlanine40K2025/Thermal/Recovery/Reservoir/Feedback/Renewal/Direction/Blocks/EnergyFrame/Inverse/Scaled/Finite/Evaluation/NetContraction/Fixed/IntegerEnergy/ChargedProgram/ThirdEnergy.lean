import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.EnergyOrder
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.DominantMass.PositiveSource

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def thirdPhysicalPair : Matrix (Fin 2) (Fin 2) ℂ :=
  Field.computedPair.submatrix (pairAddress (0 : Basis) (3 : Basis))
    (pairAddress (0 : Basis) (3 : Basis))

def thirdPhysicalBody : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker thirdPhysicalPair environmentState

theorem third_physical_pair_positive : thirdPhysicalPair.PosSemidef :=
  computed_pair_positive.submatrix _

theorem third_physical_body_positive : thirdPhysicalBody.PosSemidef := by
  exact third_physical_pair_positive.kronecker environmentState_positive

theorem third_source_pair_mass : (1/50 : ℚ) <
    (pairQ ((0 : Basis),(3 : Basis)) ((0 : Basis),(3 : Basis))).1+
    (pairQ ((3 : Basis),(0 : Basis)) ((3 : Basis),(0 : Basis))).1 := by
  decide +kernel

theorem source_pair_entry_error (p : Basis × Basis) :
    |(Field.computedPair p p).re-(InputProducts.pair p p).re| ≤
      (2/10^20 : ℝ) := by
  have h := (matrix_entry_norm_le (Field.computedPair-InputProducts.pair) p p).trans
    InputProducts.pair_error
  have re := (Complex.abs_re_le_norm ((Field.computedPair-InputProducts.pair) p p)).trans h
  simpa only [Matrix.sub_apply,Complex.sub_re] using re

theorem third_physical_pair_mass : (199/10000 : ℝ) < thirdPhysicalPair.trace.re := by
  have source : (1/50 : ℝ) <
      ((pairQ ((0 : Basis),(3 : Basis)) ((0 : Basis),(3 : Basis))).1 : ℝ)+
      ((pairQ ((3 : Basis),(0 : Basis)) ((3 : Basis),(0 : Basis))).1 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 third_source_pair_mass
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have e0 := (abs_le.mp (source_pair_entry_error ((0 : Basis),(3 : Basis)))).1
  have e1 := (abs_le.mp (source_pair_entry_error ((3 : Basis),(0 : Basis)))).1
  have q0 := pair_mass_entry_source (0 : Basis) (3 : Basis)
  have q1 := pair_mass_entry_source (3 : Basis) (0 : Basis)
  have trace : thirdPhysicalPair.trace.re =
      (Field.computedPair ((0 : Basis),(3 : Basis)) ((0 : Basis),(3 : Basis))).re+
      (Field.computedPair ((3 : Basis),(0 : Basis)) ((3 : Basis),(0 : Basis))).re := by
    simp [thirdPhysicalPair,Matrix.trace,Matrix.diag,Fin.sum_univ_two,pairAddress]
  rw [trace]
  rw [←q0] at e0
  rw [←q1] at e1
  linarith only [source,e0,e1]

theorem third_physical_body_mass : (199/10000 : ℝ) < thirdPhysicalBody.trace.re := by
  have env := environmentState_trace
  rw [thirdPhysicalBody]
  simp only [Matrix.kronecker,Matrix.trace_kronecker,env]
  simpa using third_physical_pair_mass

theorem third_physical_energy_floor :
    (138/10^7 : ℝ)*thirdPhysicalBody.trace.re ≤
      (sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) *
        thirdPhysicalBody).trace.re :=
  energy_lower_from_order _ _ third_physical_body_positive _
    third_qnet_strict_floor

theorem third_physical_energy_positive :
    0 < (sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) *
      thirdPhysicalBody).trace.re := by
  have floor := third_physical_energy_floor
  have mass := third_physical_body_mass
  nlinarith only [floor,mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
