import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.PaidComparison.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdEnergy

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def paidPhysicalPair (slot : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Field.computedPair.submatrix (pairAddress (0 : Basis) (paidB slot))
    (pairAddress (0 : Basis) (paidB slot))

def paidPhysicalBody (slot : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (paidPhysicalPair slot) environmentState

theorem paid_physical_body_positive (slot : Fin 2) :
    (paidPhysicalBody slot).PosSemidef :=
  (computed_pair_positive.submatrix _).kronecker environmentState_positive

theorem paid_physical_pair_mass (slot : Fin 2) :
    (199/10000 : ℝ) < (paidPhysicalPair slot).trace.re := by
  have source : (1/50 : ℝ) <
      ((pairQ ((0 : Basis),paidB slot) ((0 : Basis),paidB slot)).1 : ℝ)+
      ((pairQ (paidB slot,(0 : Basis)) (paidB slot,(0 : Basis))).1 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 (paid_source_pair_mass slot)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have e0 := (abs_le.mp (source_pair_entry_error ((0 : Basis),paidB slot))).1
  have e1 := (abs_le.mp (source_pair_entry_error (paidB slot,(0 : Basis)))).1
  have q0 := pair_mass_entry_source (0 : Basis) (paidB slot)
  have q1 := pair_mass_entry_source (paidB slot) (0 : Basis)
  have trace : (paidPhysicalPair slot).trace.re =
      (Field.computedPair ((0 : Basis),paidB slot)
        ((0 : Basis),paidB slot)).re+
      (Field.computedPair (paidB slot,(0 : Basis))
        (paidB slot,(0 : Basis))).re := by
    simp [paidPhysicalPair,Matrix.trace,Matrix.diag,Fin.sum_univ_two,pairAddress]
  rw [trace]
  rw [←q0] at e0
  rw [←q1] at e1
  linarith only [source,e0,e1]

theorem paid_physical_body_mass (slot : Fin 2) :
    (199/10000 : ℝ) < (paidPhysicalBody slot).trace.re := by
  rw [paidPhysicalBody]
  simp only [Matrix.kronecker,Matrix.trace_kronecker,environmentState_trace]
  simpa using paid_physical_pair_mass slot

theorem paid_physical_energy_floor (slot : Fin 2) :
    (16/10^6 : ℝ)*(paidPhysicalBody slot).trace.re ≤
      (sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) *
        paidPhysicalBody slot).trace.re :=
  energy_lower_from_order _ _ (paid_physical_body_positive slot) _
    (paid_qnet_uniform_floor slot)

theorem paid_physical_energy_positive (slot : Fin 2) :
    0 < (sourceOrdinaryQNet (0 : Basis) (paidB slot) (paid_ordered slot) *
      paidPhysicalBody slot).trace.re := by
  have floor := paid_physical_energy_floor slot
  have mass := paid_physical_body_mass slot
  nlinarith only [floor,mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
