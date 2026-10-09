import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.LowEntry

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Propagation.Producer Load.Source Load.Producer.StrictThermal Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_cos_square_upper : (Real.cos BasisInverse.actualAngle)^2 < (1/4000000 : ℝ) := by
  rw [BasisInverse.actualAngle,Real.cos_pi_div_two_sub]
  have h := Real.sin_le nativeClock_small.1.le
  have positive : 0 < Real.sin (nativeClockStep : ℝ) := by
    have p := source_cos_lower
    rw [BasisInverse.actualAngle,Real.cos_pi_div_two_sub] at p
    linarith
  nlinarith [nativeClock_small.2]

theorem donor_energy_bounds : (92/10 : ℝ) < donorEnergy ∧ donorEnergy < 93/10 := by
  have lower := Spectral.Producer.source_top_lower
  have upper := Spectral.Producer.source_top_upper
  unfold donorEnergy Donor.originalTop
  constructor <;> linarith

theorem original_inverse_low_negative (i : Basis) (low : Preparation.sourceEnergies i < -18) :
    (BasisInverse.bodyInverse Spectral.Projection.excitedIndex (Real.cos BasisInverse.actualAngle)
      (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian (lowIndex i,0) (lowIndex i,0)).re < -100000000 := by
  rw [original_inverse_low_entry]
  have cast : (2*(Preparation.sourceEnergies i : ℂ)+1-(Real.sin BasisInverse.actualAngle : ℂ)^2*(donorEnergy : ℂ))/
      (Real.cos BasisInverse.actualAngle : ℂ)^2 =
    (( (2*Preparation.sourceEnergies i+1-(Real.sin BasisInverse.actualAngle)^2*donorEnergy)/
      (Real.cos BasisInverse.actualAngle)^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [cast,Complex.ofReal_re]
  have positive : 0 < (Real.cos BasisInverse.actualAngle)^2 := sq_pos_of_pos (by linarith [source_cos_lower])
  apply (div_lt_iff₀ positive).mpr
  have circle := Real.cos_sq_add_sin_sq BasisInverse.actualAngle
  have lower := donor_energy_bounds.1
  have upper := donor_energy_bounds.2
  have bound := source_cos_square_upper
  nlinarith [mul_le_mul_of_nonneg_right upper.le positive.le]

theorem original_measurement_scale_lower : (100000000 : ℝ) < measurementScale (sourceOutputObservable loadTotalHamiltonian) := by
  obtain ⟨i,low⟩ := original_low_energy
  let X := BasisInverse.bodyInverse Spectral.Projection.excitedIndex (Real.cos BasisInverse.actualAngle)
    (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian
  have entry := original_inverse_low_negative i low
  change (X (lowIndex i,0) (lowIndex i,0)).re < -100000000 at entry
  have normRead := (Complex.abs_re_le_norm (X (lowIndex i,0) (lowIndex i,0))).trans
    (matrix_entry_norm_le X (lowIndex i,0) (lowIndex i,0))
  have normIdentity : ‖sourceOutputObservable loadTotalHamiltonian‖ = ‖X‖ := by
    rw [BasisInverse.original_inverse_formula,BasisInverse.actualOutput]
    exact StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint BodyKernel.bodyFree) X
  rw [measurementScale,normIdentity]
  linarith [(abs_le.mp normRead).1]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
