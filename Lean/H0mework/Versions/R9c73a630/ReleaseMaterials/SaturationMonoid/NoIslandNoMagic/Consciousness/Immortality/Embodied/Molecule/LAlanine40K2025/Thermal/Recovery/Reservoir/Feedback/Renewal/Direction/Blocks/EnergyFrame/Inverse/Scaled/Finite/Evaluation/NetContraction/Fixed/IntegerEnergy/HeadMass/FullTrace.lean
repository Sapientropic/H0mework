import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.TraceComparison
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.FinitePair
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Collision Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_finite_pair_trace_real_error :
    |Input.finiteCollisionPair.trace.re-Input.finitePair.trace.re| ≤
      (2/10^12 : ℝ) := by
  have h := Input.finite_coupling_energy_error (1 : JointMatrix Basis)
  simpa only [Collision.energy,Matrix.one_mul,norm_one,mul_one] using h

theorem source_field_pair_finite_error :
    ‖Field.computedPair-Input.finitePair‖ ≤ (3/10^15 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub Input.finitePair
    Diagonal.computedPair Field.computedPair
  rw [norm_sub_rev]
  exact triangle.trans
    ((add_le_add Diagonal.pair_numeric_error Field.pair_numeric_error).trans
      (by norm_num))

theorem source_field_pair_trace_real_error :
    |Field.computedPair.trace.re-Input.finitePair.trace.re| ≤
      (1/10^10 : ℝ) := by
  have h := source_trace_norm_error Field.computedPair Input.finitePair
    (3/10^15) source_field_pair_finite_error
  have paid : ‖Field.computedPair.trace-Input.finitePair.trace‖ ≤
      (1/10^10 : ℝ) := h.trans (by norm_num [Basis])
  have real := (Complex.abs_re_le_norm
    (Field.computedPair.trace-Input.finitePair.trace)).trans paid
  simpa only [Complex.sub_re] using real

theorem source_field_pair_trace_lt_two : Field.computedPair.trace.re < (2 : ℝ) := by
  have collision : |Input.finiteCollisionPair.trace.re-1| ≤
      (1/10^5 : ℝ) := by
    have h := (Complex.abs_re_le_norm (Input.finiteCollisionPair.trace-1)).trans
      source_finite_collision_trace_near_one
    simpa only [Complex.sub_re,Complex.one_re] using h
  have finite := source_finite_pair_trace_real_error
  have field := source_field_pair_trace_real_error
  have hc := (abs_le.mp collision).2
  have hf := (abs_le.mp finite).1
  have hg := (abs_le.mp field).2
  linarith only [hc,hf,hg]

theorem head_ordinary_pair_trace_lt_four :
    (∑ p : HeadOrdinary,
      (computedOrdinaryPairBlock p.val.1 p.val.2).trace.re) < (4 : ℝ) := by
  have h := head_ordinary_pair_trace_le_full_twice
  linarith only [h,source_field_pair_trace_lt_two]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
