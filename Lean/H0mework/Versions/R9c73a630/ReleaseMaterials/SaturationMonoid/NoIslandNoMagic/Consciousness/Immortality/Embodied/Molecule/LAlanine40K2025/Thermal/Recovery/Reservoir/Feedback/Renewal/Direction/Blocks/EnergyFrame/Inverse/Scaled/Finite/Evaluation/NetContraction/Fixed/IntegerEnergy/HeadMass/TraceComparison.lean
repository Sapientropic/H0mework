import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.HeadTrace
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_trace_norm_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (e : ℝ) (distance : ‖A-B‖ ≤ e) :
    ‖A.trace-B.trace‖ ≤ (Fintype.card ι : ℝ)*e := by
  rw [← Matrix.trace_sub]
  exact (Donor.trace_norm_bound (A-B)).trans
    (mul_le_mul_of_nonneg_left distance (by positivity))

theorem source_finite_system_trace_near_one :
    ‖Input.finiteSystem.trace-1‖ ≤ (13/10^9 : ℝ) := by
  have h := source_trace_norm_error Input.finiteSystem Input.calculatedSystem
    (13/10^11) (by simpa only [norm_sub_rev] using Input.finite_system_error)
  rw [Input.calculated_system_lawful.2] at h
  exact h.trans (by norm_num [Basis])

theorem source_finite_bath_trace_near_one :
    ‖Input.finiteBath.trace-1‖ ≤ (41/10^7 : ℝ) := by
  have h := source_trace_norm_error Input.finiteBath Input.calculatedBath
    (41/10^9) (by simpa only [norm_sub_rev] using Input.finite_bath_error)
  rw [Input.calculated_bath_lawful.2] at h
  exact h.trans (by norm_num [Basis])

theorem source_finite_collision_trace_near_one :
    ‖Input.finiteCollisionPair.trace-1‖ ≤ (1/10^5 : ℝ) := by
  have source : Input.finiteCollisionPair.trace=
      Input.finiteSystem.trace*Input.finiteBath.trace := by
    rw [Input.finiteCollisionPair,Quantum.conjugation_trace]
    exact Matrix.trace_kronecker _ _
  rw [source]
  have split : Input.finiteSystem.trace*Input.finiteBath.trace-1=
      (Input.finiteSystem.trace-1)*Input.finiteBath.trace+
        (Input.finiteBath.trace-1) := by ring
  rw [split]
  have bathBound : ‖Input.finiteBath.trace‖ ≤ (1+41/10^7 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      Input.finiteBath.trace (1 : ℂ) 0
    simp only [sub_zero,norm_one] at triangle
    linarith only [triangle,source_finite_bath_trace_near_one]
  calc
    _ ≤ ‖(Input.finiteSystem.trace-1)*Input.finiteBath.trace‖+
      ‖Input.finiteBath.trace-1‖ := norm_add_le _ _
    _ ≤ ‖Input.finiteSystem.trace-1‖*‖Input.finiteBath.trace‖+
      ‖Input.finiteBath.trace-1‖ :=
      add_le_add (norm_mul_le _ _) (le_refl _)
    _ ≤ (13/10^9 : ℝ)*(1+41/10^7)+41/10^7 := by
      gcongr
      · exact source_finite_system_trace_near_one
      · exact source_finite_bath_trace_near_one
    _ ≤ 1/10^5 := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
