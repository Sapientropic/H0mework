import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.InstrumentContinuation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem basis_projector_norm (k : ι) : ‖Spectrum.basisPure k‖ ≤ 1 := by
  rw [Spectrum.basisPure,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  split_ifs <;> simp

theorem basis_projector_sandwich (P : Matrix ι ι ℂ) (k : ι) :
    Spectrum.basisPure k*P*Spectrum.basisPure k = (P k k) • Spectrum.basisPure k := by
  ext i j
  simp only [Spectrum.basisPure,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul]
  split_ifs <;> subst_vars <;> simp_all

theorem trace_norm_bound (P : Matrix ι ι ℂ) : ‖P.trace‖ ≤ Fintype.card ι*‖P‖ := by
  calc
    _ ≤ ∑ i, ‖P i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖P‖ := Finset.sum_le_sum (fun i _ => matrix_entry_norm_le P i i)
    _ = _ := by simp

theorem projection_compression_error (P : Matrix ι ι ℂ) (hermitian : P.IsHermitian) (k : ι) :
    ‖P-Spectrum.basisPure k*P*Spectrum.basisPure k‖ ≤ 2*‖(1-Spectrum.basisPure k)*P‖ := by
  let Q := Spectrum.basisPure k
  have split : P-Q*P*Q = (1-Q)*P+Q*(P*(1-Q)) := by noncomm_ring
  have transpose : star ((1-Q)*P) = P*(1-Q) := by
    simp only [star_mul,star_sub,star_one,show star P = P from hermitian.eq,show star Q = Q from (Spectrum.basisPure_positive k).isHermitian.eq]
  have right : ‖P*(1-Q)‖ = ‖(1-Q)*P‖ := by rw [← transpose,norm_star]
  rw [split]
  calc
    _ ≤ ‖(1-Q)*P‖+‖Q*(P*(1-Q))‖ := norm_add_le _ _
    _ ≤ ‖(1-Q)*P‖+‖Q‖*‖P*(1-Q)‖ := add_le_add le_rfl (norm_mul_le _ _)
    _ ≤ ‖(1-Q)*P‖+1*‖(1-Q)*P‖ := by rw [right]; gcongr; exact basis_projector_norm k
    _ = _ := by ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
