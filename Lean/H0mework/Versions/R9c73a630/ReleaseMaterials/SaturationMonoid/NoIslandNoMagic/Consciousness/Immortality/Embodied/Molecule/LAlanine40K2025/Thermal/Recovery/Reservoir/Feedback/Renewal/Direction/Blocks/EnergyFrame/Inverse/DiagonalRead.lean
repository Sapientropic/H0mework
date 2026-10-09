import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Trace

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Donor
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_trace_remainder (d : ι → ℂ) (P : Matrix ι ι ℂ) (k : ι) (normalized : P.trace=1) :
    (Matrix.diagonal d*P).trace-d k =
      (Matrix.diagonal (fun i => d i-d k)*((1-Spectrum.basisPure k)*P*(1-Spectrum.basisPure k))).trace := by
  have remainder : (Matrix.diagonal (fun i => d i-d k)*((1-Spectrum.basisPure k)*P*(1-Spectrum.basisPure k))).trace =
      ∑ i, (d i-d k)*P i i := by
    simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Matrix.sub_mul,Matrix.mul_sub,
      Matrix.one_mul,Matrix.mul_one,Matrix.sub_apply,Spectrum.basisPure,Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    by_cases same : i=k
    · subst i; simp
    · simp [same]
  rw [remainder]
  have trace : ∑ i, P i i = 1 := normalized
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Finset.sum_sub_distrib,sub_mul,
    ← Finset.mul_sum,trace,mul_one]

theorem diagonal_expectation_error (d : ι → ℂ) (P : Matrix ι ι ℂ)
    (positive : P.PosSemidef) (projector : P*P=P) (normalized : P.trace=1) (k : ι) :
    ‖(Matrix.diagonal d*P).trace-d k‖ ≤
      ‖Matrix.diagonal (fun i => d i-d k)‖*(Fintype.card ι*‖(1-Spectrum.basisPure k)*P‖^2) := by
  let R := 1-Spectrum.basisPure k
  have hermitian : R.IsHermitian := Matrix.isHermitian_one.sub (Spectrum.basisPure_positive k).isHermitian
  have p : (R*P*R).PosSemidef := by
    have h := positive.mul_mul_conjTranspose_same R
    simpa only [hermitian.eq] using h
  rw [diagonal_trace_remainder d P k normalized]
  apply (complex_trace_norm_mass _ _ p).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have tr := trace_norm_bound (R*P*R)
  rw [projection_complement_square P positive.isHermitian projector k] at tr
  exact (Complex.re_le_norm _).trans tr

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
