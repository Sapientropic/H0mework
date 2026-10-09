import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Projector

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projection_complement_trace (P : Matrix ι ι ℂ) (k : ι) (normalized : P.trace = 1) :
    ((1-Spectrum.basisPure k)*P*(1-Spectrum.basisPure k)).trace = 1-P k k := by
  have idempotent : Spectrum.basisPure k*Spectrum.basisPure k = Spectrum.basisPure k := by
    ext i j
    simp [Spectrum.basisPure,Matrix.diagonal_apply]
    aesop
  have complement : (1-Spectrum.basisPure k)*(1-Spectrum.basisPure k) = 1-Spectrum.basisPure k := by
    noncomm_ring [idempotent]
  rw [Matrix.trace_mul_cycle,complement,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,normalized]
  have cycle : (Spectrum.basisPure k*P).trace = (P*Spectrum.basisPure k).trace := Matrix.trace_mul_comm _ _
  rw [cycle,BasisInverse.trace_basis]

theorem projection_complement_square (P : Matrix ι ι ℂ) (hermitian : P.IsHermitian)
    (projector : P*P=P) (k : ι) :
    ‖(1-Spectrum.basisPure k)*P*(1-Spectrum.basisPure k)‖ = ‖(1-Spectrum.basisPure k)*P‖^2 := by
  have identity : (1-Spectrum.basisPure k)*P*(1-Spectrum.basisPure k) =
      ((1-Spectrum.basisPure k)*P)*star ((1-Spectrum.basisPure k)*P) := by
    simp only [star_mul,star_sub,star_one,show star P=P from hermitian.eq,
      show star (Spectrum.basisPure k)=Spectrum.basisPure k from (Spectrum.basisPure_positive k).isHermitian.eq,
      Matrix.mul_assoc,← Matrix.mul_assoc P P,projector]
  rw [identity,CStarRing.norm_self_mul_star,pow_two]

theorem rank_one_projection_error (P : Matrix ι ι ℂ) (hermitian : P.IsHermitian)
    (projector : P*P=P) (normalized : P.trace=1) (k : ι) :
    ‖P-Spectrum.basisPure k‖ ≤ 2*‖(1-Spectrum.basisPure k)*P‖+
      Fintype.card ι*‖(1-Spectrum.basisPure k)*P‖^2 := by
  let Q := Spectrum.basisPure k
  have diag : ‖P k k-1‖ ≤ Fintype.card ι*‖(1-Q)*P‖^2 := by
    have h := trace_norm_bound ((1-Q)*P*(1-Q))
    rw [projection_complement_trace P k normalized,projection_complement_square P hermitian projector k] at h
    simpa only [norm_sub_rev] using h
  have second : ‖Q*P*Q-Q‖ ≤ Fintype.card ι*‖(1-Q)*P‖^2 := by
    rw [basis_projector_sandwich]
    have expression : (P k k) • Q-Q = (P k k-1) • Q := by module
    rw [expression,norm_smul]
    exact (mul_le_mul_of_nonneg_left (basis_projector_norm k) (norm_nonneg _)).trans (by simpa using diag)
  have split : P-Q = (P-Q*P*Q)+(Q*P*Q-Q) := by abel
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add (projection_compression_error P hermitian k) second)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
