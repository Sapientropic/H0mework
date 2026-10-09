import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.RootOrder

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sqrt_floor (A : Matrix ι ι ℂ) (r : ℝ) (nonnegative : 0 ≤ r)
    (floor : (r*r) • (1 : Matrix ι ι ℂ) ≤ A) : r • (1 : Matrix ι ι ℂ) ≤ CFC.sqrt A := by
  have step := CFC.sqrt_le_sqrt _ _ floor
  have square : (r • (1 : Matrix ι ι ℂ))*(r • 1) = (r*r) • (1 : Matrix ι ι ℂ) := by
    simp only [mul_smul_comm,mul_one,smul_smul]
  rw [← square,CFC.sqrt_mul_self _ (smul_nonneg nonnegative zero_le_one)] at step
  exact step

theorem sqrt_perturbation (A B : Matrix ι ι ℂ) (positiveA : 0 ≤ A) (positiveB : 0 ≤ B)
    (r d : ℝ) (rpos : 0 ≤ r) (dpos : 0 ≤ d)
    (floorA : (r*r) • (1 : Matrix ι ι ℂ) ≤ A)
    (floorB : (r*r) • (1 : Matrix ι ι ℂ) ≤ B)
    (paid : ‖A-B‖ ≤ 2*r*d) : ‖CFC.sqrt A-CFC.sqrt B‖ ≤ d := by
  have matrixBound (X Y : Matrix ι ι ℂ) (self : (X-Y).IsHermitian)
      (cost : ‖X-Y‖ ≤ 2*r*d) : X-Y ≤ (2*r*d) • (1 : Matrix ι ι ℂ) := by
    have raw := self.isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at raw
    exact raw.trans (smul_le_smul_of_nonneg_right cost zero_le_one)
  have hermitian : (CFC.sqrt A-CFC.sqrt B).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.sub
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  have up := sqrt_order_step A B positiveB r d dpos (sqrt_floor B r rpos floorB)
    (matrixBound A B ((Matrix.nonneg_iff_posSemidef.mp positiveA).isHermitian.sub
      (Matrix.nonneg_iff_posSemidef.mp positiveB).isHermitian) paid)
  have reversePaid : ‖B-A‖ ≤ 2*r*d := by rw [norm_sub_rev]; exact paid
  have down := sqrt_order_step B A positiveA r d dpos (sqrt_floor A r rpos floorA)
    (matrixBound B A ((Matrix.nonneg_iff_posSemidef.mp positiveB).isHermitian.sub
      (Matrix.nonneg_iff_posSemidef.mp positiveA).isHermitian) reversePaid)
  apply self_adjoint_norm_of_sides _ hermitian d dpos up
  rw [neg_smul]
  simpa only [neg_sub] using neg_le_neg down

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
