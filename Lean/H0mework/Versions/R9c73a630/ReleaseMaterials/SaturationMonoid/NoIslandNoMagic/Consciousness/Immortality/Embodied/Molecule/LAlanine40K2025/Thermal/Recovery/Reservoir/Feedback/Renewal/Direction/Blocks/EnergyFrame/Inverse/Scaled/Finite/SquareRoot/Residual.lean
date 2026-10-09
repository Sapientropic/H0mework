import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.FactorBound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem order_of_square_error (A B : Matrix ι ι ℂ) (positiveB : 0 ≤ B) (d : ℝ) (dpos : 0 ≤ d)
    (paid : A-B ≤ (d*d) • (1 : Matrix ι ι ℂ)) : CFC.sqrt A-CFC.sqrt B ≤ d • (1 : Matrix ι ι ℂ) := by
  have square : (CFC.sqrt B+d • (1 : Matrix ι ι ℂ))*(CFC.sqrt B+d • 1)=
      B+(2*d) • CFC.sqrt B+(d*d) • (1 : Matrix ι ι ℂ) := by
    rw [add_mul,mul_add,mul_add,CFC.sqrt_mul_sqrt_self B positiveB]
    simp only [mul_smul_comm,smul_mul_assoc,one_mul,mul_one,smul_smul]
    module
  have middle : 0 ≤ (2*d) • CFC.sqrt B := smul_nonneg (by positivity) (CFC.sqrt_nonneg B)
  have first : A ≤ B+(d*d) • (1 : Matrix ι ι ℂ) := by
    simpa only [add_comm] using (sub_le_iff_le_add).mp paid
  have bound : A ≤ (CFC.sqrt B+d • (1 : Matrix ι ι ℂ))*(CFC.sqrt B+d • 1) := by
    rw [square]
    have increase : B ≤ B+(2*d) • CFC.sqrt B := le_add_of_nonneg_right middle
    exact first.trans (add_le_add increase (le_refl ((d*d) • (1 : Matrix ι ι ℂ))))
  have roots := CFC.sqrt_le_sqrt A _ bound
  rw [CFC.sqrt_mul_self _ (add_nonneg (CFC.sqrt_nonneg B) (smul_nonneg dpos zero_le_one))] at roots
  exact (sub_le_iff_le_add).mpr (by simpa only [add_comm] using roots)

theorem sqrt_error_from_squared_budget (A B : Matrix ι ι ℂ) (positiveA : 0 ≤ A) (positiveB : 0 ≤ B)
    (d : ℝ) (dpos : 0 ≤ d) (paid : ‖A-B‖ ≤ d*d) : ‖CFC.sqrt A-CFC.sqrt B‖ ≤ d := by
  have ha := (Matrix.nonneg_iff_posSemidef.mp positiveA).isHermitian
  have hb := (Matrix.nonneg_iff_posSemidef.mp positiveB).isHermitian
  have upper (X Y : Matrix ι ι ℂ) (hermitian : (X-Y).IsHermitian) (cost : ‖X-Y‖ ≤ d*d) :
      X-Y ≤ (d*d) • (1 : Matrix ι ι ℂ) := by
    have raw := hermitian.isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at raw
    exact raw.trans (smul_le_smul_of_nonneg_right cost zero_le_one)
  have up := order_of_square_error A B positiveB d dpos (upper A B (ha.sub hb) paid)
  have down := order_of_square_error B A positiveA d dpos (upper B A (hb.sub ha) (by simpa only [norm_sub_rev] using paid))
  have hr : (CFC.sqrt A-CFC.sqrt B).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.sub
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  apply self_adjoint_norm_of_sides _ hr d dpos up
  rw [neg_smul]
  simpa only [neg_sub] using neg_le_neg down

theorem root_gram_residual (A L : Matrix ι ι ℂ) (positiveA : 0 ≤ A) (d : ℝ) (dpos : 0 ≤ d)
    (paid : ‖A-(L*Lᴴ)*(L*Lᴴ)‖ ≤ d*d) : ‖CFC.sqrt A-L*Lᴴ‖ ≤ d := by
  have gram := Matrix.posSemidef_self_mul_conjTranspose L
  have square : ((L*Lᴴ)*(L*Lᴴ)).PosSemidef := by
    simpa only [gram.isHermitian.eq] using Matrix.posSemidef_self_mul_conjTranspose (L*Lᴴ)
  have cost := sqrt_error_from_squared_budget A ((L*Lᴴ)*(L*Lᴴ)) positiveA square.nonneg d dpos paid
  rw [CFC.sqrt_mul_self _ gram.nonneg] at cost
  exact cost

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
