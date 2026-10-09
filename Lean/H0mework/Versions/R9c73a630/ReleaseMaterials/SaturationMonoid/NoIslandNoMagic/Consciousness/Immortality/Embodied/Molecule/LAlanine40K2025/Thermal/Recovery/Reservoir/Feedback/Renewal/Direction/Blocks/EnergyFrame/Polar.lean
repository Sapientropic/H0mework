import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransportError

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open ElectronicFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The recorded energy frame may be far from identity; its actual Gram controls invertibility. -/
theorem isUnit_of_gram (Q : Matrix ι ι ℂ) (close : ‖star Q*Q-1‖ < 1) : IsUnit Q := by
  have gram := Polar.isUnit_of_close (star Q*Q) close
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w same
  apply Matrix.mulVec_injective_of_isUnit gram
  simp only [← Matrix.mulVec_mulVec,same]

theorem source_polar_unitary (Q : Matrix ι ι ℂ) (close : ‖star Q*Q-1‖ < 1) :
    Polar.matrix Q ∈ Matrix.unitaryGroup ι ℂ := by
  have unit : IsUnit (CFC.abs Q) := (CFC.isUnit_sqrt_iff _ (star_mul_self_nonneg Q)).mpr
    ((isUnit_of_gram Q close).star.mul (isUnit_of_gram Q close))
  have selfAdjoint : star (CFC.abs Q) = CFC.abs Q := (CFC.abs_nonneg Q).star_eq
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Polar.matrix,star_mul,← Ring.inverse_star,selfAdjoint]
  calc
    _ = Ring.inverse (CFC.abs Q)*(star Q*Q)*Ring.inverse (CFC.abs Q) := by simp only [mul_assoc]
    _ = Ring.inverse (CFC.abs Q)*(CFC.abs Q*CFC.abs Q)*Ring.inverse (CFC.abs Q) := by rw [CFC.abs_mul_abs]
    _ = 1 := by rw [Ring.inverse_mul_cancel_left _ _ unit,Ring.mul_inverse_cancel _ unit]

def sourcePolar (Q : Matrix ι ι ℂ) (close : ‖star Q*Q-1‖ < 1) : Matrix.unitaryGroup ι ℂ :=
  ⟨Polar.matrix Q,source_polar_unitary Q close⟩

theorem source_polar_error (Q : Matrix ι ι ℂ) (close : ‖star Q*Q-1‖ < 1) :
    ‖(sourcePolar Q close : Matrix ι ι ℂ)-Q‖ ≤ ‖star Q*Q-1‖ := by
  have unit : IsUnit (CFC.abs Q) := (CFC.isUnit_sqrt_iff _ (star_mul_self_nonneg Q)).mpr
    ((isUnit_of_gram Q close).star.mul (isUnit_of_gram Q close))
  have factor : Polar.matrix Q*CFC.abs Q = Q := Ring.inverse_mul_cancel_right _ _ unit
  have residual : Q-Polar.matrix Q = Polar.matrix Q*(CFC.abs Q-1) := by rw [mul_sub,mul_one,factor]
  change ‖Polar.matrix Q-Q‖ ≤ _
  rw [norm_sub_rev,residual,CStarRing.norm_mem_unitary_mul _ (source_polar_unitary Q close)]
  exact Polar.sqrt_residual_norm _ (star_mul_self_nonneg Q)

/-- The same source residual and Gram error bound the Hermitian Hamiltonian in the generated unitary frame. -/
theorem diagonalized_source_error (A Q E : Matrix ι ι ℂ) (close : ‖star Q*Q-1‖ < 1) :
    ‖star (sourcePolar Q close : Matrix ι ι ℂ)*A*(sourcePolar Q close : Matrix ι ι ℂ)-E‖ ≤
      ‖A*Q-Q*E‖+(‖A‖+‖E‖)*‖star Q*Q-1‖ := by
  let U := sourcePolar Q close
  have residual : star (U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)-E =
      star (U : Matrix ι ι ℂ)*(A*(U : Matrix ι ι ℂ)-(U : Matrix ι ι ℂ)*E) := by
    have unit : star (U : Matrix ι ι ℂ)*(U : Matrix ι ι ℂ) = 1 := (Unitary.mem_iff.mp U.property).1
    rw [mul_sub,← mul_assoc,← mul_assoc,unit,one_mul]
  rw [residual]
  have unitStar : star (U : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ := by
    exact (star U).property
  rw [CStarRing.norm_mem_unitary_mul _ unitStar]
  have split : A*(U : Matrix ι ι ℂ)-(U : Matrix ι ι ℂ)*E =
      (A*Q-Q*E)+A*((U : Matrix ι ι ℂ)-Q)-((U : Matrix ι ι ℂ)-Q)*E := by noncomm_ring
  rw [split]
  calc
    _ ≤ ‖A*Q-Q*E‖+‖A*((U : Matrix ι ι ℂ)-Q)‖+‖((U : Matrix ι ι ℂ)-Q)*E‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖A*Q-Q*E‖+‖A‖*‖(U : Matrix ι ι ℂ)-Q‖+‖(U : Matrix ι ι ℂ)-Q‖*‖E‖ := by gcongr <;> exact norm_mul_le _ _
    _ ≤ ‖A*Q-Q*E‖+‖A‖*‖star Q*Q-1‖+‖star Q*Q-1‖*‖E‖ := by gcongr <;> exact source_polar_error Q close
    _ = _ := by ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
