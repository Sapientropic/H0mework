import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Field
import Mathlib.MeasureTheory.Group.Integral

/-! Actual conjugation transports the strong integral; the test translation derivative is an operator-norm derivative. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.StrongFields
noncomputable section
open Terminal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))
  (strong : ∀ v, Continuous (Quantum.Generator.orbit U v)) (A : H →L[ℂ] H)

theorem kernel_shift (t : ℝ) (p : Terminal.Spacetime) (v : H) :
    U (Multiplicative.ofAdd t) (kernel U A (p + timeLine t) v) =
      kernel U A p (U (Multiplicative.ofAdd t) v) := by
  have hp : (p + timeLine t) 0 = p 0 + t := by
    change p 0 + timeLine t 0 = _
    rw [timeLine_time]
  change U (Multiplicative.ofAdd t)
    (U (Multiplicative.ofAdd (-(p + timeLine t) 0))
      (A ((U (Multiplicative.ofAdd (-(p + timeLine t) 0))).symm v))) =
    U (Multiplicative.ofAdd (-p 0)) (A ((U (Multiplicative.ofAdd (-p 0))).symm
      (U (Multiplicative.ofAdd t) v)))
  simp only [hp]
  have inverse (s : ℝ) : (U (Multiplicative.ofAdd (-s))).symm = U (Multiplicative.ofAdd s) := by
    rw [show Multiplicative.ofAdd (-s) = (Multiplicative.ofAdd s)⁻¹ from rfl, map_inv]
    rfl
  rw [inverse, inverse]
  have add (r s : ℝ) (x : H) : U (Multiplicative.ofAdd r) (U (Multiplicative.ofAdd s) x) =
      U (Multiplicative.ofAdd (r+s)) x := (Quantum.Generator.orbit_add U x r s).symm
  rw [add, add]
  congr 2; congr 1; ring

include strong in
theorem field_time (t : ℝ) (f : Terminal.Test) (v : H) :
    U (Multiplicative.ofAdd t) (field U strong A f v) =
      field U strong A (translateTest (timeLine t) f) (U (Multiplicative.ofAdd t) v) := by
  rw [field_integral, field_integral]
  let L := (U (Multiplicative.ofAdd t)).toContinuousLinearEquiv.toContinuousLinearMap
  change L (∫ p, f p • kernel U A p v) = _
  rw [← L.integral_comp_comm (field_integrable U strong A f v)]
  calc
    _ = ∫ p, L (f (p+timeLine t) • kernel U A (p+timeLine t) v) :=
      (integral_add_right_eq_self _ (timeLine t)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by dsimp only; rw [map_smul, translateTest_apply]; exact congrArg (f (p+timeLine t) • ·) (kernel_shift U A t p v))

theorem conjugation_field (f : Terminal.Test) (t : ℝ) :
    Quantum.Generator.Commutator.conjugation U (field U strong A f) t =
      field U strong A (translateTest (timeLine t) f) := by
  ext v
  exact (field_time U strong A t f ((U (Multiplicative.ofAdd t)).symm v)).trans
    (congrArg (field U strong A (translateTest (timeLine t) f))
      ((U (Multiplicative.ofAdd t)).apply_symm_apply v))

theorem field_derivative (f : Terminal.Test) :
    HasDerivAt (Quantum.Generator.Commutator.conjugation U (field U strong A f))
      (field U strong A (testDerivative 0 f)) 0 := by
  have derivative := ((onL1 U strong A).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (Domain.Translation.toLp_hasDerivAt f)
  convert! derivative using 1
  funext t
  exact conjugation_field U strong A f t

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.StrongFields
