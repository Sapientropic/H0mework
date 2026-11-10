import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Spatial.Field
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Time

/-! Actual conjugation transports the strong integral; the test translation derivative is an operator-norm derivative. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.SpatialFields
noncomputable section
open Terminal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))
  (strong : ∀ v, Continuous (Quantum.Generator.orbit U v)) (B : Terminal.Spacetime →ᵇ (H →L[ℂ] H))

theorem kernel_shift (t : ℝ) (p : Terminal.Spacetime) (v : H) :
    U (Multiplicative.ofAdd t) (kernel U B (p + timeLine t) v) =
      kernel U B p (U (Multiplicative.ofAdd t) v) := by
  simp only [kernel, spatialPoint_shift]
  exact StrongFields.kernel_shift U (B (spatialPoint p)) t p v

include strong in
theorem field_time (t : ℝ) (f : Terminal.Test) (v : H) :
    U (Multiplicative.ofAdd t) (field U strong B f v) =
      field U strong B (translateTest (timeLine t) f) (U (Multiplicative.ofAdd t) v) := by
  rw [field_integral, field_integral]
  let L := (U (Multiplicative.ofAdd t)).toContinuousLinearEquiv.toContinuousLinearMap
  change L (∫ p, f p • kernel U B p v) = _
  rw [← L.integral_comp_comm (field_integrable U strong B f v)]
  calc
    _ = ∫ p, L (f (p+timeLine t) • kernel U B (p+timeLine t) v) :=
      (integral_add_right_eq_self _ (timeLine t)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by dsimp only; rw [map_smul, translateTest_apply]; exact congrArg (f (p+timeLine t) • ·) (kernel_shift U B t p v))

theorem conjugation_field (f : Terminal.Test) (t : ℝ) :
    Quantum.Generator.Commutator.conjugation U (field U strong B f) t =
      field U strong B (translateTest (timeLine t) f) := by
  ext v
  exact (field_time U strong B t f ((U (Multiplicative.ofAdd t)).symm v)).trans
    (congrArg (field U strong B (translateTest (timeLine t) f))
      ((U (Multiplicative.ofAdd t)).apply_symm_apply v))

theorem field_derivative (f : Terminal.Test) :
    HasDerivAt (Quantum.Generator.Commutator.conjugation U (field U strong B f))
      (field U strong B (testDerivative 0 f)) 0 := by
  have derivative := ((onL1 U strong B).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (Domain.Translation.toLp_hasDerivAt f)
  convert! derivative using 1
  funext t
  exact conjugation_field U strong B f t

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.SpatialFields
