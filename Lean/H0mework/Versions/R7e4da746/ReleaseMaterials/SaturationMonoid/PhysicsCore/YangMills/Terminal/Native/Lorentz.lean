import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Geometry
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Polynomials

/-! Lorentz recognition compares actual connection readouts. No chosen
presentation of the algebra of local labels is required. -/

set_option autoImplicit false
open scoped ContDiff

namespace SaturationMonoid.PhysicsCore.YangMills.Terminal.NativeLorentz

noncomputable section

private theorem pullback_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : GaugeSpacetime → GaugeSpacetime →L[ℝ] E) (smooth : ContDiff ℝ ∞ A)
    (L : GaugeSpacetime →L[ℝ] GaugeSpacetime) :
    ContDiff ℝ ∞ (fun x => (A (L x)).comp L) :=
  (smooth.comp L.contDiff).clm_comp contDiff_const

def connection (G : GaugeGroup) (L : GaugeSpacetime →L[ℝ] GaugeSpacetime)
    (A : Connection G) : Connection G :=
  ⟨fun x => (A.val (L x)).comp L, pullback_smooth A.val A.property L⟩

theorem connection_apply (G : GaugeGroup) (L : GaugeSpacetime →L[ℝ] GaugeSpacetime)
    (A : Connection G) (x v : GaugeSpacetime) :
    (connection G L A).val x v = A.val (L x) (L v) := rfl

theorem connection_id (G : GaugeGroup) (A : Connection G) :
    connection G (ContinuousLinearMap.id ℝ GaugeSpacetime) A = A := by
  apply Subtype.ext
  funext x
  exact ContinuousLinearMap.comp_id _

theorem connection_comp (G : GaugeGroup)
    (L M : GaugeSpacetime →L[ℝ] GaugeSpacetime) (A : Connection G) :
    connection G M (connection G L A) = connection G (L.comp M) A := by
  apply Subtype.ext
  funext x
  rfl

private theorem pullback_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : GaugeSpacetime → GaugeSpacetime →L[ℝ] E) (smooth : ContDiff ℝ ∞ A)
    (L : GaugeSpacetime →L[ℝ] GaugeSpacetime) (x u v : GaugeSpacetime) :
    (fderiv ℝ (fun y => (A (L y)).comp L) x u) v =
      (fderiv ℝ A (L x) (L u)) (L v) := by
  have generated := (((smooth.differentiable (by simp) (L x)).hasFDerivAt).comp x
    L.hasFDerivAt).clm_comp (hasFDerivAt_const L x)
  erw [generated.fderiv]
  simp

theorem curvature_pullback (G : GaugeGroup) (L : GaugeSpacetime →L[ℝ] GaugeSpacetime)
    (A : Connection G) (x u v : GaugeSpacetime) :
    curvature G (connection G L A) x u v = curvature G A (L x) (L u) (L v) := by
  unfold curvature
  change (fderiv ℝ (fun y => (A.val (L y)).comp L) x u) v -
    (fderiv ℝ (fun y => (A.val (L y)).comp L) x v) u +
      ⁅A.val (L x) (L u), A.val (L x) (L v)⁆ = _
  erw [pullback_derivative A.val A.property L x u v,
    pullback_derivative A.val A.property L x v u]
  rfl

/-- Moving the evaluation point back makes this a transformation of the
tensor label at the same point, matching the lower indices of the stress tensor. -/
def Related (G : GaugeGroup) (spin : Spin)
    (before after : differentialPolynomials G) : Prop :=
  ∀ (A : Connection G) (x : GaugeSpacetime),
    after.val (A, x) = before.val
      (connection G (lorentzMap spin).toContinuousLinearMap A, (lorentzMap spin).symm x)

theorem related_unique (G : GaugeGroup) (spin : Spin)
    (before first second : differentialPolynomials G)
    (hfirst : Related G spin before first) (hsecond : Related G spin before second) :
    first = second := by
  apply Subtype.ext
  funext pair
  exact (hfirst pair.1 pair.2).trans (hsecond pair.1 pair.2).symm

end
end SaturationMonoid.PhysicsCore.YangMills.Terminal.NativeLorentz
