import H0mework.Chemistry.LAlanineTrueTube.TraceFieldBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeTrace

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap ContinuousGradient Set
noncomputable section

def signedGradient (sign : ℝ) (x : Point) : Point := sign • sourceGradient x
def signedHessian (sign : ℝ) (x : Point) : Point →L[ℝ] Point := sign • sourceHessianLinear x

def signedGradientPair (sign : ℚ) (field : FieldBox) : VectorPair :=
  vectorScale (point sign) field.gradient

theorem signed_gradient_contains (sign : ℚ) (field : FieldBox) (x : Point)
    (bounded : FieldHolds field x) :
    VectorHolds (signedGradientPair sign field) (signedGradient (sign : ℝ) x) :=
  vectorScale_contains _ _ _ _ (point_holds sign) bounded.1

theorem signedGradient_hasFDerivAt (sign : ℝ) (x : Point) :
    HasFDerivAt (signedGradient sign) (signedHessian sign x) x :=
  (sourceGradient_hasFDerivAt x).const_smul sign

theorem signed_field_lipschitz (box : Rectangle) (field : FieldBox)
    (bounded : ∀ x, InRectangle box x → FieldHolds field x)
    (sign : ℝ) (unit : |sign| = 1) :
    LipschitzOnWith (fieldLipschitz field) (signedGradient sign)
      (Icc (lowerPoint box) (upperPoint box)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [signedGradient, dist_smul₀, Real.norm_eq_abs, unit, one_mul] using
    (field_lipschitz box field bounded).dist_le_mul x hx y hy

theorem signed_acceleration (sign : ℝ) (unit : sign * sign = 1) (x : Point) :
    signedHessian sign x (signedGradient sign x) = sourceHessianLinear x (sourceGradient x) := by
  simp only [signedHessian, signedGradient, smul_apply, map_smul,
    smul_smul, unit, one_smul]

theorem signed_acceleration_contains (field : FieldBox) (x : Point) (bounded : FieldHolds field x)
    (sign : ℝ) (unit : sign * sign = 1) :
    VectorHolds (accelerationPair field) (signedHessian sign x (signedGradient sign x)) := by
  rw [signed_acceleration sign unit x]
  exact acceleration_contains field x bounded

end
end LAlanine40K2025.BasinRefinement.TrueTubeTrace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
