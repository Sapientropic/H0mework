import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Scalar finite-projective tensor duality

Finite generation and projectivity generate the ordinary module-tensor
evaluation, coevaluation, both reconstruction triangles, reflexivity, and
the canonical perfect evaluation pairing.  These are generated outputs,
not premises of the surrounding observation classifier.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarFiniteProjectiveDuality

open TensorProduct Module

noncomputable section

universe r o

variable {R : Type r} [CommRing R]
variable {O : Type o} [AddCommGroup O] [Module R O]

structure TensorDuality (O : Type o) [AddCommGroup O] [Module R O] where
  evaluation : Module.Dual R O ⊗[R] O →ₗ[R] R
  coevaluation : R →ₗ[R] Module.Dual R O ⊗[R] O
  evaluation_is_canonical : evaluation = contractLeft R O
  triangle : dualTensorHom R O O (coevaluation 1) = LinearMap.id
  dualTriangle : Module.Dual.transpose
      (dualTensorHom R O O (coevaluation 1)) = LinearMap.id
  reflexive : Module.IsReflexive R O
  perfectEvaluation : (Module.Dual.eval R O).IsPerfPair

noncomputable def generate
    (finite : Module.Finite R O) (projective : Module.Projective R O) :
    TensorDuality (R := R) O := by
  letI : Module.Finite R O := finite
  letI : Module.Projective R O := projective
  let reflexive : Module.IsReflexive R O := inferInstance
  letI : Module.IsReflexive R O := reflexive
  let coevaluationElement : Module.Dual R O ⊗[R] O :=
    (dualTensorHomEquiv R O O).symm LinearMap.id
  exact
    { evaluation := contractLeft R O
      coevaluation := LinearMap.toSpanSingleton R _ coevaluationElement
      evaluation_is_canonical := rfl
      triangle := by
        rw [LinearMap.toSpanSingleton_apply_one]
        exact (dualTensorHomEquiv R O O).apply_symm_apply _
      dualTriangle := by
        rw [LinearMap.toSpanSingleton_apply_one]
        have identityReconstruction :
            dualTensorHom R O O coevaluationElement = LinearMap.id :=
          (dualTensorHomEquiv R O O).apply_symm_apply _
        rw [identityReconstruction]
        rfl
      reflexive := reflexive
      perfectEvaluation := inferInstance }

theorem generated_triangle
    (finite : Module.Finite R O) (projective : Module.Projective R O) :
    dualTensorHom R O O ((generate finite projective).coevaluation 1) =
      LinearMap.id :=
  (generate finite projective).triangle

theorem generated_dualTriangle
    (finite : Module.Finite R O) (projective : Module.Projective R O) :
    Module.Dual.transpose
        (dualTensorHom R O O ((generate finite projective).coevaluation 1)) =
      LinearMap.id :=
  (generate finite projective).dualTriangle

end
end SourceGeneratedScalarFiniteProjectiveDuality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
