import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Bounded.LivingLawRootGeneratedScalarBoundedObservationDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarProjectiveDeterminantDispositionKernel

/-!
# Bounded scalar projective determinant disposition

This is the determinant consumer of the complete bounded observation
classifier.  A bounded-dualizable face is passed to the rank/Picard producer;
all finite, kernel and coverage residual branches pass through unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarBoundedProjectiveDeterminantDisposition

open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarBoundedObservationDisposition
open SourceGeneratedScalarFiniteProjectiveDuality

noncomputable section

universe r c d o

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d} {O : Type o}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]
variable [AddCommGroup O] [Module R O]
variable {evaluation : C →ₗ[R] Module.Dual R D}
variable {observation : PerfectificationCarrier evaluation →ₗ[R] O}

inductive Disposition :
    (bounded : SourceGeneratedScalarBoundedObservationDisposition.Disposition
      evaluation observation) → Type (max r c d o + 2) where
  | boundedProjective
      (equivalence : PerfectificationCarrier evaluation ≃ₗ[R] O)
      (finite : Module.Finite R O)
      (projective : Module.Projective R O)
      (duality : TensorDuality (R := R) O)
      (determinant :
        SourceGeneratedScalarProjectiveDeterminantDisposition.Disposition
          (R := R) (M := O)) :
      Disposition (.boundedDualizable equivalence finite projective duality)
  | finiteNonprojective
      (equivalence : PerfectificationCarrier evaluation ≃ₗ[R] O)
      (finite : Module.Finite R O)
      (notProjective : ¬ Module.Projective R O) :
      Disposition (.finiteNonprojective equivalence finite notProjective)
  | nonfinite
      (equivalence : PerfectificationCarrier evaluation ≃ₗ[R] O)
      (notFinite : ¬ Module.Finite R O) :
      Disposition (.nonfinite equivalence notFinite)
  | kernelOnly
      (coordinate : SourceGeneratedScalarObservationDisposition.KernelCoordinate observation)
      (surjective : Function.Surjective observation) :
      Disposition (.kernelOnly coordinate surjective)
  | coverageOnly
      (coordinate : SourceGeneratedScalarObservationDisposition.CoverageCoordinate observation)
      (injective : Function.Injective observation) :
      Disposition (.coverageOnly coordinate injective)
  | kernelAndCoverage
      (kernelCoordinate :
        SourceGeneratedScalarObservationDisposition.KernelCoordinate observation)
      (coverageCoordinate :
        SourceGeneratedScalarObservationDisposition.CoverageCoordinate observation) :
      Disposition (.kernelAndCoverage kernelCoordinate coverageCoordinate)

noncomputable def settle
    (bounded : SourceGeneratedScalarBoundedObservationDisposition.Disposition
      evaluation observation) : Disposition bounded := by
  exact match bounded with
    | .boundedDualizable equivalence finite projective duality =>
        .boundedProjective equivalence finite projective duality
          (SourceGeneratedScalarProjectiveDeterminantDisposition.settle
            finite projective)
    | .finiteNonprojective equivalence finite notProjective =>
        .finiteNonprojective equivalence finite notProjective
    | .nonfinite equivalence notFinite => .nonfinite equivalence notFinite
    | .kernelOnly coordinate surjective => .kernelOnly coordinate surjective
    | .coverageOnly coordinate injective => .coverageOnly coordinate injective
    | .kernelAndCoverage kernelCoordinate coverageCoordinate =>
        .kernelAndCoverage kernelCoordinate coverageCoordinate

theorem total
    (bounded : SourceGeneratedScalarBoundedObservationDisposition.Disposition
      evaluation observation) : Nonempty (Disposition bounded) :=
  ⟨settle bounded⟩

theorem settle_boundedProjective
    (equivalence : PerfectificationCarrier evaluation ≃ₗ[R] O)
    (finite : Module.Finite R O) (projective : Module.Projective R O)
    (duality : TensorDuality (R := R) O) :
    settle (observation := observation)
        (.boundedDualizable (observation := observation)
          equivalence finite projective duality) =
      .boundedProjective equivalence finite projective duality
        (SourceGeneratedScalarProjectiveDeterminantDisposition.settle
          finite projective) :=
  rfl

end
end SourceGeneratedScalarBoundedProjectiveDeterminantDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
