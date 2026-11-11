import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Bounded.LivingLawRootGeneratedScalarFiniteProjectiveDualityKernel
import H0mework.Realization.Perfectification.ScalarCoimage
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Observation.LivingLawRootGeneratedScalarObservationDispositionKernel

/-!
# Scalar bounded observation disposition

The only inputs are an actual scalar dual evaluation and an observation of
its exact carrier.  The existing four-way observation classifier runs first.
Only its exact branch tests finite generation and projectivity internally;
no caller selects a branch or supplies boundedness evidence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarBoundedObservationDisposition

open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarObservationDisposition
open SourceGeneratedScalarFiniteProjectiveDuality

noncomputable section

universe r c d o

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d} {O : Type o}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]
variable [AddCommGroup O] [Module R O]
variable (evaluation : C →ₗ[R] Module.Dual R D)

abbrev ExactCarrier := PerfectificationCarrier evaluation

inductive Disposition (observation : ExactCarrier evaluation →ₗ[R] O) :
    Type (max r c d o + 2) where
  | boundedDualizable
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
      (finite : Module.Finite R O)
      (projective : Module.Projective R O)
      (tensorDuality : TensorDuality (R := R) O)
  | finiteNonprojective
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
      (finite : Module.Finite R O)
      (notProjective : ¬ Module.Projective R O)
  | nonfinite
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
      (notFinite : ¬ Module.Finite R O)
  | kernelOnly
      (coordinate : KernelCoordinate observation)
      (surjective : Function.Surjective observation)
  | coverageOnly
      (coordinate : CoverageCoordinate observation)
      (injective : Function.Injective observation)
  | kernelAndCoverage
      (kernelCoordinate : KernelCoordinate observation)
      (coverageCoordinate : CoverageCoordinate observation)

noncomputable def settle
    (observation : ExactCarrier evaluation →ₗ[R] O) :
    Disposition evaluation observation := by
  classical
  exact match SourceGeneratedScalarObservationDisposition.settle observation with
    | .exact equivalence =>
        if finite : Module.Finite R O then
          if projective : Module.Projective R O then
            .boundedDualizable equivalence finite projective
              (SourceGeneratedScalarFiniteProjectiveDuality.generate finite projective)
          else .finiteNonprojective equivalence finite projective
        else .nonfinite equivalence finite
    | .kernelOnly coordinate surjective => .kernelOnly coordinate surjective
    | .coverageOnly coordinate injective => .coverageOnly coordinate injective
    | .kernelAndCoverage kernelCoordinate coverageCoordinate =>
        .kernelAndCoverage kernelCoordinate coverageCoordinate

theorem total (observation : ExactCarrier evaluation →ₗ[R] O) :
    Nonempty (Disposition evaluation observation) :=
  ⟨settle evaluation observation⟩

theorem settle_eq_boundedDualizable
    (observation : ExactCarrier evaluation →ₗ[R] O)
    (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
    (outcome : SourceGeneratedScalarObservationDisposition.settle observation =
      .exact equivalence)
    (finite : Module.Finite R O) (projective : Module.Projective R O) :
    settle evaluation observation =
      .boundedDualizable equivalence finite projective
        (SourceGeneratedScalarFiniteProjectiveDuality.generate finite projective) := by
  rw [settle, outcome]
  simp [finite, projective]

theorem settle_eq_finiteNonprojective
    (observation : ExactCarrier evaluation →ₗ[R] O)
    (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
    (outcome : SourceGeneratedScalarObservationDisposition.settle observation =
      .exact equivalence)
    (finite : Module.Finite R O) (notProjective : ¬ Module.Projective R O) :
    settle evaluation observation =
      .finiteNonprojective equivalence finite notProjective := by
  rw [settle, outcome]
  simp [finite, notProjective]

theorem settle_eq_nonfinite
    (observation : ExactCarrier evaluation →ₗ[R] O)
    (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
    (outcome : SourceGeneratedScalarObservationDisposition.settle observation =
      .exact equivalence)
    (notFinite : ¬ Module.Finite R O) :
    settle evaluation observation = .nonfinite equivalence notFinite := by
  rw [settle, outcome]
  simp [notFinite]

theorem settle_eq_kernelOnly
    (observation : ExactCarrier evaluation →ₗ[R] O)
    (coordinate : KernelCoordinate observation)
    (surjective : Function.Surjective observation)
    (outcome : SourceGeneratedScalarObservationDisposition.settle observation =
      .kernelOnly coordinate surjective) :
    settle evaluation observation = .kernelOnly coordinate surjective := by
  rw [settle, outcome]

theorem settle_eq_coverageOnly
    (observation : ExactCarrier evaluation →ₗ[R] O)
    (coordinate : CoverageCoordinate observation)
    (injective : Function.Injective observation)
    (outcome : SourceGeneratedScalarObservationDisposition.settle observation =
      .coverageOnly coordinate injective) :
    settle evaluation observation = .coverageOnly coordinate injective := by
  rw [settle, outcome]

theorem settle_eq_kernelAndCoverage
    (observation : ExactCarrier evaluation →ₗ[R] O)
    (kernelCoordinate : KernelCoordinate observation)
    (coverageCoordinate : CoverageCoordinate observation)
    (outcome : SourceGeneratedScalarObservationDisposition.settle observation =
      .kernelAndCoverage kernelCoordinate coverageCoordinate) :
    settle evaluation observation =
      .kernelAndCoverage kernelCoordinate coverageCoordinate := by
  rw [settle, outcome]

def quotientToSource (injective : Function.Injective evaluation) :
    ExactCarrier evaluation →ₗ[R] C :=
  (LinearMap.ker evaluation).liftQ LinearMap.id (by
    rw [LinearMap.ker_eq_bot.mpr injective]
    exact bot_le)

theorem quotientToSource_bijective (injective : Function.Injective evaluation) :
    Function.Bijective (quotientToSource evaluation injective) := by
  constructor
  · intro left right equality
    obtain ⟨leftValue, rfl⟩ :=
      Submodule.mkQ_surjective (LinearMap.ker evaluation) left
    obtain ⟨rightValue, rfl⟩ :=
      Submodule.mkQ_surjective (LinearMap.ker evaluation) right
    exact congrArg (canonicalMap evaluation) equality
  · intro value
    exact ⟨canonicalMap evaluation value, rfl⟩

end
end SourceGeneratedScalarBoundedObservationDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
