import Mathlib.LinearAlgebra.Determinant
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Bounded.LivingLawRootGeneratedScalarBoundedObservationDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarDeterminantFrameTorsorKernel

/-!
# Scalar finite-free determinant disposition

This reader consumes an already generated bounded observation disposition.
Only `boundedDualizable` is tested for `Module.Free`; the free branch receives
the top-exterior readout, projective nonfree modules retain a Picard-eligible residual,
and every other bounded-observation branch passes through unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarFiniteFreeDeterminantDisposition

open SourceGeneratedScalarBoundedObservationDisposition
open SourceGeneratedScalarFiniteProjectiveDuality
open SourceGeneratedScalarFiniteFreeTopExterior

noncomputable section

universe r c d o

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d} {O : Type o}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]
variable [AddCommGroup O] [Module R O]
variable {evaluation : C →ₗ[R] Module.Dual R D}
variable {observation : ExactCarrier evaluation →ₗ[R] O}

inductive PicardEligibilityResidual : Type (max r o + 1) where
  | projectiveNonfree (notFree : ¬ Module.Free R O)

inductive Disposition :
    (bounded : SourceGeneratedScalarBoundedObservationDisposition.Disposition
      evaluation observation) → Type (max r c d o + 2) where
  | freeDeterminant
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
      (readout : Readout (R := R) (O := O)) :
      Disposition (.boundedDualizable equivalence readout.finite
        readout.projective readout.duality)
  | picardEligibleResidual
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
      (finite : Module.Finite R O)
      (projective : Module.Projective R O)
      (duality : TensorDuality (R := R) O)
      (reason : PicardEligibilityResidual (R := R) (O := O)) :
      Disposition (.boundedDualizable equivalence finite projective duality)
  | finiteNonprojective
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
      (finite : Module.Finite R O)
      (notProjective : ¬ Module.Projective R O) :
      Disposition (.finiteNonprojective equivalence finite notProjective)
  | nonfinite
      (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
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
  classical
  exact match bounded with
    | .boundedDualizable equivalence finite projective duality =>
        if free : Module.Free R O then
          .freeDeterminant equivalence ⟨finite, projective, duality, free⟩
        else .picardEligibleResidual equivalence finite projective duality
          (.projectiveNonfree free)
    | .finiteNonprojective equivalence finite notProjective =>
        .finiteNonprojective equivalence finite notProjective
    | .nonfinite equivalence notFinite => .nonfinite equivalence notFinite
    | .kernelOnly coordinate surjective => .kernelOnly coordinate surjective
    | .coverageOnly coordinate injective => .coverageOnly coordinate injective
    | .kernelAndCoverage kernelCoordinate coverageCoordinate =>
        .kernelAndCoverage kernelCoordinate coverageCoordinate

theorem settle_bounded_free
    (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
    (finite : Module.Finite R O) (projective : Module.Projective R O)
    (duality : TensorDuality (R := R) O) (free : Module.Free R O) :
    settle (observation := observation)
        (.boundedDualizable (observation := observation)
          equivalence finite projective duality) =
      .freeDeterminant (observation := observation) equivalence
        ⟨finite, projective, duality, free⟩ := by
  simp only [settle, dif_pos free]

theorem settle_bounded_projectiveNonfree
    (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
    (finite : Module.Finite R O) (projective : Module.Projective R O)
    (duality : TensorDuality (R := R) O)
    (notFree : ¬ Module.Free R O) :
    settle (observation := observation)
        (.boundedDualizable (observation := observation)
          equivalence finite projective duality) =
      .picardEligibleResidual (observation := observation)
        equivalence finite projective duality (.projectiveNonfree notFree) := by
  simp only [settle, dif_neg notFree]

theorem settle_finiteNonprojective
    (equivalence : ExactCarrier evaluation ≃ₗ[R] O)
    (finite : Module.Finite R O)
    (notProjective : ¬ Module.Projective R O) :
    settle (observation := observation)
        (.finiteNonprojective (observation := observation)
          equivalence finite notProjective) =
      .finiteNonprojective (observation := observation)
        equivalence finite notProjective :=
  rfl

/-! Raw `LinearMap.det` has a fallback convention.  This package records the
stronger evidence required for a safe finite-free determinant readout. -/
structure SafeLinearMapDetReadout where
  free : Module.Free R O
  finite : Module.Finite R O
  endomorphism : O →ₗ[R] O

namespace SafeLinearMapDetReadout

noncomputable def det (readout : SafeLinearMapDetReadout (R := R) (O := O)) : R := by
  letI : Module.Free R O := readout.free
  letI : Module.Finite R O := readout.finite
  exact LinearMap.det readout.endomorphism

end SafeLinearMapDetReadout

theorem no_safe_linearMap_det_readout (notFree : ¬ Module.Free R O) :
    ¬ Nonempty (SafeLinearMapDetReadout (R := R) (O := O)) := by
  rintro ⟨readout⟩
  exact notFree readout.free

end
end SourceGeneratedScalarFiniteFreeDeterminantDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
