import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.Naturality.LivingLawRootGeneratedScalarProjectiveDeterminantEquivalenceNaturalityKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Observation.LivingLawRootGeneratedScalarObservationDispositionKernel

/-!
# Scalar projective determinant morphism disposition

An arbitrary source morphism is not allowed to manufacture an equivalence of
determinant lines or Picard coordinates.  The generic classifier first asks
whether the actual linear map is bijective.  A bijective map generates its
linear equivalence and transports the complete projective determinant
disposition.  Otherwise the existing observation classifier retains an
actual nonzero kernel coordinate, an actual cokernel representative, or both.

No finite, projective, constant-rank, determinant, frame, or equivalence
premise is accepted by the morphism classifier itself.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarProjectiveDeterminantMorphismDisposition

open SourceGeneratedScalarProjectiveDeterminantDisposition
open SourceGeneratedScalarProjectiveDeterminantEquivalenceNaturality
open SourceGeneratedScalarObservationDisposition

noncomputable section

universe r m n p

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]
variable {N : Type n} [AddCommGroup N] [Module R N]
variable {P : Type p} [AddCommGroup P] [Module R P]

/-- Complete kernel/coverage disposition of an arbitrary source morphism. -/
abbrev MorphismDisposition (map : M →ₗ[R] N) :=
  SourceGeneratedScalarObservationDisposition.Disposition map

/-- The actual map is the only classifier input. -/
noncomputable def settleMorphism (map : M →ₗ[R] N) :
    MorphismDisposition map :=
  SourceGeneratedScalarObservationDisposition.settle map

theorem settleMorphism_total (map : M →ₗ[R] N) :
    Nonempty (MorphismDisposition map) :=
  ⟨settleMorphism map⟩

theorem settleMorphism_equivalence_of_bijective (map : M →ₗ[R] N)
    (bijective : Function.Bijective map) :
    ∃ equivalence : M ≃ₗ[R] N,
      settleMorphism map = .exact equivalence := by
  exact (SourceGeneratedScalarObservationDisposition.settle_exact_iff_bijective
    map).mpr bijective

/-- The identity source morphism reaches the equivalence branch. -/
theorem identity_equivalence_branch :
    ∃ equivalence : M ≃ₗ[R] M,
      settleMorphism (LinearMap.id : M →ₗ[R] M) =
        .exact equivalence :=
  settleMorphism_equivalence_of_bijective LinearMap.id
    Function.bijective_id

/-- Composition of two positive source morphisms again reaches an actual
generated equivalence. -/
theorem composition_equivalence_branch
    (first : M →ₗ[R] N) (second : N →ₗ[R] P)
    (firstBijective : Function.Bijective first)
    (secondBijective : Function.Bijective second) :
    ∃ equivalence : M ≃ₗ[R] P,
      settleMorphism (second.comp first) = .exact equivalence := by
  exact settleMorphism_equivalence_of_bijective (second.comp first)
    ⟨secondBijective.1.comp firstBijective.1,
      secondBijective.2.comp firstBijective.2⟩

/-- Complete action of an arbitrary source morphism on a projective
determinant disposition.  Only the exact branch exposes a target disposition. -/
inductive ProjectiveTransportDisposition
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N) :
    Type (max r m n + 1) where
  | transported
      (equivalence : M ≃ₗ[R] N)
      (target : Disposition (R := R) (M := N))
  | kernelOnly
      (coordinate : KernelCoordinate map)
      (surjective : Function.Surjective map)
  | coverageOnly
      (coordinate : CoverageCoordinate map)
      (injective : Function.Injective map)
  | kernelAndCoverage
      (kernelCoordinate : KernelCoordinate map)
      (coverageCoordinate : CoverageCoordinate map)

noncomputable def settleProjectiveTransport
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N) :
    ProjectiveTransportDisposition source map :=
  match settleMorphism map with
  | .exact equivalence =>
      .transported equivalence (transportDisposition equivalence source)
  | .kernelOnly coordinate surjective => .kernelOnly coordinate surjective
  | .coverageOnly coordinate injective => .coverageOnly coordinate injective
  | .kernelAndCoverage kernelCoordinate coverageCoordinate =>
      .kernelAndCoverage kernelCoordinate coverageCoordinate

theorem settleProjectiveTransport_total
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N) :
    Nonempty (ProjectiveTransportDisposition source map) :=
  ⟨settleProjectiveTransport source map⟩

/-- Positive transport contains exactly the dependent disposition obtained
from the generated equivalence. -/
theorem settleProjectiveTransport_of_bijective
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N)
    (bijective : Function.Bijective map) :
    ∃ equivalence : M ≃ₗ[R] N,
      settleProjectiveTransport source map =
        .transported equivalence
          (transportDisposition equivalence source) := by
  obtain ⟨equivalence, settled⟩ :=
    settleMorphism_equivalence_of_bijective map bijective
  exact ⟨equivalence, by simp [settleProjectiveTransport, settled]⟩

/-- A noninjective but surjective map retains its actual kernel coordinate. -/
theorem settleProjectiveTransport_kernelOnly
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N)
    (notInjective : ¬ Function.Injective map)
    (surjective : Function.Surjective map) :
    ∃ coordinate : KernelCoordinate map,
      settleProjectiveTransport source map =
        .kernelOnly coordinate surjective := by
  let coordinate := kernelCoordinateOfNotInjective map notInjective
  refine ⟨coordinate, ?_⟩
  simp [settleProjectiveTransport, settleMorphism,
    SourceGeneratedScalarObservationDisposition.settle,
    notInjective, surjective, coordinate]

/-- An injective but nonsurjective map retains an actual cokernel class and
representative outside its range. -/
theorem settleProjectiveTransport_coverageOnly
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N)
    (injective : Function.Injective map)
    (notSurjective : ¬ Function.Surjective map) :
    ∃ coordinate : CoverageCoordinate map,
      settleProjectiveTransport source map =
        .coverageOnly coordinate injective := by
  let coordinate := coverageCoordinateOfNotSurjective map notSurjective
  refine ⟨coordinate, ?_⟩
  simp [settleProjectiveTransport, settleMorphism,
    SourceGeneratedScalarObservationDisposition.settle,
    injective, notSurjective, coordinate]

/-- If both directions fail, neither residual coordinate is discarded. -/
theorem settleProjectiveTransport_kernelAndCoverage
    (source : Disposition (R := R) (M := M)) (map : M →ₗ[R] N)
    (notInjective : ¬ Function.Injective map)
    (notSurjective : ¬ Function.Surjective map) :
    ∃ (kernelCoordinate : KernelCoordinate map)
      (coverageCoordinate : CoverageCoordinate map),
      settleProjectiveTransport source map =
        .kernelAndCoverage kernelCoordinate coverageCoordinate := by
  let kernelCoordinate := kernelCoordinateOfNotInjective map notInjective
  let coverageCoordinate :=
    coverageCoordinateOfNotSurjective map notSurjective
  refine ⟨kernelCoordinate, coverageCoordinate, ?_⟩
  simp [settleProjectiveTransport, settleMorphism,
    SourceGeneratedScalarObservationDisposition.settle,
    notInjective, notSurjective, kernelCoordinate, coverageCoordinate]

end

end SourceGeneratedScalarProjectiveDeterminantMorphismDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
