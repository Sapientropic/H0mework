import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Scalar observation disposition

Every linear observation over a commutative ring is classified by the map
alone.  Kernel loss and coverage loss are settled independently, so a map
which has both defects retains both explicit residual coordinates.

No finite, projective, duality, determinant, or branch-selection datum is
accepted by the classifier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarObservationDisposition

noncomputable section

universe r p o

variable {R : Type r} [CommRing R]
variable {P : Type p} {O : Type o}
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup O] [Module R O]

/-- A nonzero source coordinate annihilated by the observation. -/
structure KernelCoordinate (observation : P →ₗ[R] O) : Type (max p o + 1) where
  private mk ::
  coordinate : P
  coordinate_ne_zero : coordinate ≠ 0
  maps_to_zero : observation coordinate = 0

namespace KernelCoordinate

variable {observation : P →ₗ[R] O}

theorem nonzero (coordinate : KernelCoordinate observation) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

theorem vanishes (coordinate : KernelCoordinate observation) :
    observation coordinate.coordinate = 0 :=
  coordinate.maps_to_zero

theorem not_injective (coordinate : KernelCoordinate observation) :
    ¬ Function.Injective observation := by
  intro injective
  apply coordinate.nonzero
  apply injective
  simpa using coordinate.vanishes

end KernelCoordinate

/-- A nonzero exact cokernel class with an actual representative outside the
observation range. -/
structure CoverageCoordinate (observation : P →ₗ[R] O) : Type (max p o + 1) where
  private mk ::
  coordinate : O ⧸ LinearMap.range observation
  coordinate_ne_zero : coordinate ≠ 0
  representative : O
  representative_class :
    (Submodule.Quotient.mk representative : O ⧸ LinearMap.range observation) =
      coordinate
  representative_not_mem_range : representative ∉ LinearMap.range observation

namespace CoverageCoordinate

variable {observation : P →ₗ[R] O}

theorem nonzero (coordinate : CoverageCoordinate observation) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

theorem representative_outside_range
    (coordinate : CoverageCoordinate observation) :
    coordinate.representative ∉ LinearMap.range observation :=
  coordinate.representative_not_mem_range

theorem not_surjective (coordinate : CoverageCoordinate observation) :
    ¬ Function.Surjective observation := by
  intro surjective
  apply coordinate.representative_outside_range
  obtain ⟨preimage, equality⟩ := surjective coordinate.representative
  exact ⟨preimage, equality⟩

end CoverageCoordinate

/-- Complete disposition.  Neither residual direction hides the other. -/
inductive Disposition (observation : P →ₗ[R] O) : Type (max p o + 1) where
  | exact (equivalence : P ≃ₗ[R] O)
  | kernelOnly
      (coordinate : KernelCoordinate observation)
      (surjective : Function.Surjective observation)
  | coverageOnly
      (coordinate : CoverageCoordinate observation)
      (injective : Function.Injective observation)
  | kernelAndCoverage
      (kernelCoordinate : KernelCoordinate observation)
      (coverageCoordinate : CoverageCoordinate observation)

private theorem exists_distinct_equal_images
    {observation : P →ₗ[R] O}
    (notInjective : ¬ Function.Injective observation) :
    ∃ left right, left ≠ right ∧ observation left = observation right := by
  classical
  by_contra impossible
  apply notInjective
  intro left right equality
  by_contra different
  exact impossible ⟨left, right, different, equality⟩

noncomputable def kernelCoordinateOfNotInjective
    (observation : P →ₗ[R] O)
    (notInjective : ¬ Function.Injective observation) :
    KernelCoordinate observation := by
  classical
  let witness := exists_distinct_equal_images notInjective
  let left : P := Classical.choose witness
  let right : P := Classical.choose (Classical.choose_spec witness)
  have different : left ≠ right :=
    (Classical.choose_spec (Classical.choose_spec witness)).1
  have equalImages : observation left = observation right :=
    (Classical.choose_spec (Classical.choose_spec witness)).2
  let coordinate : P := left - right
  exact ⟨coordinate, sub_ne_zero.mpr different, by
    rw [map_sub, equalImages, sub_self]⟩

noncomputable def coverageCoordinateOfNotSurjective
    (observation : P →ₗ[R] O)
    (notSurjective : ¬ Function.Surjective observation) :
    CoverageCoordinate observation := by
  classical
  have existsOutside : ∃ value : O, value ∉ LinearMap.range observation := by
    by_contra impossible
    apply notSurjective
    intro value
    by_contra outside
    apply impossible
    exact ⟨value, outside⟩
  let representative : O := Classical.choose existsOutside
  have representativeOutside : representative ∉ LinearMap.range observation :=
    Classical.choose_spec existsOutside
  let coordinate : O ⧸ LinearMap.range observation :=
    Submodule.Quotient.mk representative
  have coordinateNonzero : coordinate ≠ 0 := by
    intro equality
    apply representativeOutside
    exact (Submodule.Quotient.mk_eq_zero _).mp equality
  exact ⟨coordinate, coordinateNonzero, representative, rfl,
    representativeOutside⟩

/-- The observation is the only input.  All branch evidence and coordinates
are generated internally. -/
noncomputable def settle (observation : P →ₗ[R] O) :
    Disposition observation := by
  classical
  by_cases injective : Function.Injective observation
  · by_cases surjective : Function.Surjective observation
    · exact .exact (LinearEquiv.ofBijective observation ⟨injective, surjective⟩)
    · exact .coverageOnly
        (coverageCoordinateOfNotSurjective observation surjective) injective
  · by_cases surjective : Function.Surjective observation
    · exact .kernelOnly
        (kernelCoordinateOfNotInjective observation injective) surjective
    · exact .kernelAndCoverage
        (kernelCoordinateOfNotInjective observation injective)
        (coverageCoordinateOfNotSurjective observation surjective)

theorem total (observation : P →ₗ[R] O) :
    Nonempty (Disposition observation) :=
  ⟨settle observation⟩

theorem settle_eq_exact_of_bijective
    (observation : P →ₗ[R] O)
    (bijective : Function.Bijective observation) :
    settle observation =
      .exact (LinearEquiv.ofBijective observation bijective) := by
  classical
  rcases bijective with ⟨injective, surjective⟩
  simp [settle, injective, surjective]

theorem settle_exact_iff_bijective (observation : P →ₗ[R] O) :
    (∃ equivalence : P ≃ₗ[R] O, settle observation = .exact equivalence) ↔
      Function.Bijective observation := by
  constructor
  · rintro ⟨_, settled⟩
    classical
    simp only [settle] at settled
    split at settled
    · rename_i injective
      split at settled
      · rename_i surjective
        exact ⟨injective, surjective⟩
      · cases settled
    · split at settled <;> cases settled
  · intro bijective
    exact ⟨LinearEquiv.ofBijective observation bijective,
      settle_eq_exact_of_bijective observation bijective⟩

theorem settle_eq_kernelOnly_of_not_injective_surjective
    (observation : P →ₗ[R] O)
    (notInjective : ¬ Function.Injective observation)
    (surjective : Function.Surjective observation) :
    settle observation = .kernelOnly
      (kernelCoordinateOfNotInjective observation notInjective) surjective := by
  classical
  simp [settle, notInjective, surjective]

theorem settle_eq_coverageOnly_of_injective_not_surjective
    (observation : P →ₗ[R] O)
    (injective : Function.Injective observation)
    (notSurjective : ¬ Function.Surjective observation) :
    settle observation = .coverageOnly
      (coverageCoordinateOfNotSurjective observation notSurjective) injective := by
  classical
  simp [settle, injective, notSurjective]

theorem settle_eq_kernelAndCoverage_of_neither
    (observation : P →ₗ[R] O)
    (notInjective : ¬ Function.Injective observation)
    (notSurjective : ¬ Function.Surjective observation) :
    settle observation = .kernelAndCoverage
      (kernelCoordinateOfNotInjective observation notInjective)
      (coverageCoordinateOfNotSurjective observation notSurjective) := by
  classical
  simp [settle, notInjective, notSurjective]

end
end SourceGeneratedScalarObservationDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
