import Mathlib.LinearAlgebra.Prod
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Observation.LivingLawRootGeneratedScalarObservationDispositionKernel

/-! Direct regression for all four scalar observation disposition branches. -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarObservationDispositionRegression

open SourceGeneratedScalarObservationDisposition

noncomputable section

def exactExample : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.id

theorem exactExample_is_exact :
    ∃ equivalence : ℤ ≃ₗ[ℤ] ℤ,
      settle exactExample = .exact equivalence := by
  rw [settle_exact_iff_bijective]
  exact Function.bijective_id

def kernelExample : ℤ × ℤ →ₗ[ℤ] ℤ :=
  LinearMap.fst ℤ ℤ ℤ

theorem kernelExample_not_injective :
    ¬ Function.Injective kernelExample := by
  intro injective
  have equality : kernelExample (0, 1) = kernelExample (0, 0) := rfl
  have pairEquality := injective equality
  have secondEquality := congrArg Prod.snd pairEquality
  norm_num at secondEquality

theorem kernelExample_has_nonzero_residual :
    ∃ (coordinate : KernelCoordinate kernelExample)
        (surjective : Function.Surjective kernelExample),
      settle kernelExample = .kernelOnly coordinate surjective ∧
      coordinate.coordinate ≠ 0 := by
  let coordinate := kernelCoordinateOfNotInjective kernelExample
    kernelExample_not_injective
  let surjective : Function.Surjective kernelExample :=
    LinearMap.fst_surjective
  exact ⟨coordinate, surjective,
    settle_eq_kernelOnly_of_not_injective_surjective kernelExample
      kernelExample_not_injective surjective,
    coordinate.nonzero⟩

def coverageExample : ℤ →ₗ[ℤ] ℤ × ℤ :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0

theorem coverageExample_injective :
    Function.Injective coverageExample := by
  intro left right equality
  exact congrArg Prod.fst equality

theorem coverageExample_not_surjective :
    ¬ Function.Surjective coverageExample := by
  intro surjective
  obtain ⟨value, equality⟩ := surjective (0, 1)
  have secondEquality := congrArg Prod.snd equality
  norm_num [coverageExample] at secondEquality

theorem coverageExample_has_nonzero_residual :
    ∃ (coordinate : CoverageCoordinate coverageExample)
        (injective : Function.Injective coverageExample),
      settle coverageExample = .coverageOnly coordinate injective ∧
      coordinate.coordinate ≠ 0 ∧
      coordinate.representative ∉ LinearMap.range coverageExample := by
  let coordinate := coverageCoordinateOfNotSurjective coverageExample
    coverageExample_not_surjective
  exact ⟨coordinate, coverageExample_injective,
    settle_eq_coverageOnly_of_injective_not_surjective coverageExample
      coverageExample_injective coverageExample_not_surjective,
    coordinate.nonzero, coordinate.representative_outside_range⟩

def doubleResidualExample : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ :=
  0

theorem doubleResidualExample_not_injective :
    ¬ Function.Injective doubleResidualExample := by
  intro injective
  have equality : doubleResidualExample (1, 0) =
      doubleResidualExample (0, 0) := by
    simp [doubleResidualExample]
  have pairEquality := injective equality
  have firstEquality := congrArg Prod.fst pairEquality
  norm_num at firstEquality

theorem doubleResidualExample_not_surjective :
    ¬ Function.Surjective doubleResidualExample := by
  intro surjective
  obtain ⟨value, equality⟩ := surjective (1, 0)
  have firstEquality := congrArg Prod.fst equality
  norm_num [doubleResidualExample] at firstEquality

theorem doubleResidualExample_has_both_nonzero_residuals :
    ∃ (kernelCoordinate : KernelCoordinate doubleResidualExample)
        (coverageCoordinate : CoverageCoordinate doubleResidualExample),
      settle doubleResidualExample =
          .kernelAndCoverage kernelCoordinate coverageCoordinate ∧
      kernelCoordinate.coordinate ≠ 0 ∧
      coverageCoordinate.coordinate ≠ 0 ∧
      coverageCoordinate.representative ∉
        LinearMap.range doubleResidualExample := by
  let kernelCoordinate := kernelCoordinateOfNotInjective doubleResidualExample
    doubleResidualExample_not_injective
  let coverageCoordinate :=
    coverageCoordinateOfNotSurjective doubleResidualExample
      doubleResidualExample_not_surjective
  exact ⟨kernelCoordinate, coverageCoordinate,
    settle_eq_kernelAndCoverage_of_neither doubleResidualExample
      doubleResidualExample_not_injective
      doubleResidualExample_not_surjective,
    kernelCoordinate.nonzero, coverageCoordinate.nonzero,
    coverageCoordinate.representative_outside_range⟩

#print axioms total
#print axioms settle_exact_iff_bijective
#print axioms kernelExample_has_nonzero_residual
#print axioms coverageExample_has_nonzero_residual
#print axioms doubleResidualExample_has_both_nonzero_residuals

end
end SourceGeneratedScalarObservationDispositionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
