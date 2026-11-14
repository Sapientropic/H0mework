import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Bounded.LivingLawRootGeneratedScalarBoundedObservationDispositionKernel
import H0mework.Realization.Perfectification.FiniteCompressionNoGo

/-! Direct positive and residual regressions for scalar bounded disposition. -/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarBoundedObservationDispositionRegression

open Module
open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarBoundedObservationDisposition

noncomputable section

namespace FieldExample

noncomputable def basis : Basis Unit ℚ ℚ := Basis.singleton Unit ℚ
noncomputable def evaluation : ℚ →ₗ[ℚ] Module.Dual ℚ ℚ := basis.toDual
theorem evaluation_injective : Function.Injective evaluation := basis.toDual_injective
noncomputable def observation : ExactCarrier evaluation →ₗ[ℚ] ℚ :=
  quotientToSource evaluation evaluation_injective
theorem observation_bijective : Function.Bijective observation :=
  quotientToSource_bijective evaluation evaluation_injective

theorem settles_boundedDualizable :
    ∃ (equivalence : ExactCarrier evaluation ≃ₗ[ℚ] ℚ)
      (finite : Module.Finite ℚ ℚ)
      (projective : Module.Projective ℚ ℚ)
      (duality : SourceGeneratedScalarFiniteProjectiveDuality.TensorDuality
        (R := ℚ) ℚ),
      settle evaluation observation =
        .boundedDualizable equivalence finite projective duality := by
  let equivalence := LinearEquiv.ofBijective observation observation_bijective
  let finite : Module.Finite ℚ ℚ := inferInstance
  let projective : Module.Projective ℚ ℚ := inferInstance
  let duality := SourceGeneratedScalarFiniteProjectiveDuality.generate finite projective
  exact ⟨equivalence, finite, projective, duality,
    settle_eq_boundedDualizable evaluation observation equivalence
      (SourceGeneratedScalarObservationDisposition.settle_eq_exact_of_bijective
        observation observation_bijective) finite projective⟩

theorem point_ne_zero : canonicalMap evaluation (1 : ℚ) ≠ 0 := by
  intro equality
  have observed := congrArg observation equality
  change (1 : ℚ) = 0 at observed
  exact one_ne_zero observed

def doubleResidualObservation : ExactCarrier evaluation →ₗ[ℚ] ℚ × ℚ := 0

theorem doubleResidual_not_injective :
    ¬ Function.Injective doubleResidualObservation := by
  intro injective
  apply point_ne_zero
  apply injective
  simp [doubleResidualObservation]

theorem doubleResidual_not_surjective :
    ¬ Function.Surjective doubleResidualObservation := by
  intro surjective
  obtain ⟨value, equality⟩ := surjective ((1, 0) : ℚ × ℚ)
  have first := congrArg Prod.fst equality
  norm_num [doubleResidualObservation] at first

theorem doubleResidual_passes_through :
    ∃ (kernelCoordinate :
        SourceGeneratedScalarObservationDisposition.KernelCoordinate
          doubleResidualObservation)
      (coverageCoordinate :
        SourceGeneratedScalarObservationDisposition.CoverageCoordinate
          doubleResidualObservation),
      settle evaluation doubleResidualObservation =
        .kernelAndCoverage kernelCoordinate coverageCoordinate ∧
      kernelCoordinate.coordinate ≠ 0 ∧ coverageCoordinate.coordinate ≠ 0 := by
  let kernelCoordinate :=
    SourceGeneratedScalarObservationDisposition.kernelCoordinateOfNotInjective
      doubleResidualObservation doubleResidual_not_injective
  let coverageCoordinate :=
    SourceGeneratedScalarObservationDisposition.coverageCoordinateOfNotSurjective
      doubleResidualObservation doubleResidual_not_surjective
  refine ⟨kernelCoordinate, coverageCoordinate, ?_, kernelCoordinate.coordinate_ne_zero,
    coverageCoordinate.coordinate_ne_zero⟩
  exact settle_eq_kernelAndCoverage evaluation doubleResidualObservation
    kernelCoordinate coverageCoordinate
    (SourceGeneratedScalarObservationDisposition.settle_eq_kernelAndCoverage_of_neither
      doubleResidualObservation
        doubleResidual_not_injective doubleResidual_not_surjective)

end FieldExample

namespace ZModFourExample

abbrev R4 := ZMod 4
noncomputable def basis : Basis Unit R4 R4 := Basis.singleton Unit R4
noncomputable def evaluation : R4 →ₗ[R4] Module.Dual R4 R4 :=
  basis.toDual.comp (LinearMap.mulLeft R4 2)
abbrev Carrier := ExactCarrier evaluation
def observation : Carrier →ₗ[R4] Carrier := LinearMap.id
theorem carrier_finite : Module.Finite R4 Carrier := inferInstance

theorem carrier_not_projective : ¬ Module.Projective R4 Carrier := by
  intro projective
  letI : Module.Projective R4 Carrier := projective
  let quotientMap : R4 →ₗ[R4] Carrier := canonicalMap evaluation
  obtain ⟨splitting, splittingLaw⟩ := Module.projective_lifting_property
    quotientMap LinearMap.id (Submodule.mkQ_surjective (LinearMap.ker evaluation))
  let point : Carrier := quotientMap 1
  have quotient_splitting : quotientMap (splitting point) = point :=
    LinearMap.congr_fun splittingLaw point
  have two_mem_kernel : (2 : R4) ∈ LinearMap.ker evaluation := by
    rw [LinearMap.mem_ker]
    change basis.toDual ((2 : R4) * 2) = 0
    have two_mul_two : (2 : R4) * 2 = 0 := by decide
    rw [two_mul_two, map_zero]
  have quotient_two_zero : quotientMap 2 = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 two_mem_kernel
  have point_torsion : (2 : R4) • point = 0 := by
    change (2 : R4) • quotientMap 1 = 0
    rw [← map_smul, smul_eq_mul, mul_one, quotient_two_zero]
  have splitting_torsion : (2 : R4) • splitting point = 0 := by
    rw [← map_smul, point_torsion, map_zero]
  have evaluationEquality : evaluation (splitting point) = evaluation 1 := by
    have equality := congrArg (dualEmbedding evaluation) quotient_splitting
    change evaluation (splitting point) = evaluation 1 at equality
    exact equality
  have weightedEquality : (2 : R4) * splitting point = 2 := by
    apply basis.toDual_injective
    simpa [evaluation, LinearMap.mulLeft_apply] using evaluationEquality
  have weightedZero : (2 : R4) * splitting point = 0 := by
    simpa [smul_eq_mul] using splitting_torsion
  exact (by decide : (2 : R4) ≠ 0) (weightedEquality.symm.trans weightedZero)

theorem settles_finiteNonprojective :
    ∃ (equivalence : Carrier ≃ₗ[R4] Carrier)
      (finite : Module.Finite R4 Carrier)
      (notProjective : ¬ Module.Projective R4 Carrier),
      settle evaluation observation =
        .finiteNonprojective equivalence finite notProjective := by
  let equivalence := LinearEquiv.ofBijective observation Function.bijective_id
  exact ⟨equivalence, carrier_finite, carrier_not_projective,
    settle_eq_finiteNonprojective evaluation observation equivalence
      (SourceGeneratedScalarObservationDisposition.settle_eq_exact_of_bijective
        observation Function.bijective_id) carrier_finite carrier_not_projective⟩

end ZModFourExample

namespace InfiniteExample

abbrev Carrier := ℕ →₀ ℤ
noncomputable def basis : Basis ℕ ℤ Carrier := Finsupp.basisSingleOne
noncomputable def evaluation : Carrier →ₗ[ℤ] Module.Dual ℤ Carrier := basis.toDual
theorem evaluation_injective : Function.Injective evaluation := basis.toDual_injective
noncomputable def observation : ExactCarrier evaluation →ₗ[ℤ] Carrier :=
  quotientToSource evaluation evaluation_injective
theorem observation_bijective : Function.Bijective observation :=
  quotientToSource_bijective evaluation evaluation_injective

theorem settles_nonfinite :
    ∃ (equivalence : ExactCarrier evaluation ≃ₗ[ℤ] Carrier)
      (notFinite : ¬ Module.Finite ℤ Carrier),
      settle evaluation observation = .nonfinite equivalence notFinite := by
  let equivalence := LinearEquiv.ofBijective observation observation_bijective
  let notFinite : ¬ Module.Finite ℤ Carrier :=
    CofinalPerfectCompressionNoGo.natFinsupp_not_moduleFinite
  exact ⟨equivalence, notFinite,
    settle_eq_nonfinite evaluation observation equivalence
      (SourceGeneratedScalarObservationDisposition.settle_eq_exact_of_bijective
        observation observation_bijective) notFinite⟩

end InfiniteExample

#print axioms SourceGeneratedScalarFiniteProjectiveDuality.generate
#print axioms SourceGeneratedScalarBoundedObservationDisposition.settle
#print axioms FieldExample.settles_boundedDualizable
#print axioms FieldExample.doubleResidual_passes_through
#print axioms ZModFourExample.carrier_not_projective
#print axioms ZModFourExample.settles_finiteNonprojective
#print axioms InfiniteExample.settles_nonfinite

end
end SourceGeneratedScalarBoundedObservationDispositionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
