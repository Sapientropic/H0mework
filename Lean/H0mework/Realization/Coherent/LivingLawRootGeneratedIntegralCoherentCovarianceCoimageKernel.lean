import H0mework.Realization.Coherent.LivingLawRootGeneratedIntegralCoherentCovarianceEquivKernel

/-!
# Covariant action on the generated energy coimage

Exact integral/coherent covariance preserves the feature radical.  It
therefore generates, without a caller-supplied quotient action, the action on
the algebraic feature coimage and its commuting square with the coherent
completion.  Any integral eigenmeasurement that kills the same radical then
descends with its exact character law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCoherentCovariance

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedIntegralCoherentCompletion

noncomputable section

universe l h

variable {L : Type l} [AddCommGroup L]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem complexifiedTransition_maps_radical
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    gramRadical (complexifiedFeature feature) ≤
      (gramRadical (complexifiedFeature feature)).comap
        (complexifiedTransition action) := by
  intro value valueMem
  rw [LinearMap.mem_ker] at valueMem
  change complexifiedTransition action value ∈
    gramRadical (complexifiedFeature feature)
  rw [LinearMap.mem_ker]
  have square := LinearMap.congr_fun
    (complexified_covariance action covariant) value
  change action.hilbertEvolution (complexifiedFeature feature value) =
    complexifiedFeature feature (complexifiedTransition action value) at square
  rw [valueMem, map_zero] at square
  exact square.symm

/-- Action generated on the faithful algebraic energy coimage. -/
def coherentCoimageAction
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    Carrier (complexifiedFeature feature) →ₗ[ℂ]
      Carrier (complexifiedFeature feature) :=
  (gramRadical (complexifiedFeature feature)).mapQ
    (gramRadical (complexifiedFeature feature))
    (complexifiedTransition action)
    (complexifiedTransition_maps_radical action covariant)

@[simp] theorem coherentCoimageAction_canonicalMap
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    (coherentCoimageAction action covariant).comp
        (canonicalMap (complexifiedFeature feature)) =
      (canonicalMap (complexifiedFeature feature)).comp
        (complexifiedTransition action) := by
  apply LinearMap.ext
  intro value
  rfl

theorem faithfulFeature_coherentCoimageAction
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    (faithfulFeature (complexifiedFeature feature)).comp
        (coherentCoimageAction action covariant) =
      action.hilbertEvolution.toLinearMap.comp
        (faithfulFeature (complexifiedFeature feature)) := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := Submodule.mkQ_surjective
    (gramRadical (complexifiedFeature feature)) value
  have square := LinearMap.congr_fun
    (complexified_covariance action covariant) source
  change complexifiedFeature feature (complexifiedTransition action source) =
    action.hilbertEvolution (complexifiedFeature feature source)
  exact square.symm

/-- The algebraic coimage action and completed action are sibling faces of
the same source transition. -/
theorem coherentCompletionAction_coimage
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    (coherentCompletionAction action covariant).toLinearMap.comp
        (carrierToHilbertAmbient (complexifiedFeature feature)) =
      (carrierToHilbertAmbient (complexifiedFeature feature)).comp
        (coherentCoimageAction action covariant) := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := Submodule.mkQ_surjective
    (gramRadical (complexifiedFeature feature)) value
  have actionSource := coherentCompletionAction_complexified_source
    action covariant source
  change coherentCompletionAction action covariant
      (canonicalHilbertMap (complexifiedFeature feature) source) =
    canonicalHilbertMap (complexifiedFeature feature)
      (complexifiedTransition action source)
  exact actionSource

/-- An integral character law extends canonically across complexification. -/
theorem complexifiedIntegralMeasurement_eigenlaw
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (measurement : L →ₗ[ℤ] ℂ) (character : ℂ)
    (eigenlaw : ∀ event : L,
      measurement (action.integralTransition event) =
        character * measurement event) :
    (complexifiedLinearMap measurement).comp
        (complexifiedTransition action) =
      character • complexifiedLinearMap measurement := by
  apply LinearMap.ext
  intro source
  induction source using TensorProduct.induction_on with
  | zero => simp
  | add left right left_ih right_ih =>
      simpa only [map_add] using congrArg₂ (· + ·) left_ih right_ih
  | tmul coefficient event =>
      rw [LinearMap.comp_apply, complexifiedTransition_tmul,
        complexifiedLinearMap_tmul, LinearMap.smul_apply,
        complexifiedLinearMap_tmul, eigenlaw]
      simp only [smul_eq_mul]
      ring

/-- A compatible algebraic measurement descends to the energy coimage with
the same generated character law. -/
theorem coherentCoimageFactor_eigenlaw
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (measurement : L →ₗ[ℤ] ℂ) (character : ℂ)
    (kills_radical : LinearMap.ker (complexifiedFeature feature) ≤
      LinearMap.ker (complexifiedLinearMap measurement))
    (eigenlaw : ∀ event : L,
      measurement (action.integralTransition event) =
        character * measurement event) :
    (canonicalFactor (complexifiedFeature feature)
        (complexifiedLinearMap measurement) kills_radical).comp
        (coherentCoimageAction action covariant) =
      character • canonicalFactor (complexifiedFeature feature)
        (complexifiedLinearMap measurement) kills_radical := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := Submodule.mkQ_surjective
    (gramRadical (complexifiedFeature feature)) value
  change canonicalFactor (complexifiedFeature feature)
      (complexifiedLinearMap measurement) kills_radical
      (coherentCoimageAction action covariant
        (canonicalMap (complexifiedFeature feature) source)) =
    character * canonicalFactor (complexifiedFeature feature)
      (complexifiedLinearMap measurement) kills_radical
      (canonicalMap (complexifiedFeature feature) source)
  have actionSource := LinearMap.congr_fun
    (coherentCoimageAction_canonicalMap action covariant) source
  have complexEigen := LinearMap.congr_fun
    (complexifiedIntegralMeasurement_eigenlaw action measurement character
      eigenlaw) source
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at actionSource
  rw [LinearMap.smul_apply] at complexEigen
  rw [actionSource]
  change complexifiedLinearMap measurement
      (complexifiedTransition action source) =
    character * complexifiedLinearMap measurement source
  exact complexEigen

end

end SourceGeneratedIntegralCoherentCovariance
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
