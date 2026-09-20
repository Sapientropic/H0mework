import Mathlib.Analysis.Normed.Operator.Extend
import H0mework.Realization.Coherent.Completion

/-!
# Integral action and coherent Hilbert covariance

An actual integral transition and an owner-free Hilbert isometry are tested
against the same actual feature.  Exact covariance generates the canonical
isometric action on the coherent completion.  Failure retains an explicit
integral event and its nonzero coupling residual.  Nothing here assumes a
finite presentation, projectivity, determinant eligibility, or vanishing
residual.
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

/-- Same-carrier integral transition and owner-free coherent evolution. -/
structure ActionData (feature : L →ₗ[ℤ] H) where
  integralTransition : L →ₗ[ℤ] L
  hilbertEvolution : H →ₗᵢ[ℂ] H

/-- Exact event-coordinate mismatch between coherent evolution and the
integral transition. -/
def couplingResidual {feature : L →ₗ[ℤ] H}
    (action : ActionData feature) (event : L) : H :=
  action.hilbertEvolution (feature event) -
    feature (action.integralTransition event)

theorem couplingResidual_eq_zero_iff
    {feature : L →ₗ[ℤ] H} (action : ActionData feature) (event : L) :
    couplingResidual action event = 0 ↔
      action.hilbertEvolution (feature event) =
        feature (action.integralTransition event) := by
  exact sub_eq_zero

/-- Radial/energy readout of the coupling mismatch.  It forgets phase and
direction, so its vanishing is strictly weaker than vector covariance. -/
def radialResidual {feature : L →ₗ[ℤ] H}
    (action : ActionData feature) (event : L) : ℝ :=
  ‖action.hilbertEvolution (feature event)‖ -
    ‖feature (action.integralTransition event)‖

theorem radialResidual_eq_zero_iff
    {feature : L →ₗ[ℤ] H} (action : ActionData feature) (event : L) :
    radialResidual action event = 0 ↔
      ‖action.hilbertEvolution (feature event)‖ =
        ‖feature (action.integralTransition event)‖ := by
  exact sub_eq_zero

theorem couplingResidual_zero_implies_radialResidual_zero
    {feature : L →ₗ[ℤ] H} (action : ActionData feature) (event : L)
    (strict : couplingResidual action event = 0) :
    radialResidual action event = 0 := by
  rw [radialResidual_eq_zero_iff]
  exact congrArg norm ((couplingResidual_eq_zero_iff action event).mp strict)

theorem radialResidual_ne_zero_implies_couplingResidual_ne_zero
    {feature : L →ₗ[ℤ] H} (action : ActionData feature) (event : L)
    (radial : radialResidual action event ≠ 0) :
    couplingResidual action event ≠ 0 := by
  intro strict
  exact radial
    (couplingResidual_zero_implies_radialResidual_zero action event strict)

/-- Complex-linear scalar extension of the integral transition. -/
def complexifiedTransition {feature : L →ₗ[ℤ] H}
    (action : ActionData feature) :
    ComplexifiedCarrier L →ₗ[ℂ] ComplexifiedCarrier L :=
  TensorProduct.AlgebraTensorModule.map LinearMap.id
    action.integralTransition

@[simp] theorem complexifiedTransition_tmul
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (coefficient : ℂ) (event : L) :
    complexifiedTransition action (coefficient ⊗ₜ[ℤ] event) =
      coefficient ⊗ₜ[ℤ] action.integralTransition event := by
  rw [complexifiedTransition, TensorProduct.AlgebraTensorModule.map_tmul]
  rfl

theorem complexified_covariance
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    action.hilbertEvolution.toLinearMap.comp
        (complexifiedFeature feature) =
      (complexifiedFeature feature).comp
        (complexifiedTransition action) := by
  apply LinearMap.ext
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp
  | add left right left_ih right_ih =>
      simpa only [map_add] using congrArg₂ (· + ·) left_ih right_ih
  | tmul coefficient event =>
      have event_covariance :=
        (couplingResidual_eq_zero_iff action event).mp (covariant event)
      change action.hilbertEvolution (coefficient • feature event) =
        coefficient • feature (action.integralTransition event)
      rw [map_smul, event_covariance]

theorem hilbertEvolution_maps_complexified_range
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : LinearMap.range (complexifiedFeature feature)) :
    action.hilbertEvolution value.1 ∈
      LinearMap.range (complexifiedFeature feature) := by
  obtain ⟨source, source_eq⟩ := value.2
  refine ⟨complexifiedTransition action source, ?_⟩
  rw [← source_eq]
  exact (LinearMap.congr_fun
    (complexified_covariance action covariant) source).symm

/-- The exact-covariance action restricted to the actual complex feature
range. -/
def coherentRangeAction
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    LinearMap.range (complexifiedFeature feature) →ₗᵢ[ℂ]
      LinearMap.range (complexifiedFeature feature) where
  toLinearMap :=
    ((action.hilbertEvolution.toLinearMap.domRestrict
      (LinearMap.range (complexifiedFeature feature))).codRestrict
        (LinearMap.range (complexifiedFeature feature))
        (hilbertEvolution_maps_complexified_range action covariant))
  norm_map' value := action.hilbertEvolution.norm_map value.1

@[simp] theorem coherentRangeAction_apply
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : LinearMap.range (complexifiedFeature feature)) :
    ((coherentRangeAction action covariant value :
        LinearMap.range (complexifiedFeature feature)) : H) =
      action.hilbertEvolution value.1 := by
  rfl

/-- Named dense embedding of the actual complex feature range into its
coherent completion. -/
def coherentRangeEmbedding (feature : L →ₗ[ℤ] H) :
    LinearMap.range (complexifiedFeature feature) →L[ℂ]
      CoherentCompletion feature :=
  (UniformSpace.Completion.toComplₗᵢ :
    LinearMap.range (complexifiedFeature feature) →ₗᵢ[ℂ]
      CoherentCompletion feature).toContinuousLinearMap

theorem coherentRangeEmbedding_denseRange (feature : L →ₗ[ℤ] H) :
    DenseRange (coherentRangeEmbedding feature) :=
  UniformSpace.Completion.denseRange_coe

theorem coherentRangeEmbedding_isUniformInducing
    (feature : L →ₗ[ℤ] H) :
    IsUniformInducing (coherentRangeEmbedding feature) :=
  (UniformSpace.Completion.toComplₗᵢ :
    LinearMap.range (complexifiedFeature feature) →ₗᵢ[ℂ]
      CoherentCompletion feature).isometry.isUniformInducing

/-- Canonical continuous extension of the exact range action to the coherent
completion. -/
def coherentCompletionActionCLM
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    CoherentCompletion feature →L[ℂ] CoherentCompletion feature :=
  ((coherentRangeEmbedding feature).comp
    (coherentRangeAction action covariant).toContinuousLinearMap).extend
      (coherentRangeEmbedding feature)

@[simp] theorem coherentCompletionActionCLM_range_readback
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : LinearMap.range (complexifiedFeature feature)) :
    coherentCompletionActionCLM action covariant
        (coherentRangeEmbedding feature value) =
      coherentRangeEmbedding feature
        (coherentRangeAction action covariant value) := by
  rw [coherentCompletionActionCLM, ContinuousLinearMap.extend_eq
    ((coherentRangeEmbedding feature).comp
      (coherentRangeAction action covariant).toContinuousLinearMap)
    (coherentRangeEmbedding_denseRange feature)
    (coherentRangeEmbedding_isUniformInducing feature)]
  rfl

theorem coherentCompletionActionCLM_norm
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : CoherentCompletion feature) :
    ‖coherentCompletionActionCLM action covariant value‖ = ‖value‖ := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (continuous_norm.comp
          (coherentCompletionActionCLM action covariant).continuous)
        continuous_norm
  | ih rangeValue =>
      change ‖coherentCompletionActionCLM action covariant
          (coherentRangeEmbedding feature rangeValue)‖ =
        ‖coherentRangeEmbedding feature rangeValue‖
      rw [coherentCompletionActionCLM_range_readback]
      simp [coherentRangeEmbedding]

/-- Canonical isometric action generated by exact covariance. -/
def coherentCompletionAction
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0) :
    CoherentCompletion feature →ₗᵢ[ℂ] CoherentCompletion feature where
  toLinearMap := (coherentCompletionActionCLM action covariant).toLinearMap
  norm_map' := coherentCompletionActionCLM_norm action covariant

@[simp] theorem coherentCompletionAction_apply
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : CoherentCompletion feature) :
    coherentCompletionAction action covariant value =
      coherentCompletionActionCLM action covariant value := by
  rfl

@[simp] theorem coherentCompletionAction_complexified_source
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : ComplexifiedCarrier L) :
    coherentCompletionAction action covariant
        (canonicalHilbertMap (complexifiedFeature feature) value) =
      canonicalHilbertMap (complexifiedFeature feature)
        (complexifiedTransition action value) := by
  change coherentCompletionActionCLM action covariant
      (coherentRangeEmbedding feature
        ((complexifiedFeature feature).rangeRestrict value)) = _
  rw [coherentCompletionActionCLM_range_readback]
  change coherentRangeEmbedding feature
      (coherentRangeAction action covariant
        ((complexifiedFeature feature).rangeRestrict value)) =
    coherentRangeEmbedding feature
      ((complexifiedFeature feature).rangeRestrict
        (complexifiedTransition action value))
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (complexified_covariance action covariant) value

@[simp] theorem coherentCompletionAction_discrete_source
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (event : L) :
    coherentCompletionAction action covariant
        (discreteToCoherentCompletion feature event) =
      discreteToCoherentCompletion feature
        (action.integralTransition event) := by
  change coherentCompletionAction action covariant
      (canonicalHilbertMap (complexifiedFeature feature)
        (1 ⊗ₜ[ℤ] event)) =
    canonicalHilbertMap (complexifiedFeature feature)
      (1 ⊗ₜ[ℤ] action.integralTransition event)
  rw [coherentCompletionAction_complexified_source,
    complexifiedTransition_tmul]

theorem coherentCompletionAction_realization
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
    [CompleteSpace H]
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (value : CoherentCompletion feature) :
    coherentCompletionRealization feature
        (coherentCompletionAction action covariant value) =
      action.hilbertEvolution
        (coherentCompletionRealization feature value) := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((coherentCompletionRealization feature).continuous.comp
          (coherentCompletionAction action covariant).continuous)
        (action.hilbertEvolution.continuous.comp
          (coherentCompletionRealization feature).continuous)
  | ih rangeValue =>
      change coherentCompletionRealization feature
          (coherentCompletionActionCLM action covariant
            (coherentRangeEmbedding feature rangeValue)) =
        action.hilbertEvolution
          (coherentCompletionRealization feature
            (coherentRangeEmbedding feature rangeValue))
      rw [coherentCompletionActionCLM_range_readback]
      change hilbertAmbientRealization (complexifiedFeature feature)
          (coherentRangeEmbedding feature
            (coherentRangeAction action covariant rangeValue)) =
        action.hilbertEvolution
          (hilbertAmbientRealization (complexifiedFeature feature)
            (coherentRangeEmbedding feature rangeValue))
      rw [show coherentRangeEmbedding feature
            (coherentRangeAction action covariant rangeValue) =
          (coherentRangeAction action covariant rangeValue :
            LinearMap.range (complexifiedFeature feature)) by rfl,
        show coherentRangeEmbedding feature rangeValue =
          (rangeValue : CoherentCompletion feature) by rfl,
        hilbertAmbientRealization_range_readback,
        hilbertAmbientRealization_range_readback]
      exact coherentRangeAction_apply action covariant rangeValue

/-- Total vector/radial covariance disposition.  Strict vector covariance
generates the completion action.  A radially neutral but vector-noncovariant
system retains an explicit phase/direction representation residual.  The
remaining branch retains an event whose radial/energy readout is nonzero. -/
inductive CovarianceDisposition [CompleteSpace H]
    {feature : L →ₗ[ℤ] H} (action : ActionData feature)
  | coherent
      (ambientAction : CoherentCompletion feature →ₗᵢ[ℂ]
        CoherentCompletion feature)
      (source_commutes : ∀ event : L,
        ambientAction (discreteToCoherentCompletion feature event) =
          discreteToCoherentCompletion feature
            (action.integralTransition event))
      (realization_commutes : ∀ value : CoherentCompletion feature,
        coherentCompletionRealization feature (ambientAction value) =
          action.hilbertEvolution
            (coherentCompletionRealization feature value))
  | radialNeutral
      (representationResidual :
        {event : L // couplingResidual action event ≠ 0})
      (radial_neutral : ∀ event : L, radialResidual action event = 0)
  | radialResidual
      (coordinate : {event : L // radialResidual action event ≠ 0})

/-- No branch is assumed.  Exact vector covariance generates the canonical
coherent action.  Pure phase/direction loss remains visible even when every
radial coordinate is neutral; otherwise a nonzero radial event is retained. -/
def settleCovariance
    {feature : L →ₗ[ℤ] H} [CompleteSpace H]
    (action : ActionData feature) :
    CovarianceDisposition action := by
  classical
  by_cases covariant : ∀ event : L, couplingResidual action event = 0
  · exact .coherent
      (coherentCompletionAction action covariant)
      (coherentCompletionAction_discrete_source action covariant)
      (coherentCompletionAction_realization action covariant)
  · push Not at covariant
    let representationResidual :
        {event : L // couplingResidual action event ≠ 0} :=
      ⟨Classical.choose covariant, Classical.choose_spec covariant⟩
    by_cases radialNeutral : ∀ event : L, radialResidual action event = 0
    · exact .radialNeutral representationResidual radialNeutral
    · push Not at radialNeutral
      exact .radialResidual
        ⟨Classical.choose radialNeutral,
          Classical.choose_spec radialNeutral⟩

end

end SourceGeneratedIntegralCoherentCovariance
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
