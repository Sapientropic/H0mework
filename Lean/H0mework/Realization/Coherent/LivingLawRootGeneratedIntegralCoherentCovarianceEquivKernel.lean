import H0mework.Realization.Coherent.Covariance

/-!
# Invertible integral/coherent covariance on the generated completion

When the source transition and the coherent evolution are actual
equivalences, exact forward covariance also generates inverse covariance.
The canonical action on the source-generated coherent completion therefore
upgrades from a one-sided isometry to an isometric equivalence.  No
surjectivity, inverse action, or completed carrier is supplied separately.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCoherentCovariance

open SourceGeneratedIntegralCoherentCompletion

noncomputable section

universe l h

variable {L : Type l} [AddCommGroup L]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Same-source invertible transition and coherent evolution. -/
structure EquivActionData (feature : L →ₗ[ℤ] H) where
  integralTransition : L ≃ₗ[ℤ] L
  hilbertEvolution : H ≃ₗᵢ[ℂ] H

def EquivActionData.toActionData
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature) :
    ActionData feature where
  integralTransition := action.integralTransition.toLinearMap
  hilbertEvolution := action.hilbertEvolution.toLinearIsometry

def EquivActionData.symm
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature) :
    EquivActionData feature where
  integralTransition := action.integralTransition.symm
  hilbertEvolution := action.hilbertEvolution.symm

/-- Forward covariance of equivalences determines inverse covariance; the
caller cannot independently choose a second inverse square. -/
theorem EquivActionData.symm_covariant
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature)
    (covariant : ∀ event : L,
      couplingResidual action.toActionData event = 0)
    (event : L) :
    couplingResidual action.symm.toActionData event = 0 := by
  rw [couplingResidual_eq_zero_iff]
  have forward := (couplingResidual_eq_zero_iff action.toActionData
    (action.integralTransition.symm event)).mp
      (covariant (action.integralTransition.symm event))
  have forward' :
      action.hilbertEvolution
          (feature (action.integralTransition.symm event)) =
        feature event := by
    change action.hilbertEvolution
        (feature (action.integralTransition.symm event)) =
      feature
        (action.integralTransition
          (action.integralTransition.symm event)) at forward
    rw [action.integralTransition.apply_symm_apply] at forward
    exact forward
  change action.hilbertEvolution.symm (feature event) =
    feature (action.integralTransition.symm event)
  calc
    action.hilbertEvolution.symm (feature event) =
        action.hilbertEvolution.symm
          (action.hilbertEvolution
            (feature (action.integralTransition.symm event))) := by
      exact congrArg action.hilbertEvolution.symm forward'.symm
    _ = feature (action.integralTransition.symm event) :=
      action.hilbertEvolution.symm_apply_apply _

variable [CompleteSpace H]

/-- The two source-generated completion actions are mutual inverses. -/
def coherentCompletionActionLinearEquiv
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature)
    (covariant : ∀ event : L,
      couplingResidual action.toActionData event = 0) :
    CoherentCompletion feature ≃ₗ[ℂ] CoherentCompletion feature where
  toFun := coherentCompletionAction action.toActionData covariant
  invFun := coherentCompletionAction action.symm.toActionData
    (action.symm_covariant covariant)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv value := by
    apply coherentCompletionRealization_injective feature
    rw [coherentCompletionAction_realization action.symm.toActionData
        (action.symm_covariant covariant),
      coherentCompletionAction_realization action.toActionData covariant]
    exact action.hilbertEvolution.symm_apply_apply
      (coherentCompletionRealization feature value)
  right_inv value := by
    apply coherentCompletionRealization_injective feature
    rw [coherentCompletionAction_realization action.toActionData covariant,
      coherentCompletionAction_realization action.symm.toActionData
        (action.symm_covariant covariant)]
    exact action.hilbertEvolution.apply_symm_apply
      (coherentCompletionRealization feature value)

/-- Canonical isometric equivalence generated on the coherent completion. -/
def coherentCompletionActionEquiv
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature)
    (covariant : ∀ event : L,
      couplingResidual action.toActionData event = 0) :
    CoherentCompletion feature ≃ₗᵢ[ℂ] CoherentCompletion feature :=
  ⟨coherentCompletionActionLinearEquiv action covariant,
    (coherentCompletionAction action.toActionData covariant).norm_map⟩

@[simp] theorem coherentCompletionActionEquiv_apply
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature)
    (covariant : ∀ event : L,
      couplingResidual action.toActionData event = 0)
    (value : CoherentCompletion feature) :
    coherentCompletionActionEquiv action covariant value =
      coherentCompletionAction action.toActionData covariant value :=
  rfl

@[simp] theorem coherentCompletionActionEquiv_discrete_source
    {feature : L →ₗ[ℤ] H} (action : EquivActionData feature)
    (covariant : ∀ event : L,
      couplingResidual action.toActionData event = 0)
    (event : L) :
    coherentCompletionActionEquiv action covariant
        (discreteToCoherentCompletion feature event) =
      discreteToCoherentCompletion feature
        (action.integralTransition event) := by
  exact coherentCompletionAction_discrete_source
    action.toActionData covariant event

end

end SourceGeneratedIntegralCoherentCovariance
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
