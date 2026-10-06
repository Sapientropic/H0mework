import H0mework.Realization.Coherent.Covariance
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedCovarianceExecution
open SourceGeneratedIntegralCoherentCompletion SourceGeneratedIntegralCoherentCovariance
variable {L H : Type u} [AddCommGroup L]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (feature : L →ₗ[ℤ] H) (action : ActionData feature)
def sourcePoint (datum : CovarianceDisposition action) (point : L) : L :=
  match datum with
  | .coherent _ _ _ => point
  | .radialNeutral coordinate _ | .radialResidual coordinate => coordinate.val
def forward (datum : CovarianceDisposition action) : L →+ CoherentCompletion feature :=
  match datum with
  | .coherent advance _ _ => advance.toLinearMap.restrictScalars ℤ |>.toAddMonoidHom.comp (discreteToCoherentCompletion feature).toAddMonoidHom
  | .radialNeutral _ _ | .radialResidual _ => (discreteToCoherentCompletion feature).toAddMonoidHom.comp action.integralTransition.toAddMonoidHom

theorem forward_source (datum : CovarianceDisposition action) (point : L) :
    coherentCompletionRealization feature (forward feature action datum point) = feature (action.integralTransition point) := by
  cases datum with
  | coherent advance sourceSquare realizationSquare =>
    exact (congrArg (coherentCompletionRealization feature) (sourceSquare point)).trans
      (discreteToCoherentCompletion_actual_readback feature _)
  | radialNeutral _ _ | radialResidual _ => exact discreteToCoherentCompletion_actual_readback feature _
theorem selected_coherent (point : L)
    (advance : CoherentCompletion feature →ₗᵢ[ℂ] CoherentCompletion feature)
    (sourceSquare : ∀ event : L, advance (discreteToCoherentCompletion feature event)=discreteToCoherentCompletion feature (action.integralTransition event))
    (realizationSquare : ∀ value : CoherentCompletion feature,
      coherentCompletionRealization feature (advance value)=action.hilbertEvolution (coherentCompletionRealization feature value)) :
    couplingResidual action (sourcePoint feature action (.coherent advance sourceSquare realizationSquare) point)=0 := by
  rw [couplingResidual_eq_zero_iff]
  have given := realizationSquare (discreteToCoherentCompletion feature point)
  rw [sourceSquare,discreteToCoherentCompletion_actual_readback,discreteToCoherentCompletion_actual_readback] at given
  exact given.symm

theorem selected_phase (point : L)
    (coordinate : {event : L // couplingResidual action event ≠ 0})
    (radialNeutral : ∀ event : L, radialResidual action event=0) :
    couplingResidual action (sourcePoint feature action (.radialNeutral coordinate radialNeutral) point) ≠ 0 := coordinate.property

theorem selected_radial (point : L)
    (coordinate : {event : L // radialResidual action event ≠ 0}) :
    couplingResidual action (sourcePoint feature action (.radialResidual coordinate) point) ≠ 0 := by
  intro zero
  exact coordinate.property (couplingResidual_zero_implies_radialResidual_zero action coordinate.val zero)
def EffectPredicate (datum : CovarianceDisposition action) (value : H) : Prop :=
  match datum with
  | .coherent _ _ _ => value=0
  | .radialNeutral _ _ | .radialResidual _ => value≠0

theorem source_effect_predicate (datum : CovarianceDisposition action) (point : L) :
    EffectPredicate feature action datum (couplingResidual action (sourcePoint feature action datum point)) := by
  cases datum with
  | coherent advance sourceSquare realizationSquare => exact selected_coherent _ _ _ advance sourceSquare realizationSquare
  | radialNeutral coordinate neutral => exact selected_phase _ _ _ coordinate neutral
  | radialResidual coordinate => exact selected_radial _ _ _ coordinate
end SourceGeneratedCovarianceExecution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
