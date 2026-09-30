import H0mework.Realization.OccurrenceCharge.Source

/-! The original autonomous Model consumes the source-generated charge action and its exact full kernel. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceAccountedAction

open SourceOwnedObservationHistory SourceGeneratedActionObservationHistory

noncomputable section
universe u
variable {State Account : Type u} [AddCommGroup Account]

def occurrenceUpdate (step : State → State) (material : RootedAccountedUnfolding State) :
    RootedAccountedUnfolding State :=
  material.advance (fun state => .zero (step state))

theorem source_square (step : State → State) (charge : State → Account) :
    (observation (retained charge)).comp (sourceAction (occurrenceUpdate step)) =
      (update step charge).comp (observation (retained charge)) := by
  apply Finsupp.lhom_ext'
  intro material
  apply LinearMap.ext_ring
  change observation (retained charge) (sourceAction (occurrenceUpdate step) (sourcePoint material)) =
    update step charge (observation (retained charge) (sourcePoint material))
  rw [sourceAction_point, observation_point, observation_point]
  exact (retained_advance step charge material).symm

theorem kernel_exact (step : State → State) (charge : State → Account) :
    LinearMap.ker (sourceMap (sourceAction (occurrenceUpdate step)) (observation (retained charge))) =
      LinearMap.ker (observation (retained charge)) :=
  current_kernel_is_complete _ _ step charge (source_square step charge)

theorem model_fibre (step : State → State) (charge : State → Account)
    (left right : Carrier (RootedAccountedUnfolding State)) :
    projection (sourceAction (occurrenceUpdate step)) (observation (retained charge)) left =
      projection (sourceAction (occurrenceUpdate step)) (observation (retained charge)) right ↔
        observation (retained charge) left = observation (retained charge) right := by
  change (LinearMap.ker (sourceMap (sourceAction (occurrenceUpdate step)) (observation (retained charge)))).mkQ left =
    (LinearMap.ker (sourceMap (sourceAction (occurrenceUpdate step)) (observation (retained charge)))).mkQ right ↔ _
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    kernel_exact, LinearMap.mem_ker, map_sub, sub_eq_zero]

theorem model_next (step : State → State) (charge : State → Account) (material : RootedAccountedUnfolding State) :
    modelAction (sourceAction (occurrenceUpdate step)) (observation (retained charge))
      (projection (sourceAction (occurrenceUpdate step)) (observation (retained charge)) (sourcePoint material)) =
    projection (sourceAction (occurrenceUpdate step)) (observation (retained charge))
      (sourcePoint (occurrenceUpdate step material)) := by
  rw [modelAction_source, sourceAction_point]

theorem model_point_fibre (step : State → State) (charge : State → Account)
    (left right : RootedAccountedUnfolding State) :
    projection (sourceAction (occurrenceUpdate step)) (observation (retained charge)) (sourcePoint left) =
      projection (sourceAction (occurrenceUpdate step)) (observation (retained charge)) (sourcePoint right) ↔
        retained charge left = retained charge right := by
  rw [model_fibre, observation_point, observation_point]

end
end SourceAccountedAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
