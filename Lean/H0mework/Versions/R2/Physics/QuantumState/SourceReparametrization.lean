import H0mework.Versions.R2.Physics.QuantumState.SourceFrame

/-! Scalar quantum readouts at the same physical point are natural under
point reparametrization and a jointly moved ambient frame. This needs only
a point equivalence, so it also applies to any diffeomorphism; it makes no
claim about the differential equations of an arbitrary pulled-back field. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Source.Reparametrization

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction Stage9C.Material.SpinPair
open SaturationMonoid.PhysicsCore.Stage9DEF.Source.Frame

noncomputable section

def matter (reparam : BasePoint ≃ BasePoint) (localFrame : BasePoint → Action)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  localFrame point (actual.matter (reparam point))

def independentDual (reparam : BasePoint ≃ BasePoint) (localFrame : BasePoint → Action)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (actual.conjugateMatter (reparam point)).comp (localFrame point).symm.toLinearMap

def preparation (reparam : BasePoint ≃ BasePoint) (localFrame : BasePoint → Action)
    (point : BasePoint) : Index → ℂ :=
  prepare (localFrame point) (matter reparam localFrame point)

def effect (reparam : BasePoint ≃ BasePoint) (localFrame : BasePoint → Action)
    (reference : BasePoint) : State.Effect :=
  Frame.effect (localFrame reference) (reparam reference)

def weight (reparam : BasePoint ≃ BasePoint) (localFrame : BasePoint → Action)
    (point reference : BasePoint) : ℝ :=
  (State.vectorEvaluation (preparation reparam localFrame point)
    (effect reparam localFrame reference).matrix).re

theorem matter_reconstruction (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (point : BasePoint) :
    movedEmbedding (localFrame point) (amplitude (reparam point)) =
      matter reparam localFrame point := rfl

theorem preparation_eq (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (point : BasePoint) :
    preparation reparam localFrame point = vector (reparam point) :=
  transformed_actual_prepare (localFrame point) (reparam point)

theorem effect_eq (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (reference : BasePoint) :
    effect reparam localFrame reference = State.sourceEffect (reparam reference) :=
  effect_eq_source (localFrame reference) (reparam reference)

theorem weight_natural (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (point reference : BasePoint) :
    weight reparam localFrame point reference =
      State.effectWeight (reparam point) (State.sourceEffect (reparam reference)) := by
  rw [weight, preparation_eq, effect_eq]
  rfl

theorem same_physical_points_weight (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (point reference : BasePoint) :
    weight reparam localFrame (reparam.symm point) (reparam.symm reference) =
      State.effectWeight point (State.sourceEffect reference) := by
  rw [weight_natural, reparam.apply_symm_apply, reparam.apply_symm_apply]

theorem independentDual_response (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    independentDual reparam localFrame point
        (observableAction (localFrame point) observable (matter reparam localFrame point)) =
      actual.conjugateMatter (reparam point)
        (observableAction (LinearEquiv.refl ℂ _) observable (actual.matter (reparam point))) :=
  Frame.independentDual_response (localFrame point) (reparam point) observable

theorem same_physical_point_independentDual (reparam : BasePoint ≃ BasePoint)
    (localFrame : BasePoint → Action) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    independentDual reparam localFrame (reparam.symm point)
        (observableAction (localFrame (reparam.symm point)) observable
          (matter reparam localFrame (reparam.symm point))) =
      actual.conjugateMatter point
        (observableAction (LinearEquiv.refl ℂ _) observable (actual.matter point)) := by
  rw [independentDual_response, reparam.apply_symm_apply]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Source.Reparametrization
