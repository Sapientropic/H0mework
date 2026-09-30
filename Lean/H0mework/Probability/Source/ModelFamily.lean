import H0mework.Probability.Source.Field
import H0mework.Realization.Operations.ObservationModel

/-! One fixed dependent observation inventory consumes the existing autonomous source coimage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FamilyModel

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {State I : Type u} {B : I → Type u} [∀ index, AddCommGroup (B index)]
variable (step : State → State) (read : (index : I) → State → B index)

def familyRead (state : State) : (index : I) → B index := fun index => read index state

theorem observation_family : observation (familyRead read) = LinearMap.pi (fun index => observation (read index)) := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  funext index
  change observation (familyRead read) (sourcePoint state) index = observation (read index) (sourcePoint state)
  rw [observation_point, observation_point]
  rfl

theorem kernel_family :
    LinearMap.ker (sourceMap (sourceAction step) (observation (familyRead read))) =
      ⨅ index, LinearMap.ker (sourceMap (sourceAction step) (observation (read index))) := by
  ext word
  simp only [Submodule.mem_iInf, mem_kernel_iff, observation_family, LinearMap.pi_apply, funext_iff, Pi.zero_apply]
  exact forall_comm

def componentMap (index : I) : Model (sourceAction step) (observation (familyRead read)) →ₗ[ℤ]
    Model (sourceAction step) (observation (read index)) :=
  Submodule.factor ((kernel_family step read).le.trans (iInf_le _ index))

theorem componentMap_projection (index : I) (word : Carrier State) :
    componentMap step read index (projection (sourceAction step) (observation (familyRead read)) word) =
      projection (sourceAction step) (observation (read index)) word := rfl

theorem componentMap_surjective (index : I) : Function.Surjective (componentMap step read index) := by
  have source := (actionRow (sourceAction step) (observation (read index))).restriction_surjective
  change Function.Surjective (projection (sourceAction step) (observation (read index))) at source
  apply Function.Surjective.of_comp (g := projection (sourceAction step) (observation (familyRead read)))
  simpa only [Function.comp_def, componentMap_projection] using source

theorem componentMap_action (index : I) (value : Model (sourceAction step) (observation (familyRead read))) :
    componentMap step read index (modelAction (sourceAction step) (observation (familyRead read)) value) =
      modelAction (sourceAction step) (observation (read index)) (componentMap step read index value) := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change componentMap step read index (modelAction (sourceAction step) (observation (familyRead read))
    (projection (sourceAction step) (observation (familyRead read)) word)) = _
  rw [modelAction_source, componentMap_projection]
  change _ = modelAction (sourceAction step) (observation (read index))
    (componentMap step read index (projection (sourceAction step) (observation (familyRead read)) word))
  rw [componentMap_projection, modelAction_source]

theorem componentMap_readout (index : I) (value : Model (sourceAction step) (observation (familyRead read))) :
    modelReadout (sourceAction step) (observation (read index)) (componentMap step read index value) =
      modelReadout (sourceAction step) (observation (familyRead read)) value index := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change modelReadout (sourceAction step) (observation (read index))
      (componentMap step read index (projection (sourceAction step) (observation (familyRead read)) word)) =
    modelReadout (sourceAction step) (observation (familyRead read))
      (projection (sourceAction step) (observation (familyRead read)) word) index
  rw [componentMap_projection, modelReadout_projection, modelReadout_projection, observation_family]
  rfl

theorem family_fibre_iff (left right : Carrier State) :
    projection (sourceAction step) (observation (familyRead read)) left =
        projection (sourceAction step) (observation (familyRead read)) right ↔
      ∀ index, projection (sourceAction step) (observation (read index)) left =
        projection (sourceAction step) (observation (read index)) right := by
  simp only [model_fibre_iff, observation_family, LinearMap.pi_apply, funext_iff]
  exact forall_comm

theorem model_ext_iff (left right : Model (sourceAction step) (observation (familyRead read))) :
    left = right ↔ ∀ index, componentMap step read index left = componentMap step read index right := by
  refine Submodule.Quotient.induction_on _ left fun leftWord => ?_
  refine Submodule.Quotient.induction_on _ right fun rightWord => ?_
  change projection (sourceAction step) (observation (familyRead read)) leftWord =
    projection (sourceAction step) (observation (familyRead read)) rightWord ↔ _
  exact family_fibre_iff step read leftWord rightWord

theorem sourcePoint_read (state : State) :
    modelReadout (sourceAction step) (observation (familyRead read))
        (projection (sourceAction step) (observation (familyRead read)) (sourcePoint state)) = familyRead read state :=
  (modelReadout_projection _ _ _).trans (observation_point (familyRead read) state)

theorem sourcePoint_action (state : State) :
    modelAction (sourceAction step) (observation (familyRead read))
        (projection (sourceAction step) (observation (familyRead read)) (sourcePoint state)) =
      projection (sourceAction step) (observation (familyRead read)) (sourcePoint (step state)) :=
  (modelAction_source _ _ _).trans
    (congrArg (projection (sourceAction step) (observation (familyRead read))) (sourceAction_point step state))

end
end SourceOwnedObservationHistory.FamilyModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
