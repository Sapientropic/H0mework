import H0mework.Probability.Source.ModelFamily

/-! Reindexing one fixed source inventory generates a canonical quotient restriction and its action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FamilyModel

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {State I J : Type u} {B : I → Type u} [∀ index, AddCommGroup (B index)]
variable (step : State → State) (read : (index : I) → State → B index) (reindex : J → I)

theorem kernel_reindex :
    LinearMap.ker (sourceMap (sourceAction step) (observation (familyRead read))) ≤
      LinearMap.ker (sourceMap (sourceAction step) (observation (familyRead (fun index => read (reindex index))))) := by
  rw [kernel_family, kernel_family]
  exact le_iInf fun index => iInf_le _ (reindex index)

def restriction : Model (sourceAction step) (observation (familyRead read)) →ₗ[ℤ]
    Model (sourceAction step) (observation (familyRead (fun index => read (reindex index)))) :=
  Submodule.factor (kernel_reindex step read reindex)

theorem restriction_projection (word : Carrier State) :
    restriction step read reindex (projection (sourceAction step) (observation (familyRead read)) word) =
      projection (sourceAction step) (observation (familyRead (fun index => read (reindex index)))) word := rfl

theorem restriction_surjective : Function.Surjective (restriction step read reindex) := by
  have source := (actionRow (sourceAction step)
    (observation (familyRead (fun index => read (reindex index))))).restriction_surjective
  change Function.Surjective
    (projection (sourceAction step) (observation (familyRead (fun index => read (reindex index))))) at source
  apply Function.Surjective.of_comp (g := projection (sourceAction step) (observation (familyRead read)))
  simpa only [Function.comp_def, restriction_projection] using source

theorem restriction_action (value : Model (sourceAction step) (observation (familyRead read))) :
    restriction step read reindex (modelAction (sourceAction step) (observation (familyRead read)) value) =
      modelAction (sourceAction step) (observation (familyRead (fun index => read (reindex index))))
        (restriction step read reindex value) := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change restriction step read reindex (modelAction (sourceAction step) (observation (familyRead read))
    (projection (sourceAction step) (observation (familyRead read)) word)) = _
  rw [modelAction_source, restriction_projection]
  change _ = modelAction (sourceAction step) (observation (familyRead (fun index => read (reindex index))))
    (restriction step read reindex (projection (sourceAction step) (observation (familyRead read)) word))
  rw [restriction_projection, modelAction_source]

theorem restriction_readout (value : Model (sourceAction step) (observation (familyRead read))) :
    modelReadout (sourceAction step) (observation (familyRead (fun index => read (reindex index))))
        (restriction step read reindex value) =
      fun index => modelReadout (sourceAction step) (observation (familyRead read)) value (reindex index) := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change modelReadout (sourceAction step) (observation (familyRead (fun index => read (reindex index))))
      (restriction step read reindex (projection (sourceAction step) (observation (familyRead read)) word)) =
    fun index => modelReadout (sourceAction step) (observation (familyRead read))
      (projection (sourceAction step) (observation (familyRead read)) word) (reindex index)
  rw [restriction_projection, modelReadout_projection, modelReadout_projection,
    observation_family, observation_family]
  rfl

theorem restriction_component (index : J) (value : Model (sourceAction step) (observation (familyRead read))) :
    componentMap step (fun item => read (reindex item)) index (restriction step read reindex value) =
      componentMap step read (reindex index) value := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change componentMap step (fun item => read (reindex item)) index
    (restriction step read reindex (projection (sourceAction step) (observation (familyRead read)) word)) = _
  rw [restriction_projection, componentMap_projection]
  rfl

end
end SourceOwnedObservationHistory.FamilyModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
