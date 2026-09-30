import H0mework.Realization.ObservationActions.DependentHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u v

variable {𝕜 : Type r} [NontriviallyNormedField 𝕜]
variable {State : Type v} (step : State → State) {C : State → Type u} {B : Type u}
variable [∀ state, NormedAddCommGroup (C state)] [∀ state, NormedSpace 𝕜 (C state)]
variable [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable (action : ∀ state, C state →L[𝕜] C (step state))
variable (observation : ∀ state, C state →L[𝕜] B)

theorem source_zero_iff (state : State) (value : C state) :
    sourceMap step action observation state value = 0 ↔
      ∀ stage, stageEvaluator step action observation state stage value = 0 := by
  constructor
  · intro invisible stage
    have prefixValue := (data step action observation state).evaluator_eq_zero_of_completionMap_eq_zero
      (compatible step action observation state) value invisible stage
    exact congrFun prefixValue (Fin.last stage)
  · intro invisible
    apply Limits.Concrete.limit_ext
      ((data step action observation state).quotientTower (compatible step action observation state))
    intro stage
    have quotientZero : (data step action observation state).quotientMap stage.unop value = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      show prefixEvaluator step action observation state stage.unop value = 0
      funext index
      exact invisible index.val
    have source := ConcreteCategory.congr_hom
      ((data step action observation state).completionMap_restriction
        (compatible step action observation state) stage.unop) value
    exact source.trans (quotientZero.trans (map_zero _).symm)

theorem source_fibre_iff (state : State) (left right : C state) :
    sourceMap step action observation state left = sourceMap step action observation state right ↔
      ∀ stage, stageEvaluator step action observation state stage left =
        stageEvaluator step action observation state stage right := by
  rw [← sub_eq_zero, ← map_sub, source_zero_iff]
  simp only [map_sub, sub_eq_zero]

theorem kernel_closed (state : State) :
    IsClosed (LinearMap.ker (sourceMap step action observation state) : Set (C state)) := by
  have same : (LinearMap.ker (sourceMap step action observation state) : Set (C state)) =
      ⋂ stage, ((stageEvaluator step action observation state stage).toLinearMap.ker : Set (C state)) := by
    ext value
    simp only [LinearMap.mem_ker, Set.mem_iInter, SetLike.mem_coe]
    exact source_zero_iff step action observation state value
  rw [same]
  exact isClosed_iInter fun stage => (stageEvaluator step action observation state stage).isClosed_ker

end
end SourceGeneratedActionObservationHistory.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
