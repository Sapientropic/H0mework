import H0mework.Realization.Operations.ObservationHistory

/-! The complete future-observation kernel is the largest invisible invariant source submodule. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B)

theorem mem_kernel_iff (value : C) :
    value ∈ LinearMap.ker (sourceMap action observation) ↔
      ∀ stage : Nat, observation ((action ^ stage) value) = 0 := by
  simpa only [LinearMap.mem_ker, map_zero] using
    (source_fibre_iff action observation value 0)

theorem kernel_eq_iInf :
    LinearMap.ker (sourceMap action observation) =
      ⨅ stage : Nat, LinearMap.ker (stageEvaluator action observation stage) := by
  ext value
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, stageEvaluator, LinearMap.comp_apply]
  exact mem_kernel_iff action observation value

theorem kernel_invariant :
    LinearMap.ker (sourceMap action observation) ≤
      (LinearMap.ker (sourceMap action observation)).comap action := by
  intro value invisible
  change sourceMap action observation (action value) = 0
  have square := endomorphism_source action observation value
  exact square.symm.trans ((congrArg (endomorphism action observation) invisible).trans (map_zero _))

theorem kernel_le_observer_kernel :
    LinearMap.ker (sourceMap action observation) ≤ LinearMap.ker observation := by
  intro value invisible
  have first := (mem_kernel_iff action observation value).mp invisible 0
  change observation value = 0
  simpa only [pow_zero, Module.End.one_apply] using first

theorem invariant_submodule_le_kernel (submodule : Submodule R C)
    (invisible : submodule ≤ LinearMap.ker observation)
    (invariant : submodule ≤ submodule.comap action) :
    submodule ≤ LinearMap.ker (sourceMap action observation) := by
  intro value member
  apply (mem_kernel_iff action observation value).mpr
  intro stage
  have remains : (action ^ stage) value ∈ submodule := by
    induction stage with
    | zero => exact member
    | succ stage inductionHypothesis =>
        rw [pow_succ']
        exact invariant inductionHypothesis
  exact invisible remains

theorem kernel_is_largest_invisible_invariant :
    LinearMap.ker (sourceMap action observation) ≤ LinearMap.ker observation ∧
    LinearMap.ker (sourceMap action observation) ≤
      (LinearMap.ker (sourceMap action observation)).comap action ∧
    ∀ submodule : Submodule R C,
      submodule ≤ LinearMap.ker observation → submodule ≤ submodule.comap action →
        submodule ≤ LinearMap.ker (sourceMap action observation) :=
  ⟨kernel_le_observer_kernel action observation, kernel_invariant action observation,
    invariant_submodule_le_kernel action observation⟩

end
end SourceGeneratedActionObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
