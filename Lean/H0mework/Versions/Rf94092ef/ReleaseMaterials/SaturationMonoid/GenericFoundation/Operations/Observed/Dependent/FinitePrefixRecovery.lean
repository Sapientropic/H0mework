import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.PrefixRecovery.Iteration
import H0mework.Realization.ObservationActions.DependentCoimage
import H0mework.Realization.ObservationActions.DependentHilbert

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent

open Filter SourceGeneratedScalarDifferentialResidual
open scoped InnerProductSpace Topology

universe u v

variable {State : Type v} (step : State → State) {C : State → Type u} {B : Type u}
variable [∀ state, NormedAddCommGroup (C state)] [∀ state, InnerProductSpace ℂ (C state)]
variable [∀ state, CompleteSpace (C state)]
variable [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
variable (action : ∀ state, C state →L[ℂ] C (step state))
variable (observe : ∀ state, C state →L[ℂ] B)

local notation "E" => stageEvaluator step action observe
local notation "J" => embedding step action observe
local notation "S" => sourceMap step action observe
local notation "Kernel" => fun state => LinearMap.ker (S state)

local instance observationKernelComplete (state : State) : CompleteSpace (Kernel state) :=
  (kernel_closed step action observe state).isComplete.completeSpace_coe

/-- The finite actual reads land on the existing orthogonal representative of the dependent coimage. -/
theorem finite_prefix_current (state : State) (value : C state) :
    Tendsto (fun n => PrefixRecovery.approximate (E state) (fun j : Fin n => E state j value)) atTop
      (𝓝 (J state (canonicalResidual (S state) value))) := by
  let fixed := (PrefixRecovery.limitAction (E state)).eqLocus (1 : C state →L[ℂ] C state)
  have same : fixed = Kernel state := by
    ext x
    change PrefixRecovery.limitAction (E state) x = (1 : C state →L[ℂ] C state) x ↔ S state x = 0
    rw [one_apply_eq_self, PrefixRecovery.limit_fixed, source_zero_iff]
  let visible := fixedᗮ.starProjection value
  have orthogonal := congrArg (fun U : Submodule ℂ (C state) => Uᗮ) same
  have member : visible ∈ (Kernel state)ᗮ := orthogonal ▸ fixedᗮ.starProjection_apply_mem value
  have difference : value-visible ∈ ((Kernel state)ᗮ)ᗮ :=
    (congrArg (fun U : Submodule ℂ (C state) => Uᗮ) orthogonal) ▸
      Submodule.sub_starProjection_mem_orthogonal (K := fixedᗮ) value
  have unique := Submodule.eq_starProjection_of_mem_orthogonal member difference
  have limit := PrefixRecovery.recover (E state) value
  change Tendsto (fun n => PrefixRecovery.approximate (E state) (fun j : Fin n => E state j value)) atTop
    (𝓝 visible) at limit
  rw [embedding_source, unique]
  exact limit

/-- Drop the first observed stage and consume the original typed coimage successor. -/
theorem finite_prefix_next (state : State) (value : C state) :
    Tendsto (fun n => PrefixRecovery.approximate (E (step state))
      (fun j : Fin n => E state (j.val+1) value)) atTop
      (𝓝 (J (step state) (nextCoimage step action observe state (canonicalResidual (S state) value)))) := by
  rw [next_coimage_source]
  exact finite_prefix_current step action observe (step state) (action state value)

omit [CompleteSpace B] in
private theorem representative_initial_read (state : State) (value : C state) :
    observe state (J state (canonicalResidual (S state) value)) = observe state value := by
  rw [embedding_source]
  have erased := (source_zero_iff step action observe state _).mp
    (LinearMap.mem_ker.mp ((Kernel state).starProjection_apply_mem value)) 0
  change observe state ((Kernel state).starProjection value) = 0 at erased
  have split := congrArg (observe state)
    ((Kernel state).starProjection_add_starProjection_orthogonal value)
  rwa [map_add, erased, zero_add] at split

/-- The next independent read consumes the finite approximation to its original source. -/
theorem finite_prefix_next_read (state : State) (value : C state) :
    Tendsto (fun n => observe (step state) (PrefixRecovery.approximate (E (step state))
      (fun j : Fin n => E state (j.val+1) value))) atTop
      (𝓝 (observe (step state) (action state value))) := by
  have next := finite_prefix_next step action observe state value
  rw [next_coimage_source] at next
  have read := ((observe (step state)).continuous.tendsto _).comp next
  rw [representative_initial_read] at read
  exact read

end SourceGeneratedActionObservationHistory.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
