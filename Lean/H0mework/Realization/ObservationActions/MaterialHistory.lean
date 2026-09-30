import H0mework.Realization.ObservationActions.MaterialCharpoly

/-! Actual material updates make the generated finite recurrence act on the same source history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.MaterialRecurrence

noncomputable section

universe r u

variable {R : Type r} [CommRing R] [Nontrivial R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
variable [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B) (material : Nat → C)

def windowAt (first : Nat) : Fin (bound action + 1) → B :=
  fun index => observation (material (first + index.val))

omit [Nontrivial R] in
theorem windows_equal_of_constant
    (constant : ∀ stage : Nat, observation (material stage) = observation (material 0)) (left right : Nat) :
    windowAt action observation material left = windowAt action observation material right := by
  funext index
  exact (constant (left + index.val)).trans (constant (right + index.val)).symm

variable (generated : ∀ stage : Nat, material (stage + 1) = action (material stage))

include generated

omit [Nontrivial R] [Module.Free R C] [Module.Finite R C] in
theorem material_iterate (first steps : Nat) :
    (action ^ steps) (material first) = material (first + steps) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
      rw [pow_succ']
      change action ((action ^ steps) (material first)) = _
      rw [previous, ← generated, Nat.add_assoc]

omit [Nontrivial R] in
theorem window_from_source (first : Nat) :
    windowAt action observation material first = prefixEvaluator action observation (bound action) (material first) := by
  funext index
  change observation (material (first + index.val)) = observation ((action ^ index.val) (material first))
  rw [material_iterate action material generated]

theorem window_next (first : Nat) :
    FiniteRecurrence.advance (bound action) (coefficients action) (windowAt action observation material first) =
      windowAt action observation material (first + 1) := by
  rw [window_from_source action observation material generated, window_from_source action observation material generated]
  have actual := LinearMap.congr_fun (FiniteRecurrence.advance_source action observation (bound action)
    (coefficients action) (observation_law action observation)) (material first)
  change FiniteRecurrence.advance (bound action) (coefficients action)
    (prefixEvaluator action observation (bound action) (material first)) =
      prefixEvaluator action observation (bound action) (action (material first)) at actual
  exact actual.trans (congrArg (prefixEvaluator action observation (bound action)) (generated first).symm)

theorem forecast_material (first : Nat) :
    (∑ index : Fin (bound action + 1), coefficients action index • windowAt action observation material first index) =
      observation (material (first + bound action + 1)) := by
  have actual := congrFun (window_next action observation material generated first) (Fin.last (bound action))
  rw [FiniteRecurrence.advance_last] at actual
  change (∑ index : Fin (bound action + 1), coefficients action index • windowAt action observation material first index) =
    observation (material (first + 1 + bound action)) at actual
  exact actual.trans (congrArg (fun stage => observation (material stage)) (by omega : first + 1 + bound action = first + bound action + 1))

theorem window_fibre_iff_future (left right : Nat) :
    windowAt action observation material left = windowAt action observation material right ↔
      ∀ future : Nat, observation (material (left + future)) = observation (material (right + future)) := by
  rw [window_from_source action observation material generated, window_from_source action observation material generated,
    FiniteRecurrence.prefix_fibre_iff_model action observation (bound action) (coefficients action) (observation_law action observation),
    model_fibre_iff]
  simp only [material_iterate action material generated]

end
end SourceGeneratedActionObservationHistory.MaterialRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
