import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Registered
set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor
open SourceOperationEffects SourceOperationExecution
open Registered
noncomputable section
abbrev emitted (depth : Nat) : Occurrence depth := (old depth).emitted (origin depth)

abbrev Syntax (depth : Nat) := Programme (Occurrence := Occurrence depth) (index depth) (active depth)
def wrap (depth : Nat) : Nat → Syntax depth → Syntax depth
  | 0, expression => expression
  | count + 1, expression => .linear (action (index depth) (active depth)) (wrap depth count expression)
private theorem pulses_not_const (depth count : Nat) (value : Point depth →₀ ℤ) :
    pulses (index depth) (active depth) count ≠ .const value := by
  cases count <;> simp [pulses]
private theorem linear_step_cases (depth : Nat)
    (environment : Env (Registered.Value depth) Var)
    {value target : Syntax depth}
    (actual : Step environment (.linear (action (index depth) (active depth)) value) target) :
    (∃ constant : Point depth →₀ ℤ, value = .const constant ∧
      target = .const (action (index depth) (active depth) constant)) ∨
    (∃ result : Syntax depth, target = .linear (action (index depth) (active depth)) result ∧
      Nonempty (Step environment value result)) := by
  cases actual with
  | linearConst operation value => exact .inl ⟨value, rfl, rfl⟩
  | linear operation actual => exact .inr ⟨_, rfl, ⟨actual⟩⟩
private theorem pulses_step_target (depth count : Nat)
    (environment : Env (Registered.Value depth) Var)
    {target : Syntax depth}
    (actual : Step environment (pulses (index depth) (active depth) count) target) :
    target = wrap depth count (.const (environment Unit.unit Unit.unit)) := by
  induction count generalizing target with
  | zero => cases actual; rfl
  | succ count previous =>
      rcases linear_step_cases depth environment actual with
        ⟨constant, same, _⟩ | ⟨result, same, ⟨step⟩⟩
      · exact False.elim (pulses_not_const depth count constant same)
      · rw [same, previous step]
        rfl

private theorem wrap_step_target (depth count : Nat)
    (environment : Env (Registered.Value depth) Var) (value : Point depth →₀ ℤ)
    {target : Syntax depth}
    (actual : Step environment (wrap depth (count + 1) (.const value)) target) :
    target = wrap depth count (.const (action (index depth) (active depth) value)) := by
  induction count generalizing target with
  | zero =>
      rcases linear_step_cases depth environment actual with
        ⟨constant, same, result⟩ | ⟨result, same, ⟨step⟩⟩
      · have same' : (Expr.const value : Syntax depth) = .const constant := by
          simpa only [wrap] using same
        have values : value = constant := by cases same'; rfl
        subst constant
        exact result
      · exact False.elim (const_no_step environment value result ⟨step⟩)
  | succ count previous =>
      rcases linear_step_cases depth environment actual with
        ⟨constant, same, _⟩ | ⟨result, same, ⟨step⟩⟩
      · simp only [wrap] at same
        contradiction
      · rw [same, previous step]
        rfl

namespace Engine
export RootGeneratedDebtActivationJointSource.OwnerFree
  (Current Runtime initial action targetOf nextState law runtimeCurrent mathFace initialRuntime tick_math)
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion
  (state runtime next_state initial_state history_accounting)
end Engine

abbrev mathRuntime (depth count : Nat) :=
  Engine.runtime (old depth) (origin depth) (reader depth) count

abbrev mathState (depth count : Nat) :=
  Engine.state (old depth) (origin depth) (reader depth) count

/-- The math face carries the current syntax and paid past, unlike the fixed raw seed. -/
theorem mathState_next (depth count : Nat) : mathState depth (count + 1) =
    Engine.nextState (old depth) (origin depth) (reader depth) (mathState depth count) :=
  Engine.next_state (old depth) (origin depth) (reader depth) count

theorem mathState_initial (depth : Nat) : mathState depth 0 =
    Engine.initial (old depth) (origin depth) (reader depth) := rfl

theorem mathFace_current (depth count : Nat) :
    (Engine.mathFace (old depth) (origin depth) (reader depth) (mathRuntime depth count)).rootRead =
      mathState depth count := rfl

private theorem next_syntax (depth : Nat)
    (state : Engine.Current (old depth) (origin depth) (reader depth))
    (target : Syntax depth) (progress : 0 < SourceOperationExecution.remaining state.1)
    (unique : ∀ {result : Syntax depth},
      Step (OF.raw (old depth) (origin depth) (reader depth)).environment state.1 result →
        result = target) :
    (Engine.nextState (old depth) (origin depth) (reader depth) state).1 = target := by
  unfold Engine.nextState Engine.targetOf
  cases selected : Engine.action (old depth) (origin depth) (reader depth) state with
  | inl settled =>
      have zero := (Engine.law (old depth) (origin depth) (reader depth)).settlement_budget_zero settled
      change SourceOperationExecution.remaining state.1 = 0 at zero
      omega
  | inr paid =>
      rcases paid with ⟨result, advance⟩
      cases advance with
      | paid actual => exact unique actual

private theorem wrap_remaining (depth count : Nat) (value : Point depth →₀ ℤ) :
    SourceOperationExecution.remaining (wrap depth count (.const value)) = count := by
  induction count with
  | zero => rfl
  | succ count previous => simp only [wrap, SourceOperationExecution.remaining, previous]

private theorem action_single (depth : Nat) (point : Point depth) :
    action (index depth) (active depth) (Finsupp.single point (1 : ℤ)) =
      Finsupp.single (nextPoint (index depth) (active depth) point) 1 := by
  simp only [action, LinearMap.toAddMonoidHom_coe, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- After the original bind, each canonical tick consumes one literal actor
pulse and retains all later actions around the full chronological cursor. -/
theorem current_syntax (depth count : Nat)
    (within : count ≤ sourceFuel (source depth (emitted depth))) :
    (mathState depth (count + 1)).1 =
      wrap depth (sourceFuel (source depth (emitted depth)) - count)
        (.const (Finsupp.single
          (runPoint (index depth) (active depth) count
            (initialPoint (index depth) (active depth) (emitted depth))) 1)) := by
  induction count with
  | zero =>
      rw [mathState_next, mathState_initial]
      apply next_syntax
      · change 0 < SourceOperationExecution.remaining (pulses (index depth) (active depth)
          (sourceFuel (source depth (emitted depth))))
        rw [pulses_budget]
        omega
      · intro result actual
        exact pulses_step_target depth _ _ actual
  | succ count previous =>
      have previousWithin : count ≤ sourceFuel (source depth (emitted depth)) := by omega
      have before := previous previousWithin
      rw [mathState_next]
      apply next_syntax
      · rw [before, wrap_remaining]
        omega
      · intro result actual
        rw [before] at actual
        have layers : sourceFuel (source depth (emitted depth)) - count =
            (sourceFuel (source depth (emitted depth)) - (count + 1)) + 1 := by omega
        rw [layers] at actual
        rw [wrap_step_target depth _ _ _ actual, action_single, runPoint_succ_right]

/-- Cursor recovery reads the actual syntax's constant support. Its singleton
source law makes this read independent of finite-set enumeration order. -/
def readCursor (depth : Nat) {sort : Unit} : Expr (Registered.Value depth) Var sort → Option (Point depth)
  | .const value => value.support.toList.head?
  | .linear _ expression => readCursor depth expression
  | .var _ => none
  | .add _ _ => none
  | .bilinear _ _ _ => none

private theorem readCursor_wrapped (depth count : Nat) (point : Point depth) :
    readCursor depth (wrap depth count (.const (Finsupp.single point (1 : ℤ)))) = some point := by
  induction count with
  | zero => simp [wrap, readCursor]
  | succ count previous => simpa only [wrap, readCursor] using previous

/-- The cursor is a projection of the current paid mathematical occurrence. -/
theorem current_cursor (depth count : Nat)
    (within : count ≤ sourceFuel (source depth (emitted depth))) :
    readCursor depth (mathState depth (count + 1)).1 =
      some (runPoint (index depth) (active depth) count
        (initialPoint (index depth) (active depth) (emitted depth))) := by
  rw [current_syntax depth count within, readCursor_wrapped]

/-- A literal canonical next performs the original source-selected actor update. -/
theorem literal_next_cursor (depth count : Nat)
    (within : count < sourceFuel (source depth (emitted depth))) :
    readCursor depth
        (Engine.runtimeCurrent (old depth) (origin depth) (reader depth)
          (mathRuntime depth (count + 1)).tick.next).1 =
      (readCursor depth (mathState depth (count + 1)).1).map
        (nextPoint (index depth) (active depth)) := by
  change readCursor depth (mathState depth ((count + 1) + 1)).1 = _
  rw [current_cursor depth (count + 1) (by omega), current_cursor depth count (by omega)]
  rw [runPoint_succ_right]
  rfl

/-- The recovered point retains the original occurrence and full ordered prefix. -/
theorem current_cursor_fibre (depth count : Nat)
    (within : count ≤ sourceFuel (source depth (emitted depth))) :
    readCursor depth (mathState depth (count + 1)).1 =
      some (⟨emitted depth,
        run count (initial (source depth (emitted depth)))⟩ : Point depth) := by
  rw [current_cursor depth count within, runPoint_fibre]
  rfl

theorem paid_history_length (depth count : Nat)
    (within : count ≤ sourceFuel (source depth (emitted depth))) :
    (mathState depth (count + 1)).2.length = count + 1 := by
  have accounting := Engine.history_accounting (old depth) (origin depth) (reader depth) (count + 1)
  have cursorBudget : SourceOperationExecution.remaining (mathState depth (count + 1)).1 =
      sourceFuel (source depth (emitted depth)) - count := by
    rw [current_syntax depth count within, wrap_remaining]
  rw [cursorBudget] at accounting
  change (mathState depth (count + 1)).2.length +
    (sourceFuel (source depth (emitted depth)) - count) =
      SourceOperationExecution.remaining (sourceProgramme (index depth) (active depth) (emitted depth)) at accounting
  rw [sourceProgramme_budget] at accounting
  change (mathState depth (count + 1)).2.length +
    (sourceFuel (sourceAt (index depth) (active depth) (emitted depth)) - count) =
      sourceFuel (sourceAt (index depth) (active depth) (emitted depth)) + 1 at accounting
  have bound : count ≤ sourceFuel (sourceAt (index depth) (active depth) (emitted depth)) := within
  omega
end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
