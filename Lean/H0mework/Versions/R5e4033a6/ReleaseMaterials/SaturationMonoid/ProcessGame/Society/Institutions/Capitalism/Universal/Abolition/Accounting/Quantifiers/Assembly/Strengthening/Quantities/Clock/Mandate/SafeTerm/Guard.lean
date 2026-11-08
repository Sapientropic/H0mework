import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm

open Source.Program PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Current" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Action" => Request Party Good Port (State Party Technology) Instrument
local notation "Scope" => Mandate.Scope (Party := Party) (Good := Good) (Port := Port)

inductive Guard where
  | any
  | atLeast (clock : ℚ)
  | below (clock : ℚ)
  deriving DecidableEq

def Guard.Holds (guard : Guard) (cutoff : ℚ) : Prop :=
  match guard with
  | .any => True
  | .atLeast clock => clock ≤ cutoff
  | .below clock => cutoff < clock

instance (guard : Guard) (cutoff : ℚ) : Decidable (guard.Holds cutoff) := by
  cases guard <;> unfold Guard.Holds <;> infer_instance

/-- Evaluate a deadline sensitivity query with the same service, authority,
actors and cost. The only operation that installs a scope is the native handoff. -/
abbrev withCutoff (scope : Scope) (cutoff : ℚ) : Scope :=
  {scope with task := {scope.task with deadline := cutoff}}

def Quiet (current : Current) : Prop :=
  current.technology.holder = none ∧ current.technology.offered = none

instance (current : Current) : Decidable (Quiet current) := by
  unfold Quiet
  infer_instance

def commandGuard (scope : Scope) (current : Current) : Command Party → Guard
  | .propose _ | .accept | .renew => .atLeast current.clock
  | .exit | .revoke => .any
  | .review =>
    if Quiet current then .any
    else if scope.task.deadline < current.clock then .below current.clock
    else .atLeast current.clock

def ordinaryGuard (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope) (current : Current) (action : Action) : Guard :=
  if scope.service ∈ base.requiredPorts (eraseCurrent current) (eraseRequest action) ∨
      TaskUse scope action then .atLeast current.clock else .any

def guard (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope) (current : Current) (action : Action) : Guard :=
  match action.operation with
  | .revise _ target => match target.last with
    | none => .any
    | some command => commandGuard scope current command
  | _ => ordinaryGuard base scope current action

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
    [DecidableEq Instrument] in
private theorem review_changes_active_state
    (scope : Scope) (current : Current) (first last : ℚ)
    (active : ¬ Quiet current) (expired : first < current.clock)
    (still : ¬ last < current.clock) :
    advance (withCutoff scope first) current .review ≠
      advance (withCutoff scope last) current .review := by
  intro same
  apply active
  change advance (withCutoff scope first) current .review =
    advance (withCutoff scope last) current .review at same
  simp only [advance] at same
  rw [if_pos expired, if_neg still] at same
  exact ⟨(congrArg State.holder same).symm, (congrArg State.offered same).symm⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem original_command_guard_exact (scope : Scope) (current : Current)
    (actor : Party) (command : Command Party) (cutoff : ℚ)
    (admitted : CanRun scope current actor command) :
    (advance scope current command = advance (withCutoff scope cutoff) current command ∧
      CanRun (withCutoff scope cutoff) current actor command) ↔
      (commandGuard scope current command).Holds cutoff := by
  cases command with
  | propose candidate => exact ⟨fun fits => fits.2.2, fun fits => ⟨rfl, admitted.1, fits⟩⟩
  | accept => exact ⟨fun fits => fits.2.2, fun fits => ⟨rfl, admitted.1, fits⟩⟩
  | renew => exact ⟨fun fits => fits.2.2.2, fun fits => ⟨rfl, admitted.1, admitted.2.1, fits⟩⟩
  | exit => exact ⟨fun _ => trivial, fun _ => ⟨rfl, admitted⟩⟩
  | revoke => exact ⟨fun _ => trivial, fun _ => ⟨rfl, admitted⟩⟩
  | review =>
    simp only [CanRun] at admitted
    change (_ ∧ actor ∈ Delegation.members scope.task) ↔ _
    rw [and_iff_left admitted]
    by_cases quiet : Quiet current
    · rw [commandGuard, if_pos quiet]
      simp only [Guard.Holds, iff_true]
      simp only [advance]
      by_cases old : scope.task.deadline < current.clock <;>
        by_cases new : cutoff < current.clock <;>
        simp [old, new, quiet.1, quiet.2]
    · rw [commandGuard, if_neg quiet]
      by_cases expired : scope.task.deadline < current.clock
      · rw [if_pos expired]
        change _ ↔ cutoff < current.clock
        constructor
        · intro same
          by_contra late
          exact (review_changes_active_state scope current scope.task.deadline cutoff quiet expired late) same
        · intro early
          simp only [advance]
          rw [if_pos expired, if_pos early]
      · rw [if_neg expired]
        change _ ↔ current.clock ≤ cutoff
        constructor
        · intro same
          by_contra early
          exact (review_changes_active_state scope current cutoff scope.task.deadline quiet
            (lt_of_not_ge early) expired) same.symm
        · intro late
          simp only [advance]
          rw [if_neg expired, if_neg (not_lt_of_ge late)]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem original_ordinary_guard_exact (scope : Scope) (current : Current)
    (actor : Party) (baseAdmits : Bool) (guarded : Prop) (cutoff : ℚ)
    (admitted : baseAdmits = true ∧ (guarded →
      current.technology.holder = some actor ∧ scope.task.earliest ≤ current.clock ∧
        current.clock ≤ scope.task.deadline)) :
    (baseAdmits = true ∧ (guarded →
      current.technology.holder = some actor ∧ scope.task.earliest ≤ current.clock ∧
        current.clock ≤ cutoff)) ↔ (guarded → current.clock ≤ cutoff) := by
  exact ⟨fun fits needed => (fits.2 needed).2.2, fun fits =>
    ⟨admitted.1, fun needed => ⟨(admitted.2 needed).1, (admitted.2 needed).2.1, fits needed⟩⟩⟩

omit [DecidableEq Good] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem ordinary_holds_iff (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope) (current : Current) (action : Action) (cutoff : ℚ) :
    (ordinaryGuard base scope current action).Holds cutoff ↔
      ((scope.service ∈ base.requiredPorts (eraseCurrent current) (eraseRequest action) ∨
        TaskUse scope action) → current.clock ≤ cutoff) := by
  unfold ordinaryGuard
  split <;> simp_all only [Guard.Holds, true_implies, false_implies]

omit [DecidableEq Good] [DecidableEq Instrument] in
private theorem original_policy_guard_exact (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope) (current : Current) (action : Action) (cutoff : ℚ)
    (admitted : (law base scope).operationAllowed current action = true) :
    (law base (withCutoff scope cutoff)).operationAllowed current action = true ↔
      (guard base scope current action).Holds cutoff := by
  cases operation : action.operation
  case revise operator target =>
    cases mark : target.last with
    | none =>
      simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark, Bool.false_eq_true] at admitted
    | some command =>
      simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark, decide_eq_true_eq] at admitted
      have targetExact := admitted.2.2.2.2.1
      have canRun := admitted.2.2.2.2.2
      simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark,
        guard, withCutoff]
      change decide (operator = action.signer ∧ action.consents = [] ∧ action.purpose = scope.challenge ∧
        action.gates = [scope.challenge] ∧ target = advance (withCutoff scope cutoff) current command ∧
        CanRun (withCutoff scope cutoff) current action.signer command) = true ↔ _
      rw [decide_eq_true_eq]
      rw [and_iff_right admitted.1, and_iff_right admitted.2.1,
        and_iff_right admitted.2.2.1, and_iff_right admitted.2.2.2.1, targetExact]
      exact original_command_guard_exact scope current action.signer command cutoff canRun
  all_goals
    simp only [guard, operation]
    rw [ordinary_holds_iff]
    simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, Bool.and_eq_true, decide_eq_true_eq]
      at admitted ⊢
    exact original_ordinary_guard_exact scope current action.signer _ _ cutoff admitted

omit [DecidableEq Instrument] in
/-- Affordability, claims, and standing remain literal. For a paid item
the deadline readout is exactly the change that can invalidate that item. -/
theorem original_valid_iff_guard (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope) (current : Current) (action : Action) (cutoff : ℚ)
    (paid : (law base scope).Valid current action) :
    (law base (withCutoff scope cutoff)).Valid current action ↔
      (guard base scope current action).Holds cutoff :=
  ⟨fun valid => (original_policy_guard_exact base scope current action cutoff paid.1.2).mp valid.1.2,
   fun fits => ⟨⟨paid.1.1, (original_policy_guard_exact base scope current action cutoff paid.1.2).mpr fits⟩,
      paid.2⟩⟩

theorem original_paid_step_keeps_the_entire_current (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope) (current : Current) (action : Action) (cutoff : ℚ)
    (paid : (law base scope).Valid current action) (fits : (guard base scope current action).Holds cutoff) :
    (law base (withCutoff scope cutoff)).step current action = (law base scope).step current action := by
  rw [RawLaw.step, if_pos ((original_valid_iff_guard base scope current action cutoff paid).mpr fits),
    RawLaw.step, if_pos paid]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
