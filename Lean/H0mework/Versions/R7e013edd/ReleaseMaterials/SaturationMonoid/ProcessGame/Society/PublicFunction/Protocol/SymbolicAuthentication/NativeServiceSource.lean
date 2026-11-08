import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

def nativeKind : UnifiedRecoveryDispatch.Kind → Bool
  | .recovery | .original .withdrawal => true
  | _ => false
abbrev visit (past : JointResponse.Stages model) := EventStep.boundary (EventHistory.execute start past)
abbrev after (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :=
  EventHistory.execute start (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
abbrev family := ActualInventoryPrefix.family model
abbrev inputs (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :=
  ActualInventoryPrefix.inputs model (after model start vocabulary encoding law past action)
abbrev candidates (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :=
  CompletedInventory.originals (family model) (inputs model start vocabulary encoding law past action) (visit model start past)
def eligible (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (original : Claim (family model) (inputs model start vocabulary encoding law past action)) : Bool :=
  CompletedInventory.live _ _ (visit model start past) original &&
    !(CompletedInventory.live _ _ (visit model start past + 1) original)

private theorem every_completed_original_precedes_the_visit
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (original : Claim (family model) (inputs model start vocabulary encoding law past action))
    (member : original ∈ candidates model start vocabulary encoding law past action) : original.position.ordinal < visit model start past := by
  obtain ⟨ordinal, before, decoded⟩ := List.mem_flatMap.mp member
  obtain ⟨position, _, found⟩ := List.mem_filterMap.mp decoded
  have positionAt := Mandate.Challenge.read_position _ _ position original found
  obtain ⟨index, _, shape⟩ := List.mem_map.mp (show position ∈ positionsAt _ _ ordinal from by assumption)
  rw [positionAt, ← shape]
  exact List.mem_range.mp before

structure Receipt (past : JointResponse.Stages model) where
  private mk ::
  action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past
  selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance action
  native : nativeKind (UnifiedRecoveryDispatch.kind model start vocabulary encoding law action) = true
  original : Claim (family model) (inputs model start vocabulary encoding law past action)
  old : original.position.ordinal < visit model start past
  pending : CompletedInventory.live _ _ (visit model start past) original = true
  terminal : CompletedInventory.live _ _ (visit model start past + 1) original = false

def atAction (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance action) :
    Option (Receipt model start vocabulary encoding law past) :=
  if native : nativeKind (UnifiedRecoveryDispatch.kind model start vocabulary encoding law action) = true then
    match found : (candidates model start vocabulary encoding law past action).find? (eligible model start vocabulary encoding law past action) with
    | none => none
    | some original =>
      have checked : CompletedInventory.live _ _ (visit model start past) original = true ∧
          CompletedInventory.live _ _ (visit model start past + 1) original = false := by
        simpa only [eligible, Bool.and_eq_true, Bool.not_eq_true'] using List.find?_some found
      some ⟨action, selected, native, original,
        every_completed_original_precedes_the_visit model start vocabulary encoding law past action original (List.mem_of_find?_eq_some found),
        checked.1, checked.2⟩
  else none

def produce (past : JointResponse.Stages model) : Option (Receipt model start vocabulary encoding law past) :=
  match selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
  | .advance action => atAction model start vocabulary encoding law past action selected
  | _ => none

theorem every_productive_native_visit_is_recorded
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance action)
    (native : nativeKind (UnifiedRecoveryDispatch.kind model start vocabulary encoding law action) = true)
    (productive : 0 < CompletedInventory.closedOld (family model)
      (inputs model start vocabulary encoding law past action) (visit model start past)) :
    (atAction model start vocabulary encoding law past action selected).isSome = true := by
  unfold atAction
  rw [dif_pos native]
  split
  · rename_i missing
    have empty := List.filter_eq_nil_iff.mpr (List.find?_eq_none.mp missing)
    change ((candidates model start vocabulary encoding law past action).filter
      (eligible model start vocabulary encoding law past action)).length > 0 at productive
    rw [empty, List.length_nil] at productive
    omega
  · rfl

theorem every_record_is_one_actual_native_stage (past : JointResponse.Stages model)
    (receipt : Receipt model start vocabulary encoding law past) :
    (UnifiedRecoveryDispatch.after model start vocabulary encoding law past receipt.action).length = past.length + 1 ∧
    EventStep.boundary (after model start vocabulary encoding law past receipt.action) = visit model start past + 1 := by
  have length : (UnifiedRecoveryDispatch.after model start vocabulary encoding law past receipt.action).length = past.length + 1 := by
    have native := receipt.native
    cases chosen : receipt.action with
    | recovery => simp only [UnifiedRecoveryDispatch.after, NativeRecovery.full, NativeRecoveryMaterial.full, List.length_append, List.length_singleton]
    | original action =>
      rw [chosen] at native
      cases action with
      | withdrawal => simp only [UnifiedRecoveryDispatch.after, JointResponse.after, List.length_append, List.length_singleton]
      | communication action => cases action <;> simp [nativeKind, UnifiedRecoveryDispatch.kind, JointResponse.kind, UnifiedResponse.kind] at native
      | refused | wait => simp [nativeKind, UnifiedRecoveryDispatch.kind, JointResponse.kind] at native
  refine ⟨length, ?_⟩
  rw [IncidentChallenge.execution_advances_the_actual_boundary, length]
  rw [visit, IncidentChallenge.execution_advances_the_actual_boundary]
  omega

theorem every_record_has_strict_completed_inventory_progress (past : JointResponse.Stages model)
    (receipt : Receipt model start vocabulary encoding law past) :
    0 < CompletedInventory.closedOld (family model) (inputs model start vocabulary encoding law past receipt.action) (visit model start past) ∧
    CompletedInventory.openBorn (family model) (inputs model start vocabulary encoding law past receipt.action) (visit model start past) = 0 ∧
    CompletedInventory.pending (family model) (inputs model start vocabulary encoding law past receipt.action) (visit model start past + 1) <
      CompletedInventory.pending (family model) (inputs model start vocabulary encoding law past receipt.action) (visit model start past) := by
  have closed := CompletedInventory.an_actual_old_terminalization_is_counted (family model)
    (inputs model start vocabulary encoding law past receipt.action) (visit model start past) receipt.original
    receipt.old receipt.pending receipt.terminal
  have empty : MixedBirthAction.births model start vocabulary encoding law past receipt.action = 0 := by
    have native := receipt.native
    cases chosen : receipt.action with
    | recovery answer => exact MixedBirthAction.every_actual_recovery_has_no_open_births model start vocabulary encoding law past answer
    | original action =>
      rw [chosen] at native
      cases action with
      | withdrawal ready _ _ => exact MixedBirthAction.every_native_withdrawal_or_refusal_has_no_new_births model start past ready
      | communication action => cases action <;> simp [nativeKind, UnifiedRecoveryDispatch.kind, JointResponse.kind, UnifiedResponse.kind] at native
      | refused | wait => simp [nativeKind, UnifiedRecoveryDispatch.kind, JointResponse.kind] at native
  have boundary := (every_record_is_one_actual_native_stage model start vocabulary encoding law past receipt).1
  have factor := MixedBirthAction.tail_is_the_literal_actual_extension model start vocabulary encoding law past receipt.action
  have singleton : (MixedBirthAction.tail model start vocabulary encoding law past receipt.action).length = 1 := by
    have lengths := congrArg List.length factor
    simp only [List.length_append] at lengths
    omega
  unfold MixedBirthAction.births BirthWindow.births at empty
  rw [← OriginQueue.execute_append, factor, singleton] at empty
  change 0 + CompletedInventory.openBorn (family model) (inputs model start vocabulary encoding law past receipt.action)
    (visit model start past + 0) = 0 at empty
  simp only [Nat.zero_add, Nat.add_zero] at empty
  exact ⟨closed, empty, CompletedInventory.one_actual_old_terminalization_without_open_newborns_strictly_lowers_the_complete_inventory
    _ _ _ receipt.original receipt.old receipt.pending receipt.terminal empty⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceSource
