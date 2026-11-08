import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeInventoryPrefix

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualInventoryPrefix
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace Mandate.Challenge
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

theorem complete_visits_are_preserved (cursor : Cursor code) (tail : List (EventHistory.Stage (code := code)))
    (ordinal : Nat) (inside : ordinal ≤ EventStep.boundary cursor) :
    (ProgrammeHistory.visitAt (EventHistory.execute cursor tail).source.input ordinal).current =
      (ProgrammeHistory.visitAt cursor.source.input ordinal).current := by
  induction tail generalizing cursor with
  | nil => rfl
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    have boundary : EventStep.boundary (cursor.after protocol rival) = EventStep.boundary cursor + 1 := rfl
    have later := ih (cursor.after protocol rival) (by rw [boundary]; omega)
    have first := Machine.actual_prefix_from_events cursor.source.input (Cursor.target cursor protocol rival).input
      rfl rfl (EventStep.boundary cursor)
      (Future.prior_raw_event cursor.source cursor.entry cursor.cut (Cursor.controller cursor protocol rival)
        (term cursor.source cursor.entry cursor.cut protocol).val rfl) ordinal inside
    exact later.trans first

theorem original_initial_is_preserved (cursor : Cursor code) (tail : List (EventHistory.Stage (code := code))) :
    (EventHistory.execute cursor tail).source.input.initial = cursor.source.input.initial := by
  induction tail generalizing cursor with
  | nil => rfl
  | cons stage tail ih => exact (ih (cursor.after stage.1 stage.2)).trans rfl

theorem actual_events_are_preserved (cursor : Cursor code) (tail : List (EventHistory.Stage (code := code))) :
    ∀ ordinal < EventStep.boundary cursor,
      ProgrammeSource.rawEvent (EventHistory.execute cursor tail).source.input
          (ProgrammeHistory.visitAt cursor.source.input ordinal).current =
        ProgrammeSource.rawEvent cursor.source.input (ProgrammeHistory.visitAt cursor.source.input ordinal).current := by
  intro ordinal inside
  have words := (StageTrace.final_preserves_the_complete_past cursor tail).2 ordinal inside
  rw [complete_visits_are_preserved cursor tail ordinal (by omega)] at words
  exact words

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

abbrev family := Native.Authority.programme model
abbrev inputs (cursor : Cursor model.source.code) := Native.Authority.sourceIndex (LocalContentRuntime.native model cursor)

def originalAt (cursor : Cursor model.source.code) (tail : JointResponse.Stages model)
    (original : Claim (family model) (inputs model cursor))
    (inside : original.position.ordinal < EventStep.boundary cursor) :
    Claim (family model) (inputs model (EventHistory.execute cursor tail)) :=
  Cross.Programme.replacement (family model) (EventStep.boundary cursor)
    (Feedback.Authority.Trace.ChallengeTransport.items (family model)
      (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
      (EventStep.boundary cursor) (original_initial_is_preserved cursor tail) (actual_events_are_preserved cursor tail)) original inside

theorem the_actual_original_and_its_entire_native_prefix_are_preserved
    (cursor : Cursor model.source.code) (tail : JointResponse.Stages model)
    (original : Claim (family model) (inputs model cursor))
    (inside : original.position.ordinal < EventStep.boundary cursor) (count : Nat)
    (bounded : count ≤ EventStep.boundary cursor) :
    let target := originalAt model cursor tail original inside
    Feedback.Authority.Trace.challengeImage model.source.code (family model)
      (inputs model (EventHistory.execute cursor tail)) target =
      Feedback.Authority.Trace.challengeImage model.source.code (family model) (inputs model cursor) original ∧
    Feedback.Authority.Trace.challengeStateImage model.source.code (family model)
      (inputs model (EventHistory.execute cursor tail))
      (through (family model) (inputs model (EventHistory.execute cursor tail)) target count).state.current =
      Feedback.Authority.Trace.challengeStateImage model.source.code (family model) (inputs model cursor)
        (through (family model) (inputs model cursor) original count).state.current ∧
    CompletedInventory.live (family model) (inputs model (EventHistory.execute cursor tail)) count target =
      CompletedInventory.live (family model) (inputs model cursor) count original := by
  dsimp only
  have same := Feedback.Authority.Trace.ChallengeTransport.claim_image model.source.code (family model)
    (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
    (EventStep.boundary cursor) (original_initial_is_preserved cursor tail) (actual_events_are_preserved cursor tail) original inside
  have matched := Feedback.Authority.Trace.LocalLifecycle.through_match model.source.code (family model)
    (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
    (EventStep.boundary cursor) (original_initial_is_preserved cursor tail) (actual_events_are_preserved cursor tail) count bounded same
  exact ⟨same, matched.state, NativeInventoryPrefix.actual_pending_is_preserved model.source.code (family model)
    (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
    (EventStep.boundary cursor) (original_initial_is_preserved cursor tail) (actual_events_are_preserved cursor tail) count bounded _ _ same⟩

theorem one_actual_extension_preserves_the_complete_inventory_slices
    (cursor : Cursor model.source.code) (tail : JointResponse.Stages model) (count : Nat)
    (inside : count + 1 ≤ EventStep.boundary cursor) :
    CompletedInventory.pending (family model) (inputs model (EventHistory.execute cursor tail)) count =
      CompletedInventory.pending (family model) (inputs model cursor) count ∧
    CompletedInventory.pending (family model) (inputs model (EventHistory.execute cursor tail)) (count + 1) =
      CompletedInventory.pending (family model) (inputs model cursor) (count + 1) ∧
    CompletedInventory.openBorn (family model) (inputs model (EventHistory.execute cursor tail)) count =
      CompletedInventory.openBorn (family model) (inputs model cursor) count ∧
    CompletedInventory.closedOld (family model) (inputs model (EventHistory.execute cursor tail)) count =
      CompletedInventory.closedOld (family model) (inputs model cursor) count := by
  have initial := original_initial_is_preserved cursor tail
  have events := actual_events_are_preserved cursor tail
  exact ⟨NativeInventoryPrefix.the_complete_pending_inventory_is_preserved model.source.code (family model)
      (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
      (EventStep.boundary cursor) initial events count (by omega),
    NativeInventoryPrefix.the_complete_pending_inventory_is_preserved model.source.code (family model)
      (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
      (EventStep.boundary cursor) initial events (count + 1) inside,
    NativeInventoryPrefix.the_actual_open_birth_slice_is_preserved model.source.code (family model)
      (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
      (EventStep.boundary cursor) initial events count inside,
    NativeInventoryPrefix.the_actual_old_disposition_slice_is_preserved model.source.code (family model)
      (inputs := inputs model cursor) (nextInputs := inputs model (EventHistory.execute cursor tail))
      (EventStep.boundary cursor) initial events count inside⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualInventoryPrefix
