import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentrySource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource (code)
open RecycledQuorumMaterial (Action)

abbrev bound (cursor : Cursor code) : MaterialRoundSource.Bound :=
  ⟨FuelMandateLaw.base true,Repayment.Recovery.scope,cursor.source,rfl,rfl⟩
abbrev incoming (cursor : Cursor code) := FuelMaterialSource.incoming (bound cursor) cursor.cut
abbrev produce (cursor : Cursor code) := FuelMaterialSource.produce (bound cursor) cursor.cut
abbrev status (cursor : Cursor code) := FuelMaterialSource.status (bound cursor) cursor.cut
abbrev before (cursor : Cursor code) := MaterialRoundSource.before (bound cursor) cursor.cut

theorem the_actual_feedback_endpoint_is_the_material_input (cursor : Cursor code) :
    before cursor = (EventStep.seed cursor).current := by
  have index : cursor.source.history.length+1+cursor.cut+1 = cursor.source.history.length+2+cursor.cut := by omega
  change cursor.source.currentAt (cursor.source.history.length+1+cursor.cut+1) = _
  rw [index]
  exact cursor.source.feedback_current_is_actual cursor.entry rfl rfl cursor.cut

theorem matched_actual_cursors_have_the_same_complete_raw_snapshot
    (left right : Cursor code) (same : EventStep.Matches left right) :
    RoundArchive.snapshot left.source left.cut = RoundArchive.snapshot right.source right.cut := by
  apply List.ext_getElem
  · simp only [RoundArchive.snapshot_length,RoundArchive.depth,same.history_length,same.cut]
  · intro index first second
    rw [RoundArchive.snapshot_length] at second
    simp only [RoundArchive.snapshot,List.getElem_ofFn]
    have words := same.words (index+1) (by
      dsimp only [RoundArchive.depth,EventStep.boundary] at *;omega)
    exact words

theorem matched_actual_cursors_have_the_same_material_input
    (left right : Cursor code) (same : EventStep.Matches left right) :
    before left = before right ∧ incoming left = incoming right := by
  have currents : before left = before right := by
    rw [the_actual_feedback_endpoint_is_the_material_input,the_actual_feedback_endpoint_is_the_material_input,same.state]
  refine ⟨currents,?_⟩
  unfold incoming FuelMaterialSource.incoming
  change (if (before left).stock 0 .feedstock < 1 ∧ FuelMandateLaw.Inputs (before left) then _ else _) = _
  rw [currents]

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

theorem a_continuation_snapshot_is_the_actual_old_snapshot_and_its_new_word
    (old : Machine Party Good Port Technology Instrument) (count : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    RoundArchive.snapshot (Machine.Continuation.extend old count word) (count+1) =
      RoundArchive.snapshot old count ++ [word] := by
  have length : RoundArchive.depth (Machine.Continuation.extend old count word) (count+1) =
      RoundArchive.depth old count+1 := rfl
  apply List.ext_getElem
  · simp only [RoundArchive.snapshot_length,List.length_append,List.length_singleton,length]
  · intro index first second
    rw [RoundArchive.snapshot_length] at first
    simp only [RoundArchive.snapshot,List.getElem_ofFn]
    by_cases earlier : index < RoundArchive.depth old count
    · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using earlier)]
      simp only [List.getElem_ofFn]
      have currents : (Machine.Continuation.extend old count word).currentAt (index+1) = old.currentAt (index+1) := by
        unfold Machine.currentAt
        rw [Machine.Continuation.prior_currents old count word (index+1) (by
          change index < Machine.Continuation.depth old count at earlier;omega)]
        rfl
      rw [(Machine.Continuation.extend old count word).actual_word,old.actual_word,currents]
      exact Machine.Continuation.earlier_body old count word index earlier
    · have last : index = RoundArchive.depth old count := by
        rw [length] at first;omega
      subst index
      rw [List.getElem_append_right (by rw [List.length_ofFn])]
      simp only [List.length_ofFn,Nat.sub_self,List.getElem_cons_zero]
      exact Machine.Continuation.submitted old count word

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentrySource
