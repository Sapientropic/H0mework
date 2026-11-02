import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponseRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedDuty

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (past : List (EventHistory.Stage (code := code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

abbrev current := EventHistory.execute start past
abbrev receipts (receiver : Fin code.sites) :=
  (StageReception.run vocabulary encoding law start past receiver past.length).receipts

def Confirmed (emission : StageDuty.Emission start vocabulary encoding) : Prop :=
  ∃ receipt ∈ receipts start past vocabulary encoding law emission.wire.recipient,
    receipt.wire.ballot = emission.wire.ballot

instance (emission : StageDuty.Emission start vocabulary encoding) :
    Decidable (Confirmed start past vocabulary encoding law emission) := by
  unfold Confirmed; infer_instance

-- A fresh attempt has its own window; the original duty keeps its content identity.
def latestSend (emission : StageDuty.Emission start vocabulary encoding) : Nat :=
  ((List.range past.length).filterMap (StageTransport.issuedAt vocabulary encoding start past)).foldl
    (fun cut wire => if StageDuty.content wire = StageDuty.content emission.wire then max cut wire.sendCut else cut)
    emission.wire.sendCut

structure Overdue where
  private mk ::
  emission : StageDuty.Emission start vocabulary encoding
  actual : emission ∈ StageDuty.origins start vocabulary encoding past
  unconfirmed : ¬ Confirmed start past vocabulary encoding law emission
  expired : latestSend start past vocabulary encoding emission + law.maxDelay < (current start past).cut

private def inspect (entry : {e // e ∈ StageDuty.origins start vocabulary encoding past}) :
    Option (Overdue start past vocabulary encoding law) :=
  if missing : ¬ Confirmed start past vocabulary encoding law entry.val then
    if expired : latestSend start past vocabulary encoding entry.val + law.maxDelay < (current start past).cut then
      some ⟨entry.val, entry.property, missing, expired⟩
    else none
  else none

def observed : List (Overdue start past vocabulary encoding law) :=
  (StageDuty.origins start vocabulary encoding past).attach.filterMap (inspect start past vocabulary encoding law)

def history (entry : Overdue start past vocabulary encoding law) :
    Sigma (StageDuty.History start vocabulary encoding law) :=
  ⟨entry.emission, StageDuty.through start vocabulary encoding law entry.emission
    (past.drop entry.emission.birthStages.length)⟩

theorem original_history_is_in_the_actual_census (entry : Overdue start past vocabulary encoding law) :
    history start past vocabulary encoding law entry ∈ StageDuty.histories start vocabulary encoding law past :=
  List.mem_map.mpr ⟨entry.emission, entry.actual, rfl⟩

theorem overdue_keeps_the_original_native_duty_live (entry : Overdue start past vocabulary encoding law) :
    ¬ (history start past vocabulary encoding law entry).2.2.state.TerminalAt 0 ∧
      entry.emission.birthStages ++ (history start past vocabulary encoding law entry).2.1 = past := by
  have actual := original_history_is_in_the_actual_census start past vocabulary encoding law entry
  exact ⟨fun terminal => entry.unconfirmed
    ((StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law past _ actual).mp terminal),
    StageDuty.generated_row_observes_the_original_whole_history start vocabulary encoding law past _ actual⟩

theorem original_emission_survives_extension (entry : Overdue start past vocabulary encoding law)
    (more : List (EventHistory.Stage (code := code))) :
    entry.emission ∈ StageDuty.origins start vocabulary encoding (past ++ more) := by
  obtain ⟨index, bounded, born⟩ := List.mem_filterMap.mp entry.actual
  exact List.mem_filterMap.mpr ⟨index,
    List.mem_range.mpr (by have bound := List.mem_range.mp bounded; simp only [List.length_append]; omega),
    (StageDuty.birth_survives_extension start vocabulary encoding past more index (List.mem_range.mp bounded)).trans born⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedDuty
