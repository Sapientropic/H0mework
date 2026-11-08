import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyPreservingDispatch

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PersistentDutyEntry
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := MixedFundedEntry.width model start
abbrev blocks := MixedFundedEntry.blocks model start vocabulary encoding law
abbrev deadline := MixedFundedEntry.deadline model start vocabulary encoding law

-- The future guard contains primitive signature resources, with no future duty witness.
def resources (count : Nat) (past : JointResponse.Stages model) : Bool :=
  (List.range count).all fun n => FundedSignatureDescent.resources model start vocabulary encoding law
    (width model start) (atCut model start vocabulary encoding law past (n * width model start))

theorem the_original_dispatch_generates_all_future_content_gates
    (past : JointResponse.Stages model) (count : Nat)
    (initial : UnifiedResponse.duties model start vocabulary encoding law past = [])
    (funded : resources model start vocabulary encoding law count past = true) :
    MixedFundedEntry.check model start vocabulary encoding law count past = true := by
  have paid := List.all_eq_true.mp funded
  apply List.all_eq_true.mpr
  intro n inside
  apply Bool.and_eq_true_iff.mpr
  exact ⟨decide_eq_true (DutyPreservingDispatch.the_original_mixed_run_generates_persistent_content_confirmation
    model start vocabulary encoding law _ past initial), paid n inside⟩

theorem initial_confirmation_and_primitive_resources_generate_the_original_entry
    (past : JointResponse.Stages model) (delay : Nat)
    (initial : UnifiedResponse.duties model start vocabulary encoding law past = [])
    (funded : resources model start vocabulary encoding law (blocks model start vocabulary encoding law past) past = true)
    (reserve : deadline model start vocabulary encoding law past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (atCut model start vocabulary encoding law past (deadline model start vocabulary encoding law past))) :
    ∃ index,
      CommunicationProgressSource.locate model start vocabulary encoding law
        (CommunicationProgressSource.horizon model start vocabulary encoding law past) past = some index ∧
      index ≤ CommunicationProgressSource.horizon model start vocabulary encoding law past ∧
      CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past index) :=
  MixedFundedEntry.primitive_mixed_resources_generate_the_original_communication_entry model start vocabulary encoding law past delay
    (the_original_dispatch_generates_all_future_content_gates model start vocabulary encoding law past _ initial funded) reserve compliant

theorem every_actual_cut_retains_terminal_original_content_histories
    (past : JointResponse.Stages model) (rounds : Nat)
    (initial : UnifiedResponse.duties model start vocabulary encoding law past = []) :
    ∀ row ∈ StageDuty.histories start vocabulary encoding law (atCut model start vocabulary encoding law past rounds),
      row.2.2.state.TerminalAt 0 := by
  have empty := DutyPreservingDispatch.the_original_mixed_run_generates_persistent_content_confirmation
    model start vocabulary encoding law rounds past initial
  intro row inside
  obtain ⟨emission, original, same⟩ := List.mem_map.mp inside
  cases same
  apply (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law _ _ inside).mpr
  exact DutyOriginStability.empty_duties_mean_every_original_content_is_confirmed vocabulary model start encoding law _ empty emission original

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PersistentDutyEntry
