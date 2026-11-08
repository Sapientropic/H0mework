import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyConfirmation
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

abbrev key (emission : StageDuty.Emission start vocabulary encoding) := StageDuty.content emission.wire

def contents (past : List (EventHistory.Stage (code := code))) : Finset (StageDuty.Content (code := code)) :=
  (((StageDuty.origins start vocabulary encoding past).filter fun emission =>
    decide (TimedDuty.Confirmed start past vocabulary encoding law emission)).map (key start vocabulary encoding)).toFinset

theorem mem_contents (past : List (EventHistory.Stage (code := code))) (content : StageDuty.Content (code := code)) :
    content ∈ contents start vocabulary encoding law past ↔
      ∃ emission ∈ StageDuty.origins start vocabulary encoding past,
        TimedDuty.Confirmed start past vocabulary encoding law emission ∧ key start vocabulary encoding emission = content := by
  simp only [contents, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨emission, ⟨inside, done⟩, same⟩
    exact ⟨emission, inside, done, same⟩
  · rintro ⟨emission, inside, done, same⟩
    exact ⟨emission, ⟨inside, done⟩, same⟩

theorem confirmation_depends_on_the_original_content
    (past : List (EventHistory.Stage (code := code)))
    (first second : StageDuty.Emission start vocabulary encoding)
    (same : key start vocabulary encoding first = key start vocabulary encoding second) :
    TimedDuty.Confirmed start past vocabulary encoding law first ↔
      TimedDuty.Confirmed start past vocabulary encoding law second := by
  have ballot := congrArg Prod.fst same
  have recipient := congrArg Prod.snd same
  unfold TimedDuty.Confirmed TimedDuty.receipts
  change first.wire.ballot = second.wire.ballot at ballot
  change first.wire.recipient = second.wire.recipient at recipient
  rw [ballot, recipient]

theorem the_original_emission_survives_actual_extension
    (past more : List (EventHistory.Stage (code := code)))
    (emission : StageDuty.Emission start vocabulary encoding)
    (inside : emission ∈ StageDuty.origins start vocabulary encoding past) :
    emission ∈ StageDuty.origins start vocabulary encoding (past ++ more) := by
  obtain ⟨index, bounded, born⟩ := List.mem_filterMap.mp inside
  apply List.mem_filterMap.mpr
  refine ⟨index, List.mem_range.mpr (by have old := List.mem_range.mp bounded; simp only [List.length_append]; omega), ?_⟩
  exact (StageDuty.birth_survives_extension start vocabulary encoding past more index (List.mem_range.mp bounded)).trans born

theorem the_actual_confirmation_survives_extension
    (past more : List (EventHistory.Stage (code := code)))
    (emission : StageDuty.Emission start vocabulary encoding)
    (confirmed : TimedDuty.Confirmed start past vocabulary encoding law emission) :
    TimedDuty.Confirmed start (past ++ more) vocabulary encoding law emission := by
  obtain ⟨receipt, inside, same⟩ := confirmed
  exact ⟨receipt, (StagePrefix.receipts_survive_actual_extension start past more vocabulary encoding law emission.wire.recipient).subset inside, same⟩

theorem confirmed_contents_survive_actual_extension
    (past later : List (EventHistory.Stage (code := code))) (ordered : past <+: later) :
    contents start vocabulary encoding law past ⊆ contents start vocabulary encoding law later := by
  obtain ⟨more, rfl⟩ := ordered
  intro content inside
  obtain ⟨emission, original, confirmed, same⟩ := (mem_contents start vocabulary encoding law past content).mp inside
  exact (mem_contents start vocabulary encoding law _ content).mpr ⟨emission,
    the_original_emission_survives_actual_extension start vocabulary encoding past more emission original,
    the_actual_confirmation_survives_extension start vocabulary encoding law past more emission confirmed, same⟩

theorem every_confirmed_content_has_its_original_terminal_native_duty
    (past : List (EventHistory.Stage (code := code))) (content : StageDuty.Content (code := code))
    (inside : content ∈ contents start vocabulary encoding law past) :
    ∃ row ∈ StageDuty.histories start vocabulary encoding law past,
      key start vocabulary encoding row.1 = content ∧ row.2.2.state.TerminalAt 0 := by
  obtain ⟨emission, original, confirmed, same⟩ := (mem_contents start vocabulary encoding law past content).mp inside
  let row : Sigma (StageDuty.History start vocabulary encoding law) :=
    ⟨emission, StageDuty.through start vocabulary encoding law emission (past.drop emission.birthStages.length)⟩
  have member : row ∈ StageDuty.histories start vocabulary encoding law past := List.mem_map.mpr ⟨emission, original, rfl⟩
  exact ⟨row, member, same,
    (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law past row member).mpr confirmed⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyConfirmation
