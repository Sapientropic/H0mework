import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceSource
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

abbrev full (past : JointResponse.Stages model) := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
abbrev cut (past : JointResponse.Stages model) (index : Nat) := (full model start vocabulary encoding law past).take index

def Admissible (past : JointResponse.Stages model) (index : Nat) : Prop :=
  past.length ≤ index ∧ index ≤ past.length + UnifiedServiceWindow.deadline model start vocabulary encoding law past ∧
    index ≤ (full model start vocabulary encoding law past).length ∧
    SignatureEligibility.Clear model start vocabulary encoding law (cut model start vocabulary encoding law past index) ∧
    0 < JointResponse.fuel model start (cut model start vocabulary encoding law past index)
instance (past : JointResponse.Stages model) (index : Nat) : Decidable (Admissible model start vocabulary encoding law past index) := by
  unfold Admissible; infer_instance

structure Ready (past : JointResponse.Stages model) where
  private mk ::
  index : Nat
  history : JointResponse.Stages model
  original : history = cut model start vocabulary encoding law past index
  actual : Admissible model start vocabulary encoding law past index

theorem the_actual_initial_cut_is_the_literal_original_past (past : JointResponse.Stages model) :
    cut model start vocabulary encoding law past past.length = past := by
  obtain ⟨more, same⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past
  change (full model start vocabulary encoding law past).take past.length = past
  change past ++ more = full model start vocabulary encoding law past at same
  rw [← same]; simp

inductive Result (past : JointResponse.Stages model) where
  | cut (ready : Ready model start vocabulary encoding law past)
  | blocked

def produce (past : JointResponse.Stages model) : Result model start vocabulary encoding law past :=
  if initial : SignatureEligibility.Clear model start vocabulary encoding law past ∧ 0 < JointResponse.fuel model start past then
    .cut ⟨past.length, past, (the_actual_initial_cut_is_the_literal_original_past model start vocabulary encoding law past).symm, by
      have same := the_actual_initial_cut_is_the_literal_original_past model start vocabulary encoding law past
      have ordered := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law
        (JointResponse.fuel model start past) past
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _, ordered.length_le,
        by simpa only [same] using initial.1, by simpa only [same] using initial.2⟩⟩
  else
    match found : (List.range (past.length + UnifiedServiceWindow.deadline model start vocabulary encoding law past + 1)).find?
        (fun index => decide (Admissible model start vocabulary encoding law past index)) with
    | none => .blocked
    | some index => .cut ⟨index, cut model start vocabulary encoding law past index, rfl, by
        have yes : decide (Admissible model start vocabulary encoding law past index) = true :=
          List.find?_some (p := fun n => decide (Admissible model start vocabulary encoding law past n)) (a := index) found
        exact of_decide_eq_true yes⟩

theorem primitive_source_conditions_generate_the_actual_handoff
    (past : JointResponse.Stages model) (delayAllowance : Nat)
    (reserve : UnifiedServiceWindow.deadline model start vocabulary encoding law past + 1 ≤ JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delayAllowance (full model start vocabulary encoding law past))
    (available : SignatureClock.Available model start vocabulary encoding law past
      ((full model start vocabulary encoding law past).drop past.length)) :
    ∃ ready, produce model start vocabulary encoding law past = .cut ready := by
  obtain ⟨index, actual⟩ := UnifiedServiceWindow.primitive_source_conditions_generate_a_live_signature_cut_in_the_unified_execution
    model start vocabulary encoding law past delayAllowance reserve compliant available
  have admissible : Admissible model start vocabulary encoding law past index := actual
  unfold produce
  split
  · exact ⟨_, rfl⟩
  · split
    · rename_i empty
      have member : index ∈ List.range (past.length + UnifiedServiceWindow.deadline model start vocabulary encoding law past + 1) :=
        List.mem_range.mpr (by have inside := admissible.2.1; omega)
      have absent := List.find?_eq_none.mp empty index member
      have yes : decide (Admissible model start vocabulary encoding law past index) = true := decide_eq_true admissible
      exact False.elim (absent yes)
    · exact ⟨_, rfl⟩

theorem the_generated_cut_preserves_the_original_prefix_and_signature_journals
    (past : JointResponse.Stages model) (ready : Ready model start vocabulary encoding law past) :
    let actual := ready.history
    past <+: actual ∧ actual <+: full model start vocabulary encoding law past ∧
    SignatureEligibility.Clear model start vocabulary encoding law actual ∧ 0 < JointResponse.fuel model start actual ∧
    IncidentResponse.journal model start past vocabulary encoding law <+:
      IncidentResponse.journal model start actual vocabulary encoding law ∧
    RejectionResponse.journal model start past vocabulary encoding law <+:
      RejectionResponse.journal model start actual vocabulary encoding law := by
  dsimp only
  have ordered : past <+: ready.history := by
    rw [ready.original]
    have actual : cut model start vocabulary encoding law past past.length <+: cut model start vocabulary encoding law past ready.index :=
      List.take_prefix_take_left ready.actual.1
    simpa only [the_actual_initial_cut_is_the_literal_original_past model start vocabulary encoding law past] using actual
  have retained := ordered
  obtain ⟨more, same⟩ := ordered
  exact ⟨retained, by rw [ready.original]; exact List.take_prefix _ _,
    by simpa only [ready.original] using ready.actual.2.2.2.1,
    by simpa only [ready.original] using ready.actual.2.2.2.2,
    by simpa only [same] using IncidentRegistration.actual_history_extension_preserves_the_literal_original_journal model start vocabulary encoding law past more,
    by simpa only [same] using RejectionRegistration.actual_history_extension_preserves_the_literal_original_journal model start vocabulary encoding law past more⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceSource
