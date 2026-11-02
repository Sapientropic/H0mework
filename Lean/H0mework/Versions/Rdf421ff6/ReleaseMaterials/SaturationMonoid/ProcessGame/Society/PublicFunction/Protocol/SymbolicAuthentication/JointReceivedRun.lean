import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedResponse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedRun

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
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
  (observedAt : Nat)

abbrev Stages := JointReceivedResponse.Stages model
abbrev Action := JointReceivedResponse.Action model start vocabulary encoding law observedAt
abbrev Clear := JointReceivedResponse.Clear model start vocabulary encoding law observedAt

inductive Status where
  | jointComplete | exhausted | observationCut
  deriving DecidableEq

structure Result where
  stages : Stages model
  status : Status
  trace : List JointReceivedResponse.Kind

def run : Nat → Stages model → Result model
  | 0, past =>
    if Clear model start vocabulary encoding law observedAt past then ⟨past, .jointComplete, []⟩
    else if JointReceivedResponse.fuel model start past = 0 then ⟨past, .exhausted, []⟩
    else ⟨past, .observationCut, []⟩
  | rounds + 1, past => match JointReceivedResponse.step model start vocabulary encoding law observedAt past with
    | .clear _ => ⟨past, .jointComplete, []⟩
    | .exhausted _ => ⟨past, .exhausted, []⟩
    | .advance action =>
      let next := run rounds (JointReceivedResponse.after model start vocabulary encoding law observedAt past action)
      ⟨next.stages, next.status, JointReceivedResponse.kind model start vocabulary encoding law observedAt action :: next.trace⟩

def produce (past : Stages model) := run model start vocabulary encoding law observedAt (JointReceivedResponse.fuel model start past) past

theorem every_run_keeps_the_whole_source_history (rounds : Nat) (past : Stages model) :
    past <+: (run model start vocabulary encoding law observedAt rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run]; split <;> first | exact List.prefix_refl _ | split <;> exact List.prefix_refl _
  | succ rounds ih =>
    simp only [run]
    split
    · exact List.prefix_refl _
    · exact List.prefix_refl _
    · exact (JointReceivedResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law observedAt _ _).trans (ih _)

theorem completion_has_all_same_cut_gates (rounds : Nat) (past : Stages model)
    (complete : (run model start vocabulary encoding law observedAt rounds past).status = .jointComplete) :
    Clear model start vocabulary encoding law observedAt (run model start vocabulary encoding law observedAt rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at complete ⊢; (split_ifs at complete ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointReceivedResponse.step model start vocabulary encoding law observedAt past <;>
      simp only [run, observed] at complete ⊢ <;> try contradiction
    · assumption
    · exact ih _ complete

theorem an_observation_cut_at_the_source_budget_has_no_actual_fuel (rounds : Nat) (past : Stages model)
    (bounded : JointReceivedResponse.fuel model start past ≤ rounds)
    (cut : (run model start vocabulary encoding law observedAt rounds past).status = .observationCut) :
    JointReceivedResponse.fuel model start (run model start vocabulary encoding law observedAt rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at cut ⊢; (split_ifs at cut ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointReceivedResponse.step model start vocabulary encoding law observedAt past <;>
      simp only [run, observed] at cut ⊢ <;> try contradiction
    rename_i action
    have spent := JointReceivedResponse.every_action_spends_actual_fuel model start vocabulary encoding law observedAt past action
    exact ih _ (by omega) cut

theorem observation_cuts_retain_positive_actual_fuel (rounds : Nat) (past : Stages model)
    (cut : (run model start vocabulary encoding law observedAt rounds past).status = .observationCut) :
    0 < JointReceivedResponse.fuel model start (run model start vocabulary encoding law observedAt rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at cut ⊢; (split_ifs at cut ⊢; simp_all; omega)
  | succ rounds ih =>
    cases observed : JointReceivedResponse.step model start vocabulary encoding law observedAt past <;>
      simp only [run, observed] at cut ⊢ <;> try contradiction
    exact ih _ cut

theorem exhaustion_has_zero_actual_fuel (rounds : Nat) (past : Stages model)
    (empty : (run model start vocabulary encoding law observedAt rounds past).status = .exhausted) :
    JointReceivedResponse.fuel model start (run model start vocabulary encoding law observedAt rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at empty ⊢; (split_ifs at empty ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointReceivedResponse.step model start vocabulary encoding law observedAt past <;>
      simp only [run, observed] at empty ⊢ <;> try contradiction
    · assumption
    · exact ih _ empty

theorem exhaustion_keeps_an_actual_unclosed_gate (rounds : Nat) (past : Stages model)
    (empty : (run model start vocabulary encoding law observedAt rounds past).status = .exhausted) :
    ¬ Clear model start vocabulary encoding law observedAt (run model start vocabulary encoding law observedAt rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at empty ⊢; (split_ifs at empty ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointReceivedResponse.step model start vocabulary encoding law observedAt past <;>
      simp only [run, observed] at empty ⊢ <;> try contradiction
    · intro clear
      have selected : JointReceivedResponse.step model start vocabulary encoding law observedAt past = .clear clear := by
        simp only [JointReceivedResponse.step, dif_pos clear]
      rw [selected] at observed
      contradiction
    · exact ih _ empty

theorem source_budget_generates_complete_or_actual_exhaustion (past : Stages model) :
    (produce model start vocabulary encoding law observedAt past).status = .jointComplete ∨
      ((produce model start vocabulary encoding law observedAt past).status = .exhausted ∧
        JointReceivedResponse.fuel model start (produce model start vocabulary encoding law observedAt past).stages = 0) := by
  cases outcome : (produce model start vocabulary encoding law observedAt past).status with
  | jointComplete => exact Or.inl rfl
  | exhausted => exact Or.inr ⟨rfl, exhaustion_has_zero_actual_fuel model start vocabulary encoding law observedAt _ past outcome⟩
  | observationCut =>
    have positive := observation_cuts_retain_positive_actual_fuel model start vocabulary encoding law observedAt _ past outcome
    have zero := an_observation_cut_at_the_source_budget_has_no_actual_fuel model start vocabulary encoding law observedAt
      (JointReceivedResponse.fuel model start past) past (Nat.le_refl _) outcome
    omega

theorem the_original_joint_continuation_adds_no_stage (past : Stages model) :
    (LocalJointRun.produce model start vocabulary encoding law
      (produce model start vocabulary encoding law observedAt past).stages).stages =
      (produce model start vocabulary encoding law observedAt past).stages := by
  rcases source_budget_generates_complete_or_actual_exhaustion model start vocabulary encoding law observedAt past with complete | ⟨_, empty⟩
  · have clear := (completion_has_all_same_cut_gates model start vocabulary encoding law observedAt _ past complete).1
    change LocalJointResponse.Clear model start vocabulary encoding law (produce model start vocabulary encoding law observedAt past).stages at clear
    unfold LocalJointRun.produce
    cases fuel : LocalJointResponse.fuel model start (produce model start vocabulary encoding law observedAt past).stages with
    | zero => simp only [LocalJointRun.run]; split_ifs <;> rfl
    | succ count =>
      have selected : LocalJointResponse.step model start vocabulary encoding law
          (produce model start vocabulary encoding law observedAt past).stages = .clear clear := by
        simp only [LocalJointResponse.step, UnifiedResponse.step, dif_pos clear.1, dif_pos clear.2]
      simp only [LocalJointRun.run, selected]
  · change LocalJointResponse.fuel model start (produce model start vocabulary encoding law observedAt past).stages = 0 at empty
    unfold LocalJointRun.produce
    rw [empty]
    simp only [LocalJointRun.run]
    split_ifs <;> rfl

theorem original_incidents_and_confirmations_survive (past : Stages model) :
    StageAccountability.ledger start vocabulary encoding law past <+:
        StageAccountability.ledger start vocabulary encoding law (produce model start vocabulary encoding law observedAt past).stages ∧
      ∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
        (StageReception.run vocabulary encoding law start (produce model start vocabulary encoding law observedAt past).stages receiver
          (produce model start vocabulary encoding law observedAt past).stages.length).receipts := by
  obtain ⟨more, same⟩ := every_run_keeps_the_whole_source_history model start vocabulary encoding law observedAt
    (JointReceivedResponse.fuel model start past) past
  change past ++ more = (produce model start vocabulary encoding law observedAt past).stages at same
  rw [← same]
  refine ⟨?_, fun receiver => StagePrefix.receipts_survive_actual_extension start past more vocabulary encoding law receiver⟩
  rw [StageAccountability.ledger_extends_by_its_generated_next]
  exact List.prefix_append _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedRun
