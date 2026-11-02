import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponseRun

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

abbrev Stages := JointResponse.Stages model
abbrev Action := JointResponse.Action model start vocabulary encoding law
abbrev Clear := JointResponse.Clear model start vocabulary encoding law

inductive Status where
  | jointComplete | exhausted | observationCut
  deriving DecidableEq

structure Result where
  stages : Stages model
  status : Status
  trace : List JointResponse.Kind

def run : Nat → Stages model → Result model
  | 0, past =>
    if Clear model start vocabulary encoding law past then ⟨past, .jointComplete, []⟩
    else if JointResponse.fuel model start past = 0 then ⟨past, .exhausted, []⟩
    else ⟨past, .observationCut, []⟩
  | rounds + 1, past => match JointResponse.step model start vocabulary encoding law past with
    | .clear _ => ⟨past, .jointComplete, []⟩
    | .exhausted _ => ⟨past, .exhausted, []⟩
    | .advance action =>
      let next := run rounds (JointResponse.after model start vocabulary encoding law past action)
      ⟨next.stages, next.status, JointResponse.kind model start vocabulary encoding law action :: next.trace⟩

def produce (past : Stages model) := run model start vocabulary encoding law (JointResponse.fuel model start past) past

theorem every_run_keeps_the_whole_source_history (rounds : Nat) (past : Stages model) :
    past <+: (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run]; split <;> first | exact List.prefix_refl _ | split <;> exact List.prefix_refl _
  | succ rounds ih =>
    simp only [run]
    split
    · exact List.prefix_refl _
    · exact List.prefix_refl _
    · exact (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law _ _).trans (ih _)

theorem completion_has_both_source_generated_gates (rounds : Nat) (past : Stages model)
    (complete : (run model start vocabulary encoding law rounds past).status = .jointComplete) :
    Clear model start vocabulary encoding law (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at complete ⊢; (split_ifs at complete ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointResponse.step model start vocabulary encoding law past <;>
      simp only [run, observed] at complete ⊢ <;> try contradiction
    · assumption
    · exact ih _ complete

theorem an_observation_cut_at_the_source_budget_has_no_actual_fuel (rounds : Nat) (past : Stages model)
    (bounded : JointResponse.fuel model start past ≤ rounds)
    (cut : (run model start vocabulary encoding law rounds past).status = .observationCut) :
    JointResponse.fuel model start (run model start vocabulary encoding law rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at cut ⊢; (split_ifs at cut ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointResponse.step model start vocabulary encoding law past <;>
      simp only [run, observed] at cut ⊢ <;> try contradiction
    rename_i action
    have spent := JointResponse.every_action_spends_actual_fuel model start vocabulary encoding law past action
    exact ih _ (by omega) cut

theorem observation_cuts_retain_positive_actual_fuel (rounds : Nat) (past : Stages model)
    (cut : (run model start vocabulary encoding law rounds past).status = .observationCut) :
    0 < JointResponse.fuel model start (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at cut ⊢; (split_ifs at cut ⊢; simp_all; omega)
  | succ rounds ih =>
    cases observed : JointResponse.step model start vocabulary encoding law past <;>
      simp only [run, observed] at cut ⊢ <;> try contradiction
    exact ih _ cut

theorem exhaustion_has_zero_actual_fuel (rounds : Nat) (past : Stages model)
    (empty : (run model start vocabulary encoding law rounds past).status = .exhausted) :
    JointResponse.fuel model start (run model start vocabulary encoding law rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at empty ⊢; (split_ifs at empty ⊢; simp_all)
  | succ rounds ih =>
    cases observed : JointResponse.step model start vocabulary encoding law past <;>
      simp only [run, observed] at empty ⊢ <;> try contradiction
    · assumption
    · exact ih _ empty

theorem source_budget_generates_complete_or_actual_exhaustion (past : Stages model) :
    (produce model start vocabulary encoding law past).status = .jointComplete ∨
      ((produce model start vocabulary encoding law past).status = .exhausted ∧
        JointResponse.fuel model start (produce model start vocabulary encoding law past).stages = 0) := by
  cases outcome : (produce model start vocabulary encoding law past).status with
  | jointComplete => exact Or.inl rfl
  | exhausted => exact Or.inr ⟨rfl, exhaustion_has_zero_actual_fuel model start vocabulary encoding law _ past outcome⟩
  | observationCut =>
    have positive := observation_cuts_retain_positive_actual_fuel model start vocabulary encoding law _ past outcome
    have zero := an_observation_cut_at_the_source_budget_has_no_actual_fuel model start vocabulary encoding law
      (JointResponse.fuel model start past) past (Nat.le_refl _) outcome
    omega

theorem original_incidents_and_confirmations_survive (past : Stages model) :
    StageAccountability.ledger start vocabulary encoding law past <+:
        StageAccountability.ledger start vocabulary encoding law (produce model start vocabulary encoding law past).stages ∧
      ∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
        (StageReception.run vocabulary encoding law start (produce model start vocabulary encoding law past).stages receiver
          (produce model start vocabulary encoding law past).stages.length).receipts := by
  obtain ⟨more, same⟩ := every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past
  change past ++ more = (produce model start vocabulary encoding law past).stages at same
  rw [← same]
  refine ⟨?_, fun receiver => StagePrefix.receipts_survive_actual_extension start past more vocabulary encoding law receiver⟩
  rw [StageAccountability.ledger_extends_by_its_generated_next]
  exact List.prefix_append _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponseRun
