import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryWindow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceEnvelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryRun

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (observed : BatchReentry.Stages model) (retainedAt : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (target : Fin model.source.code.sites) (allowance : Nat)

abbrev goal := RecoveryWindow.Goal model start observed retainedAt vocabulary encoding law target
abbrev fuel (past : BatchReentry.Stages model) := (EventStep.seed (EventHistory.execute start past)).remaining
abbrev extend (past : BatchReentry.Stages model) (rule : Rule model.source.code) (move : Move model.source.code) :=
  past ++ [(rule, EventStep.fixed move)]

-- Universal branches come from the actual source envelope at the current cut.
def guarantees : List (Rule model.source.code) → BatchReentry.Stages model → Bool
  | [], past => decide (goal model start observed retainedAt vocabulary encoding law target past)
  | rule :: tail, past =>
    if goal model start observed retainedAt vocabulary encoding law target past then true
    else if fuel model start past = 0 then false
    else (InterferenceEnvelope.choices start past allowance).all fun move =>
      guarantees tail (extend model past rule move)

inductive Status where
  | recovered | exhausted | windowEnded | communicationViolation
  deriving DecidableEq

structure Result where
  past : BatchReentry.Stages model
  status : Status
  inputs : List (InterferenceEnvelope.Input model.source.code)

-- This executor observes the real callback, not a successful search leaf.
-- Out-of-envelope intake takes its admitted native step and keeps the raw input.
def execute : List (Rule model.source.code) → BatchReentry.Stages model → Opponent model.source.code → Result model
  | [], past, _ => ⟨past, if goal model start observed retainedAt vocabulary encoding law target past then .recovered
      else if fuel model start past = 0 then .exhausted else .windowEnded, []⟩
  | rule :: tail, past, rival =>
    if goal model start observed retainedAt vocabulary encoding law target past then ⟨past, .recovered, []⟩
    else if fuel model start past = 0 then ⟨past, .exhausted, []⟩
    else
      let input := InterferenceEnvelope.observe start past allowance rival
      let actual := extend model past rule input.admitted
      if input.within then
        let next := execute tail actual rival
        ⟨next.past, next.status, input :: next.inputs⟩
      else ⟨actual, .communicationViolation, [input]⟩

def program := RecoveryWindow.program model start observed retainedAt vocabulary encoding law
def guaranteed := guarantees model start observed retainedAt vocabulary encoding law target allowance
  (program model start observed retainedAt vocabulary encoding law) observed
def produce (rival : Opponent model.source.code) := execute model start observed retainedAt vocabulary encoding law target allowance
  (program model start observed retainedAt vocabulary encoding law) observed rival

theorem recovered_means_an_actual_paid_recovery
    (todo : List (Rule model.source.code)) (past : BatchReentry.Stages model) (rival : Opponent model.source.code)
    (accepted : (execute model start observed retainedAt vocabulary encoding law target allowance todo past rival).status = .recovered) :
    goal model start observed retainedAt vocabulary encoding law target
      (execute model start observed retainedAt vocabulary encoding law target allowance todo past rival).past := by
  induction todo generalizing past with
  | nil =>
    dsimp only [execute] at accepted ⊢
    split_ifs at accepted with complete
    · exact complete
  | cons rule tail ih =>
    dsimp only [execute] at accepted ⊢
    split_ifs at accepted ⊢ <;> first | assumption | exact ih _ accepted

theorem every_compliant_adaptive_callback_recovers
    (todo : List (Rule model.source.code)) (past : BatchReentry.Stages model) (rival : Opponent model.source.code)
    (certified : guarantees model start observed retainedAt vocabulary encoding law target allowance todo past = true)
    (compliant : ((execute model start observed retainedAt vocabulary encoding law target allowance todo past rival).inputs.all
      fun input => input.within) = true) :
    (execute model start observed retainedAt vocabulary encoding law target allowance todo past rival).status = .recovered := by
  induction todo generalizing past with
  | nil =>
    have complete := of_decide_eq_true certified
    simp only [execute, if_pos complete]
  | cons rule tail ih =>
    by_cases complete : goal model start observed retainedAt vocabulary encoding law target past
    · simp only [execute, if_pos complete]
    · by_cases empty : fuel model start past = 0
      · simp only [guarantees, if_neg complete, if_pos empty] at certified
        contradiction
      · simp only [guarantees, if_neg complete, if_neg empty] at certified
        simp only [execute, if_neg complete, if_neg empty] at compliant ⊢
        by_cases supported : (InterferenceEnvelope.observe start past allowance rival).within = true
        · simp only [if_pos supported] at compliant ⊢
          have pair : (InterferenceEnvelope.observe start past allowance rival).within = true ∧
              ((execute model start observed retainedAt vocabulary encoding law target allowance tail
                (extend model past rule (InterferenceEnvelope.observe start past allowance rival).admitted) rival).inputs.all
                  fun input => input.within) = true := by
            simpa only [List.all_cons, Bool.and_eq_true] using compliant
          have inside : (InterferenceEnvelope.observe start past allowance rival).admitted ∈
              InterferenceEnvelope.choices start past allowance := of_decide_eq_true pair.1
          exact ih _ (List.all_eq_true.mp certified _ inside) pair.2
        · simp only [if_neg supported, List.all_cons, List.all_nil, Bool.and_true] at compliant
          contradiction

theorem execution_keeps_the_prefix_and_spends_only_its_program
    (todo : List (Rule model.source.code)) (past : BatchReentry.Stages model) (rival : Opponent model.source.code) :
    past <+: (execute model start observed retainedAt vocabulary encoding law target allowance todo past rival).past ∧
    (execute model start observed retainedAt vocabulary encoding law target allowance todo past rival).past.length ≤ past.length + todo.length := by
  induction todo generalizing past with
  | nil => exact ⟨List.prefix_refl _, by simp [execute]⟩
  | cons rule tail ih =>
    dsimp only [execute]
    split_ifs
    · exact ⟨List.prefix_refl _, by simp⟩
    · exact ⟨List.prefix_refl _, by simp⟩
    · have rest := ih (extend model past rule (InterferenceEnvelope.observe start past allowance rival).admitted)
      refine ⟨(List.prefix_append _ _).trans rest.1, ?_⟩
      have bound := rest.2
      have edgeLength : (extend model past rule (InterferenceEnvelope.observe start past allowance rival).admitted).length = past.length + 1 := by
        simp [extend]
      rw [edgeLength] at bound
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
    · exact ⟨List.prefix_append _ _, by simp [extend]⟩

theorem the_generated_window_has_a_source_paid_deadline (rival : Opponent model.source.code) :
    observed <+: (produce model start observed retainedAt vocabulary encoding law target allowance rival).past ∧
    (produce model start observed retainedAt vocabulary encoding law target allowance rival).past.length ≤
      observed.length + min (fuel model start observed) (4 * model.source.code.sites) := by
  have actual := execution_keeps_the_prefix_and_spends_only_its_program model start observed retainedAt vocabulary encoding law target allowance
    (program model start observed retainedAt vocabulary encoding law) observed rival
  have clock := RecoveryWindow.the_source_clock_bounds_the_complete_local_program model start observed retainedAt vocabulary encoding law
  exact ⟨actual.1, actual.2.trans (Nat.add_le_add_left (Nat.le_min.mpr clock) _)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryRun
