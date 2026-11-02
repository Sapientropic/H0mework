import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReviewHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReviewRun

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

abbrev Stages := List (EventHistory.Stage (code := model.source.code))
abbrev fuel (past : Stages model) := (EventStep.seed (NativeReview.current model start past)).remaining
abbrev waiting (past : Stages model) := past ++ [(SilentWindow.quiet, OriginQueue.environment start)]
abbrev attempted (past : Stages model) (ready : NativeReview.Ready model start past) :=
  NativeReviewHistory.full model start past ready (OriginQueue.environment start)

inductive Status where
  | nativeComplete | paid | refused | exhausted | observationCut
  deriving DecidableEq

structure Result where
  stages : Stages model
  status : Status
  waits : Nat

-- Recheck the actual successor after each original scheduling turn. A paid attempt is not completion.
def run : Nat → Stages model → Result model
  | 0, past =>
    if NativeReview.complete model start past then ⟨past, .nativeComplete, 0⟩
    else if fuel model start past = 0 then ⟨past, .exhausted, 0⟩ else ⟨past, .observationCut, 0⟩
  | rounds + 1, past =>
    match NativeReview.produce model start past with
    | .clear _ => ⟨past, .nativeComplete, 0⟩
    | .paid ready _ => ⟨attempted model start past ready, .paid, 0⟩
    | .refused ready _ => ⟨attempted model start past ready, .refused, 0⟩
    | _ =>
      if fuel model start past = 0 then ⟨past, .exhausted, 0⟩ else
      let next := run rounds (waiting model start past)
      ⟨next.stages, next.status, next.waits + 1⟩

def produce (past : Stages model) := run model start (fuel model start past) past

theorem every_run_preserves_the_whole_actual_history (rounds : Nat) (past : Stages model) :
    past <+: (run model start rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run]; split <;> first | exact List.prefix_refl _ | split <;> exact List.prefix_refl _
  | succ rounds ih =>
    cases observed : NativeReview.produce model start past <;> simp only [run, observed]
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)
    · split
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)
    · exact List.prefix_append _ _
    · exact List.prefix_append _ _

theorem a_complete_status_requires_the_actual_native_inventory (rounds : Nat) (past : Stages model)
    (closed : (run model start rounds past).status = .nativeComplete) :
    NativeReview.complete model start (run model start rounds past).stages = true := by
  induction rounds generalizing past with
  | zero => simp only [run] at closed ⊢; (split_ifs at closed ⊢; simp_all)
  | succ rounds ih =>
    cases observed : NativeReview.produce model start past <;> simp only [run, observed] at closed ⊢
    · assumption
    · by_cases empty : fuel model start past = 0
      · simp only [if_pos empty] at closed
        cases closed
      · simp only [if_neg empty] at closed ⊢
        exact ih _ closed
    · by_cases empty : fuel model start past = 0
      · simp only [if_pos empty] at closed
        cases closed
      · simp only [if_neg empty] at closed ⊢
        exact ih _ closed
    · contradiction
    · contradiction

theorem an_exhausted_status_requires_zero_actual_fuel (rounds : Nat) (past : Stages model)
    (empty : (run model start rounds past).status = .exhausted) :
    fuel model start (run model start rounds past).stages = 0 := by
  induction rounds generalizing past with
  | zero => simp only [run] at empty ⊢; (split_ifs at empty ⊢; simp_all)
  | succ rounds ih =>
    cases observed : NativeReview.produce model start past <;> simp only [run, observed] at empty ⊢
    · contradiction
    · by_cases zero : fuel model start past = 0
      · simpa only [if_pos zero] using zero
      · simp only [if_neg zero] at empty ⊢
        exact ih _ empty
    · by_cases zero : fuel model start past = 0
      · simpa only [if_pos zero] using zero
      · simp only [if_neg zero] at empty ⊢
        exact ih _ empty
    · contradiction
    · contradiction

theorem source_budget_excludes_an_observation_cut (rounds : Nat) (past : Stages model)
    (enough : fuel model start past ≤ rounds) : (run model start rounds past).status ≠ .observationCut := by
  induction rounds generalizing past with
  | zero =>
    simp only [run]
    split
    · intro same; cases same
    · rw [if_pos (by omega)]
      intro same; cases same
  | succ rounds ih =>
    cases observed : NativeReview.produce model start past <;> simp only [run, observed]
    · intro same; cases same
    · split
      · intro same; cases same
      · apply ih
        have spent := UnifiedResponse.fuel_after_actual_extension model start past [(SilentWindow.quiet, OriginQueue.environment start)]
        change fuel model start (waiting model start past) = fuel model start past - 1 at spent
        omega
    · split
      · intro same; cases same
      · apply ih
        have spent := UnifiedResponse.fuel_after_actual_extension model start past [(SilentWindow.quiet, OriginQueue.environment start)]
        change fuel model start (waiting model start past) = fuel model start past - 1 at spent
        omega
    · intro same; cases same
    · intro same; cases same

def PaidAt (origin final : Stages model) : Prop :=
  ∃ (prior : Stages model) (ready : NativeReview.Ready model start prior)
    (accepted : model.source.code.law.Valid (EventStep.seed (NativeReview.current model start prior)).current
      (NativeReview.action model start prior ready.receiver)),
    origin <+: prior ∧ NativeReview.produce model start prior = .paid ready accepted ∧
      final = attempted model start prior ready

theorem a_paid_status_contains_the_actual_selected_attempt (rounds : Nat) (past : Stages model)
    (paid : (run model start rounds past).status = .paid) :
    PaidAt model start past (run model start rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at paid; (split_ifs at paid)
  | succ rounds ih =>
    cases observed : NativeReview.produce model start past <;> simp only [run, observed] at paid ⊢
    · contradiction
    · by_cases empty : fuel model start past = 0
      · simp only [if_pos empty] at paid
        cases paid
      · simp only [if_neg empty] at paid ⊢
        obtain ⟨prior, ready, accepted, priorPrefix, selected, actual⟩ := ih _ paid
        exact ⟨prior, ready, accepted, (List.prefix_append _ _).trans priorPrefix, selected, actual⟩
    · by_cases empty : fuel model start past = 0
      · simp only [if_pos empty] at paid
        cases paid
      · simp only [if_neg empty] at paid ⊢
        obtain ⟨prior, ready, accepted, priorPrefix, selected, actual⟩ := ih _ paid
        exact ⟨prior, ready, accepted, (List.prefix_append _ _).trans priorPrefix, selected, actual⟩
    · exact ⟨past, _, _, List.prefix_refl _, observed, rfl⟩
    · contradiction

def RefusedAt (origin final : Stages model) : Prop :=
  ∃ (prior : Stages model) (ready : NativeReview.Ready model start prior)
    (accepted : ¬ model.source.code.law.Valid (EventStep.seed (NativeReview.current model start prior)).current
      (NativeReview.action model start prior ready.receiver)),
    origin <+: prior ∧ NativeReview.produce model start prior = .refused ready accepted ∧
      final = attempted model start prior ready

theorem a_refused_status_contains_the_actual_selected_attempt (rounds : Nat) (past : Stages model)
    (paid : (run model start rounds past).status = .refused) :
    RefusedAt model start past (run model start rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at paid; (split_ifs at paid)
  | succ rounds ih =>
    cases observed : NativeReview.produce model start past <;> simp only [run, observed] at paid ⊢
    · contradiction
    · by_cases empty : fuel model start past = 0
      · simp only [if_pos empty] at paid
        cases paid
      · simp only [if_neg empty] at paid ⊢
        obtain ⟨prior, ready, accepted, priorPrefix, selected, actual⟩ := ih _ paid
        exact ⟨prior, ready, accepted, (List.prefix_append _ _).trans priorPrefix, selected, actual⟩
    · by_cases empty : fuel model start past = 0
      · simp only [if_pos empty] at paid
        cases paid
      · simp only [if_neg empty] at paid ⊢
        obtain ⟨prior, ready, accepted, priorPrefix, selected, actual⟩ := ih _ paid
        exact ⟨prior, ready, accepted, (List.prefix_append _ _).trans priorPrefix, selected, actual⟩
    · contradiction
    · exact ⟨past, _, _, List.prefix_refl _, observed, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReviewRun
