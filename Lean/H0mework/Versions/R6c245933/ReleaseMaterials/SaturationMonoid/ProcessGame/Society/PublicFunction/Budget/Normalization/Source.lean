import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Legality
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Source

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)
  (input : Input source.code) (cut : Nat) (raw : List (Option source.code.Policy))

/-- Includes the original omitted suffix; it never invents a replacement fallback. -/
def term (cap horizon : Nat) : List (Option source.code.Policy) :=
  (List.range horizon).map (Normalization.schedule source.code cap (Residual.scheduleAt source cut raw))

theorem term_length (cap horizon : Nat) : (term source cut raw cap horizon).length = horizon := by
  simp only [term,List.length_map,List.length_range]

theorem each_consumed_control_is_its_normalized_raw_control (cap horizon n : Nat) (inside : n < horizon) :
    Residual.scheduleAt source cut (term source cut raw cap horizon) n =
      Normalization.schedule source.code cap (Residual.scheduleAt source cut raw) n := by
  unfold Residual.scheduleAt term
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using inside)]
  simp only [List.getElem_map,List.getElem_range,Option.getD_some]
  rfl

theorem outside_the_finite_installation_retains_the_original_control (cap horizon n : Nat)
    (later : horizon ≤ n) :
    Residual.scheduleAt source cut (term source cut raw cap horizon) n = source.feedbackPolicy (cut+n) := by
  unfold Residual.scheduleAt
  rw [List.getElem?_eq_none (by rw [term_length];omega)]
  rfl

private theorem run_agrees (cap horizon : Nat) (opponent : Opponent source.code) :
    ∀ n ≤ horizon,
      Residual.run source.code (Residual.scheduleAt source cut (term source cut raw cap horizon))
        ⟨opponent,input.budget⟩ (Residual.seed source input cut) n =
      Residual.run source.code (Normalization.schedule source.code cap (Residual.scheduleAt source cut raw))
        ⟨opponent,input.budget⟩ (Residual.seed source input cut) n := by
  intro n inside
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Residual.run]
    rw [each_consumed_control_is_its_normalized_raw_control source cut raw cap horizon n (by omega),ih (by omega)]

variable (horizon : Nat) (party : Party) (good : Good)
  (floor : Gross.Floor source.code.law party good source.code.actions) (budget : ℚ)

def Paid (opponent : Opponent source.code) : Prop :=
  Normalization.cost source.code (Residual.scheduleAt source cut raw) ⟨opponent,input.budget⟩
    (Residual.seed source input cut) horizon party good ≤ budget ∧
  ∀ n < horizon, Normalization.LawfulWork source.code (Residual.scheduleAt source cut raw n)
    ⟨opponent,input.budget⟩
    (Residual.run source.code (Residual.scheduleAt source cut raw) ⟨opponent,input.budget⟩
      (Residual.seed source input cut) n)

abbrev target (opponent : Opponent source.code) :=
  Future.target source input cut opponent (term source cut raw (floor.cap budget) horizon)

/-- The compiler is independent of the rival and the private current. -/
theorem one_public_normalization_preserves_each_rivals_actual_complete_prefix
    (opponent : Opponent source.code)
    (paid : Paid source input cut raw horizon party good budget opponent) :
    ∀ n ≤ horizon,
      (target source input cut raw horizon party good floor budget opponent).feedbackState
        (Future.takeover source input cut opponent) (cut+n) =
      (Future.target source input cut opponent raw).feedbackState (Future.takeover source input cut opponent) (cut+n) := by
  intro n inside
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state]
  exact (run_agrees source input cut raw (floor.cap budget) horizon opponent n inside).trans
    (Normalization.paid_normalization_keeps_every_adaptive_external_deviation source.code
      (Residual.scheduleAt source cut raw) ⟨opponent,input.budget⟩ (Residual.seed source input cut)
      horizon party good floor budget paid.1 paid.2 n inside)

theorem actual_submitted_words_are_preserved (opponent : Opponent source.code)
    (paid : Paid source input cut raw horizon party good budget opponent)
    (empty : source.continuation = []) (n : Nat) (inside : n < horizon) :
    ((target source input cut raw horizon party good floor budget opponent).actualExecution
      (source.history.length+1+(cut+n))).submitted =
    ((Future.target source input cut opponent raw).actualExecution
      (source.history.length+1+(cut+n))).submitted := by
  have equality := congrArg State.history
    (one_public_normalization_preserves_each_rivals_actual_complete_prefix source input cut raw horizon party good floor budget opponent paid (n+1) (by omega))
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at equality
  simp only [Residual.run,history_keeps_every_actual_word] at equality
  have prior := congrArg State.history
    (one_public_normalization_preserves_each_rivals_actual_complete_prefix source input cut raw horizon party good floor budget opponent paid n (by omega))
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at prior
  rw [prior] at equality
  rw [Future.future_word_is_actually_submitted source input cut opponent _ empty,
    Future.future_word_is_actually_submitted source input cut opponent raw empty]
  exact List.singleton_inj.mp (List.append_cancel_left equality)

def Supported : Prop := ∀ n < horizon, ∀ policy,
  Residual.scheduleAt source cut raw n = some policy → Normalization.Supported source.code policy

def menu (cap : Nat) : List (Option source.code.Policy) :=
  none :: (List.pi source.code.keys (fun _ => words source.code.actions cap)).map some

theorem the_raw_program_has_a_generated_finite_representative
    (supported : Supported source cut raw horizon) :
    term source cut raw (floor.cap budget) horizon ∈
      sequences (menu source (floor.cap budget)) horizon := by
  apply (mem_sequences_iff _ _ _).mpr
  refine ⟨by rw [term_length],?_⟩
  intro control member
  obtain ⟨n,inside,rfl⟩ := List.mem_map.mp member
  have bound := List.mem_range.mp inside
  unfold Normalization.schedule
  cases chosen : Residual.scheduleAt source cut raw n with
  | none => exact List.mem_cons_self
  | some rawPolicy =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,
      every_normalized_raw_table_is_finitely_enumerated source.code (floor.cap budget) rawPolicy
        (supported n bound rawPolicy chosen),rfl⟩)

theorem original_observed_acceptance_generates_paid_work
    (opponent : Opponent source.code) (supported : Supported source cut raw horizon)
    (affordable : Normalization.cost source.code (Residual.scheduleAt source cut raw) ⟨opponent,input.budget⟩
      (Residual.seed source input cut) horizon party good ≤ budget)
    (legal : (Residual.run source.code (Residual.scheduleAt source cut raw) ⟨opponent,input.budget⟩
      (Residual.seed source input cut) horizon).frame.localLegal = true) :
    Paid source input cut raw horizon party good budget opponent :=
  ⟨affordable,original_final_legality_generates_every_local_work_obligation source.code _ _ _ horizon supported legal⟩

private theorem future_body_at_feedback (opponent : Opponent source.code)
    (control : List (Option source.code.Policy)) (empty : source.continuation = [])
    (current : RawCurrent Party Good Technology Instrument) (n : Nat)
    (rounds : current.round = source.code.initial.round + (source.history.length+2+(cut+n))) :
    (Future.target source input cut opponent control).body current =
      word source.code (Residual.scheduleAt source cut control n) ⟨opponent,input.budget⟩
        (Residual.run source.code (Residual.scheduleAt source cut control) ⟨opponent,input.budget⟩
          (Residual.seed source input cut) n) := by
  unfold Machine.body
  rw [rounds]
  have address : source.code.initial.round + (source.history.length+2+(cut+n)) - source.code.initial.round - 1 =
      source.history.length+1+(cut+n) := by omega
  rw [address,List.getElem?_eq_none (by dsimp only [Future.target,Execution.target];omega),
    if_pos (by dsimp only [Future.target,Execution.target];omega)]
  simp only []
  rw [show source.history.length+1+(cut+n) - (Future.target source input cut opponent control).history.length - 1 = cut+n by
    change source.history.length+1+(cut+n)-source.history.length-1 = cut+n;omega]
  change (match source.continuation[cut+n]? with
    | some word => word
    | none => (Future.target source input cut opponent control).laterResponse current (cut+n)) = _
  rw [empty]
  change word source.code ((Future.target source input cut opponent control).feedbackPolicy (cut+n))
    (Future.takeover source input cut opponent)
    ((Future.target source input cut opponent control).feedbackState (Future.takeover source input cut opponent) (cut+n)) = _
  rw [Execution.policy_at,Future.the_whole_future_run_is_the_actual_state]
  have lengths (k : Nat) :
      (Residual.run source.code (Residual.scheduleAt source cut control) ⟨opponent,input.budget⟩
        (Residual.seed source input cut) k).history.length = source.history.length+1+cut+k := by
    induction k with
    | zero =>
      change (source.feedbackState input cut).history.length = _
      have earlier (j : Nat) : (source.feedbackState input j).history.length = source.history.length+1+j := by
        induction j with
        | zero => simp [Machine.feedbackState,Machine.feedbackInitial]
        | succ j ih =>
          change (advance source.code _ input _).history.length = _
          rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
          omega
      exact earlier cut
    | succ k ih =>
      change (advance source.code _ _ _).history.length = _
      rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
      omega
  simp only [word,decision,if_neg (show ¬(Residual.run source.code (Residual.scheduleAt source cut control)
    ⟨opponent,input.budget⟩ (Residual.seed source input cut) n).history.length < source.history.length+1+cut by
      rw [lengths];omega)]
  rfl

theorem every_original_source_event_is_transported (opponent : Opponent source.code)
    (paid : Paid source input cut raw horizon party good budget opponent)
    (active : source.feedback? = some input) (empty : source.continuation = [])
    (ordinal : Nat) (inside : ordinal < source.history.length+2+cut+horizon) :
    ProgrammeSource.rawEvent (target source input cut raw horizon party good floor budget opponent).input
      (ProgrammeHistory.visitAt (Future.target source input cut opponent raw).input ordinal).current =
    ProgrammeSource.rawEvent (Future.target source input cut opponent raw).input
      (ProgrammeHistory.visitAt (Future.target source input cut opponent raw).input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt (Future.target source input cut opponent raw).input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (target source input cut raw horizon party good floor budget opponent).body current =
      (Future.target source input cut opponent raw).body current
    have rounds := ProgrammeHistory.visit_round (Future.target source input cut opponent raw).input ordinal
    rw [view] at rounds
    change current.round = source.code.initial.round+ordinal at rounds
    by_cases earlier : ordinal < source.history.length+2+cut
    · exact (Future.earlier_body source input cut opponent _ active current (by omega)).trans
        (Future.earlier_body source input cut opponent raw active current (by omega)).symm
    · let n := ordinal-(source.history.length+2+cut)
      have address : ordinal = source.history.length+2+(cut+n) := by dsimp only [n];omega
      rw [future_body_at_feedback source input cut opponent _ empty current n (by omega),
        future_body_at_feedback source input cut opponent raw empty current n (by omega)]
      rw [← Future.future_word_is_actually_submitted source input cut opponent _ empty n,
        ← Future.future_word_is_actually_submitted source input cut opponent raw empty n]
      exact actual_submitted_words_are_preserved source input cut raw horizon party good floor budget opponent paid empty n (by omega)

theorem complete_native_financial_histories_are_transported (opponent : Opponent source.code)
    (paid : Paid source input cut raw horizon party good budget opponent)
    (active : source.feedback? = some input) (empty : source.continuation = [])
    (ordinal : Nat) (inside : ordinal ≤ source.history.length+2+cut+horizon) :
    Native.Coupling.Match source.code (Future.target source input cut opponent raw).input
      (target source input cut raw horizon party good floor budget opponent).input
      (Financial.accountAt (Future.target source input cut opponent raw).input ordinal)
      (Financial.accountAt (target source input cut raw horizon party good floor budget opponent).input ordinal) :=
  Native.Coupling.History.complete_accounts source.code
    (Future.target source input cut opponent raw).input
    (target source input cut raw horizon party good floor budget opponent).input rfl rfl
    (source.history.length+2+cut+horizon)
    (every_original_source_event_is_transported source input cut raw horizon party good floor budget opponent paid active empty)
    (Future.target source input cut opponent raw).body
    (target source input cut raw horizon party good floor budget opponent).body rfl rfl ordinal inside

theorem all_old_legal_successors_remain_available (opponent : Opponent source.code)
    (paid : Paid source input cut raw horizon party good budget opponent)
    (active : source.feedback? = some input) (empty : source.continuation = [])
    (ordinal : Nat) (inside : ordinal ≤ source.history.length+2+cut+horizon)
    (future : List (RawEvent Party Good Port Technology Instrument)) :
    Open.LegalHistory source.code.law ((Future.target source input cut opponent raw).currentAt ordinal) future ↔
      Open.LegalHistory source.code.law ((target source input cut raw horizon party good floor budget opponent).currentAt ordinal) future := by
  have same := Machine.actual_prefix_from_events (Future.target source input cut opponent raw).input
    (target source input cut raw horizon party good floor budget opponent).input rfl rfl
    (source.history.length+2+cut+horizon)
    (every_original_source_event_is_transported source input cut raw horizon party good floor budget opponent paid active empty) ordinal inside
  have currents : (target source input cut raw horizon party good floor budget opponent).currentAt ordinal =
      (Future.target source input cut opponent raw).currentAt ordinal := by
    change ProgrammeSource.rawCurrent _ _ = ProgrammeSource.rawCurrent _ _
    rw [same]
    cases (ProgrammeHistory.visitAt (Future.target source input cut opponent raw).input ordinal).current <;> rfl
  rw [currents]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Source
