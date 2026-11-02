import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Update

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine

open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (cut : Nat) (policy : source.code.Policy)

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem visit_succ_current
    (programme : ProgrammeSource.Input Party Good Port Technology Instrument) (ordinal : Nat) :
    (ProgrammeHistory.visitAt programme (ordinal + 1)).current =
      ProgrammeSource.next programme (ProgrammeHistory.visitAt programme ordinal).current := rfl

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem next_congr
    (original replacement : ProgrammeSource.Input Party Good Port Technology Instrument)
    (sameLaw : replacement.law = original.law) (sameInitial : replacement.initial = original.initial)
    (first second : ProgrammeSource.Current
      (Institutions.Capitalism.Universal.Source.Program.RawCurrent Party Good Technology Instrument))
    (same : second = first)
    (word : ProgrammeSource.rawEvent replacement second = ProgrammeSource.rawEvent original first) :
    ProgrammeSource.next replacement second = ProgrammeSource.next original first := by
  subst second
  cases first with
  | bootstrap => simp only [ProgrammeSource.next, sameLaw, sameInitial]
  | running current past =>
      change ProgrammeSource.Current.running (replacement.law.next current (ProgrammeSource.wordAt replacement current)) (past ++ [current]) =
        ProgrammeSource.Current.running (original.law.next current (ProgrammeSource.wordAt original current)) (past ++ [current])
      rw [sameLaw]
      exact congrArg (fun request => ProgrammeSource.Current.running (original.law.next current request) (past ++ [current])) word

omit [DecidableEq Port] [DecidableEq Technology] in
theorem actual_prefix_from_events
    (original replacement : ProgrammeSource.Input Party Good Port Technology Instrument)
    (sameLaw : replacement.law = original.law) (sameInitial : replacement.initial = original.initial)
    (limit : Nat)
    (events : ∀ ordinal, ordinal < limit →
      ProgrammeSource.rawEvent replacement (ProgrammeHistory.visitAt original ordinal).current =
        ProgrammeSource.rawEvent original (ProgrammeHistory.visitAt original ordinal).current) :
    ∀ ordinal, ordinal ≤ limit →
      (ProgrammeHistory.visitAt replacement ordinal).current = (ProgrammeHistory.visitAt original ordinal).current := by
  intro ordinal bounded
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      have prior := ih (by omega)
      have words := (congrArg (ProgrammeSource.rawEvent replacement) prior).trans (events ordinal (by omega))
      exact (visit_succ_current replacement ordinal).trans
        ((next_congr original replacement sameLaw sameInitial _ _ prior words).trans
          (visit_succ_current original ordinal).symm)

theorem scheduled_policy_keeps_each_earlier_body
    (current : Institutions.Capitalism.Universal.Source.Program.RawCurrent Party Good Technology Instrument)
    (bounded : current.round - source.code.initial.round - 1 < source.history.length + 1 + cut) :
    (source.atFeedbackCut cut policy).body current = source.body current := by
  unfold body
  dsimp only [atFeedbackCut]
  split
  · rfl
  · split
    · split
      · rfl
      · unfold laterResponse
        dsimp only [atFeedbackCut]
        split
        · rfl
        next actual active =>
          rw [source.scheduled_policy_does_not_change_other_cuts cut _ policy (by omega),
            source.scheduled_policy_keeps_the_entire_prior_state actual cut policy _ (by omega)]
    · rfl

theorem scheduled_policy_keeps_each_prior_raw_event (ordinal : Nat)
    (bounded : ordinal < source.history.length + 2 + cut) :
    ProgrammeSource.rawEvent (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt source.input ordinal).current =
      ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt source.input ordinal).current with
  | bootstrap => rfl
  | running current past =>
      change (source.atFeedbackCut cut policy).body current = source.body current
      apply source.scheduled_policy_keeps_each_earlier_body cut policy current
      have rounds := ProgrammeHistory.visit_round source.input ordinal
      rw [view] at rounds
      change current.round = source.code.initial.round + ordinal at rounds
      omega

theorem scheduled_policy_keeps_every_prior_actual_current (ordinal : Nat)
    (bounded : ordinal ≤ source.history.length + 2 + cut) :
    (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current =
      (ProgrammeHistory.visitAt source.input ordinal).current := by
  exact actual_prefix_from_events source.input (source.atFeedbackCut cut policy).input rfl rfl
    (source.history.length + 2 + cut)
    (source.scheduled_policy_keeps_each_prior_raw_event cut policy) ordinal bounded

theorem scheduled_policy_keeps_every_prior_occurrence (ordinal : Nat)
    (bounded : ordinal < source.history.length + 2 + cut) :
    (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current =
        (ProgrammeHistory.visitAt source.input ordinal).current ∧
      ProgrammeSource.rawEvent (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current =
      ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current := by
  have prior := source.scheduled_policy_keeps_every_prior_actual_current cut policy ordinal (by omega)
  exact ⟨prior, (congrArg (ProgrammeSource.rawEvent (source.atFeedbackCut cut policy).input) prior).trans
    (source.scheduled_policy_keeps_each_prior_raw_event cut policy ordinal bounded)⟩

theorem scheduled_policy_keeps_every_prior_instruction_trace (ordinal : Nat)
    (bounded : ordinal < source.history.length + 2 + cut) :
    Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems
        (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current =
      Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems source.input
        (ProgrammeHistory.visitAt source.input ordinal).current := by
  have same := source.scheduled_policy_keeps_every_prior_occurrence cut policy ordinal bounded
  exact congrArg₂ source.code.law.rawItems
    (congrArg (ProgrammeSource.rawCurrent source.input) same.1) same.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine
