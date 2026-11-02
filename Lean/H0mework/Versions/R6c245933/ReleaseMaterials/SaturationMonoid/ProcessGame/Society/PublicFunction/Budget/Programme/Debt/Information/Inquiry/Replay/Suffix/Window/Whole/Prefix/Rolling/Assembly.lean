import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Source

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Assembly
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {reference : Program model.source.code (horizon domain)}

theorem advance_keeps_the_entire_committed_prefix (work : Work model domain original reference) :
    work.past <+: (advance work).past := by
  by_cases inside : work.past.length < horizon domain
  · rw [advance_really_commits_only_the_current_stage work inside]
    exact List.prefix_append _ _
  · rw [advance_at_the_full_window_is_identity work (Nat.le_antisymm work.bounded (Nat.le_of_not_gt inside))]

theorem every_generated_cut_is_a_prefix_of_every_later_cut
    (work : Work model domain original reference) (n m : Nat) (earlier : n ≤ m) :
    (run work n).past <+: (run work m).past := by
  induction m with
  | zero =>
      have same : n = 0 := by omega
      subst n
      exact List.prefix_refl _
  | succ m ih =>
      by_cases same : n = m+1
      · subst n;exact List.prefix_refl _
      · exact (ih (by omega)).trans (advance_keeps_the_entire_committed_prefix (run work m))

variable (work : Work model domain original reference) (actual : Cursor model.source.code)
  (rival : Opponent model.source.code)

abbrev cutPoint (n : Nat) := Splice.install actual rival (run work n).past
abbrev full := cutPoint work actual rival (horizon domain)
abbrev bound := Replanning.native model (full work actual rival)
abbrev facade := Native.AuthorityRuntime.facade (bound work actual rival)
abbrev activated (n : Nat) := Inquiry.Runtime.readState (bound work actual rival) (depth (cutPoint work actual rival n))

theorem the_fixed_source_is_generated_by_extending_each_actual_prefix
    (n : Nat) (inside : n ≤ horizon domain) :
    ∃ suffix : List (Prefix.Rule model.source.code),
      full work actual rival = Splice.install (cutPoint work actual rival n) rival suffix := by
  obtain ⟨suffix,same⟩ := every_generated_cut_is_a_prefix_of_every_later_cut work n (horizon domain) inside
  refine ⟨suffix,?_⟩
  change Splice.install actual rival (run work (horizon domain)).past = _
  rw [←same]
  exact List.foldl_append

theorem every_actual_prefix_has_the_same_occurrences_in_the_fixed_source
    (n : Nat) (inside : n ≤ horizon domain) (ordinal : Nat)
    (earlier : ordinal < arrival (cutPoint work actual rival n)) :
    (ProgrammeHistory.visitAt (full work actual rival).source.input ordinal).current =
      (ProgrammeHistory.visitAt (cutPoint work actual rival n).source.input ordinal).current ∧
      ProgrammeSource.rawEvent (full work actual rival).source.input
        (ProgrammeHistory.visitAt (full work actual rival).source.input ordinal).current =
      ProgrammeSource.rawEvent (cutPoint work actual rival n).source.input
        (ProgrammeHistory.visitAt (cutPoint work actual rival n).source.input ordinal).current := by
  obtain ⟨suffix,same⟩ := the_fixed_source_is_generated_by_extending_each_actual_prefix work actual rival n inside
  rw [same]
  exact Native.Coupling.History.occurrences (cutPoint work actual rival n).source.input
    (Splice.install (cutPoint work actual rival n) rival suffix).source.input rfl rfl
    (arrival (cutPoint work actual rival n))
    (Installation.Chain.fold_keeps_every_prior_raw_event (model := model) (cutPoint work actual rival n) rival suffix) ordinal earlier

theorem every_cut_endpoint_is_the_same_actual_visit_in_the_fixed_source
    (n : Nat) (inside : n ≤ horizon domain) :
    (ProgrammeHistory.visitAt (full work actual rival).source.input (arrival (cutPoint work actual rival n))).current =
      (ProgrammeHistory.visitAt (cutPoint work actual rival n).source.input (arrival (cutPoint work actual rival n))).current := by
  obtain ⟨suffix,same⟩ := the_fixed_source_is_generated_by_extending_each_actual_prefix work actual rival n inside
  rw [same]
  exact Machine.actual_prefix_from_events (cutPoint work actual rival n).source.input
    (Splice.install (cutPoint work actual rival n) rival suffix).source.input rfl rfl
    (arrival (cutPoint work actual rival n))
    (Installation.Chain.fold_keeps_every_prior_raw_event (model := model) (cutPoint work actual rival n) rival suffix)
    _ (Nat.le_refl _)

theorem every_actual_prefix_keeps_its_complete_native_account_in_the_fixed_source
    (n : Nat) (inside : n ≤ horizon domain) (ordinal : Nat)
    (earlier : ordinal ≤ arrival (cutPoint work actual rival n)) :
    Native.Coupling.Match model.source.code (cutPoint work actual rival n).source.input
      (full work actual rival).source.input
      (Financial.accountAt (cutPoint work actual rival n).source.input ordinal)
      (Financial.accountAt (full work actual rival).source.input ordinal) := by
  obtain ⟨suffix,same⟩ := the_fixed_source_is_generated_by_extending_each_actual_prefix work actual rival n inside
  rw [same]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) _ rival suffix ordinal earlier

theorem each_live_cut_really_increments_the_actual_source_clock
    (n : Nat) (inside : (run work n).past.length < horizon domain) :
    depth (cutPoint work actual rival (n+1)) = depth (cutPoint work actual rival n)+1 := by
  change depth (Splice.install actual rival (advance (run work n)).past) = _
  rw [advance_really_commits_only_the_current_stage _ inside]
  unfold Splice.install
  rw [List.foldl_append]
  rfl

theorem the_one_original_root_installs_the_next_actual_cut
    (n : Nat) (inside : (run work n).past.length < horizon domain) :
    (activated work actual rival n).tick.nextCurrent = (activated work actual rival (n+1)).current := by
  have rooted := (facade work actual rival).readoutAt_factorizes (activated work actual rival n) .responsibilities
  apply rooted.2.2.2.2.trans
  change (facade work actual rival).process.stateAt (Nat.succ (activated work actual rival n).state) =
    (facade work actual rival).process.stateAt (activated work actual rival (n+1)).state
  congr 1
  rw [Inquiry.Runtime.readState_state,Inquiry.Runtime.readState_state,
    each_live_cut_really_increments_the_actual_source_clock work actual rival n inside]

theorem the_fixed_original_root_consumes_every_actual_prefix_and_its_own_next
    (n : Nat) (inside : n ≤ horizon domain) :
    let currentRoot := activated work actual rival n
    (∀ ordinal < arrival (cutPoint work actual rival n),
      (ProgrammeHistory.visitAt (full work actual rival).source.input ordinal).current =
        (ProgrammeHistory.visitAt (cutPoint work actual rival n).source.input ordinal).current) ∧
      (∀ ordinal ≤ arrival (cutPoint work actual rival n),
        Native.Coupling.Match model.source.code (cutPoint work actual rival n).source.input (full work actual rival).source.input
          (Financial.accountAt (cutPoint work actual rival n).source.input ordinal)
          (Financial.accountAt (full work actual rival).source.input ordinal)) ∧
      HEq ((facade work actual rival).readoutAt currentRoot .responsibilities)
        (currentRoot.tick.generated.projectionOutcome (.component ())) ∧
      HEq currentRoot.tick.generated.wholeLedgerWriteBack
        (currentRoot.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentRoot.current.visit.current) ∧
      ((run work n).past.length < horizon domain →
        currentRoot.tick.nextCurrent = (activated work actual rival (n+1)).current) := by
  let currentRoot := activated work actual rival n
  have rooted := (facade work actual rival).readoutAt_factorizes currentRoot .responsibilities
  exact ⟨fun ordinal earlier => (every_actual_prefix_has_the_same_occurrences_in_the_fixed_source work actual rival n inside ordinal earlier).1,
    every_actual_prefix_keeps_its_complete_native_account_in_the_fixed_source work actual rival n inside,
    rooted.2.2.2.1,rooted.2.2.1,the_one_original_root_installs_the_next_actual_cut work actual rival n⟩

namespace Source

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (budget : Nat) (published : List (Prefix.Rule model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon (Rolling.Source.domain model budget published)))
  (world : Distributed.Recall.Information.World model budget) (pastOpponent rival : Opponent model.source.code)

abbrev prepared := Rolling.Source.prepared model budget published original reference
abbrev sourceView := Rolling.Source.actual model budget published world pastOpponent

def deployment : Cursor model.source.code :=
  match prepared model budget published original reference with
  | .ready work => full work (sourceView model budget published world pastOpponent).point rival
  | .blocked _ => (sourceView model budget published world pastOpponent).point

abbrev bound := Replanning.native model (deployment model budget published original reference world pastOpponent rival)
abbrev facade := Native.AuthorityRuntime.facade (bound model budget published original reference world pastOpponent rival)
abbrev activated (n : Nat) := Inquiry.Runtime.readState (bound model budget published original reference world pastOpponent rival)
  (depth (Rolling.Source.deployment model budget published original reference world pastOpponent rival n))

def Continuation : Start model (Rolling.Source.domain model budget published) original reference → Prop
  | .blocked _ => True
  | .ready work => ∀ n ≤ horizon (Rolling.Source.domain model budget published),
      (ProgrammeHistory.visitAt (deployment model budget published original reference world pastOpponent rival).source.input
        (arrival (cutPoint work (sourceView model budget published world pastOpponent).point rival n))).current =
        (ProgrammeHistory.visitAt (cutPoint work (sourceView model budget published world pastOpponent).point rival n).source.input
          (arrival (cutPoint work (sourceView model budget published world pastOpponent).point rival n))).current ∧
      (∀ ordinal ≤ arrival (cutPoint work (sourceView model budget published world pastOpponent).point rival n),
        Native.Coupling.Match model.source.code
          (cutPoint work (sourceView model budget published world pastOpponent).point rival n).source.input
          (deployment model budget published original reference world pastOpponent rival).source.input
          (Financial.accountAt (cutPoint work (sourceView model budget published world pastOpponent).point rival n).source.input ordinal)
          (Financial.accountAt (deployment model budget published original reference world pastOpponent rival).source.input ordinal)) ∧
      ((run work n).past.length < horizon (Rolling.Source.domain model budget published) →
        (activated model budget published original reference world pastOpponent rival n).tick.nextCurrent =
          (activated model budget published original reference world pastOpponent rival (n+1)).current)

theorem every_publicly_generated_plan_reenters_one_original_root_with_its_actual_next_cut :
    Rolling.Source.Protection model budget published original reference world pastOpponent rival
      (prepared model budget published original reference) ∧
      Continuation model budget published original reference world pastOpponent rival
        (prepared model budget published original reference) ∧
      (∀ n : Nat,
        let currentRoot := activated model budget published original reference world pastOpponent rival n
        HEq ((facade model budget published original reference world pastOpponent rival).readoutAt currentRoot .responsibilities)
          (currentRoot.tick.generated.projectionOutcome (.component ())) ∧
        HEq currentRoot.tick.generated.wholeLedgerWriteBack
          (currentRoot.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentRoot.current.visit.current)) := by
  refine ⟨(Rolling.Source.every_original_source_cut_generates_its_global_comparison_paid_chain_knowledge_and_own_next
    model budget published original reference world pastOpponent rival 0).1,?_,?_⟩
  · cases generated : prepared model budget published original reference with
    | blocked rejected => trivial
    | ready work =>
        intro n inside
        have installed : deployment model budget published original reference world pastOpponent rival =
            full work (sourceView model budget published world pastOpponent).point rival := by
          unfold deployment
          rw [generated]
        refine ⟨?_,?_,?_⟩
        · rw [installed]
          exact every_cut_endpoint_is_the_same_actual_visit_in_the_fixed_source work _ rival n inside
        · rw [installed]
          exact every_actual_prefix_keeps_its_complete_native_account_in_the_fixed_source work _ rival n inside
        · intro live
          unfold activated bound
          rw [installed]
          unfold Rolling.Source.deployment
          change Rolling.Source.prepared model budget published original reference = .ready work at generated
          rw [generated]
          exact the_one_original_root_installs_the_next_actual_cut work _ rival n live
  · intro n
    have rooted := (facade model budget published original reference world pastOpponent rival).readoutAt_factorizes
      (activated model budget published original reference world pastOpponent rival n) .responsibilities
    exact ⟨rooted.2.2.2.1,rooted.2.2.1⟩

end Source

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Assembly
