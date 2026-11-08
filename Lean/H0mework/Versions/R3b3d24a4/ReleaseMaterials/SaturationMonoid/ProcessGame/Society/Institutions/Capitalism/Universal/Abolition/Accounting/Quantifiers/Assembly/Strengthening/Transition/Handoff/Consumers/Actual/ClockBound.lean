import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Clock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch

noncomputable section

open private ExactPeriodTime from H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Clock

private theorem a_paid_complete_word_on_this_source_spends_one_period
    (query : C) (word : RawEvent Bool Bool Bool Unit Unit)
    (ready : ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual)
    (owned : query.native.input = input)
    (choice : query.executionRaw = .execute word) (paid : query.physicalResult.isAccepted = true) :
    query.advance.raw.clock = query.raw.clock + 1 := by
  let root := query.native
  let cut := Evolving.Epoch.Source.originalState root
  let route := Public.Scope.executionRaw root.input root.depth root.count root.prefixLimit root.renewalLimit
    root.oldPast root.actual.snapshot (.execute word)
  have effective : route = .execute word := by
    dsimp only [route, Public.Scope.executionRaw]
    split
    · rename_i failure rejected
      have stopped := (Public.Scope.every_actual_rejection_stops_and_keeps_its_original_residual root.input
        root.depth root.count root.prefixLimit root.renewalLimit root.oldPast root.actual.snapshot
        (.execute word) failure rejected).1
      have denied := paid
      rw [Optimality.Programme.Epoch.the_epoch_physical_result_is_the_original_selected_compilation,
        choice] at denied
      change (Physical.Public.compile root.input cut route).isAccepted = true at denied
      have stoppedAt : route = .stopReview := stopped
      rw [stoppedAt] at denied
      change false = true at denied
      cases denied
    · rfl
    · rfl
  have accepted : (Physical.Public.compile root.input cut (.execute word)).isAccepted = true := by
    rw [Optimality.Programme.Epoch.the_epoch_physical_result_is_the_original_selected_compilation,
      choice] at paid
    change (Physical.Public.compile root.input cut route).isAccepted = true at paid
    rw [effective] at paid
    exact paid
  have step := Physical.Public.an_actual_complete_word_is_one_real_period_or_the_original_state root.input cut word
  unfold ExactPeriodTime at step
  rw [if_pos accepted] at step
  have duration : root.input.law.duration cut.raw = 1 := by
    change query.native.input.law.duration cut.raw = 1
    rw [owned]
    rfl
  have realClock : (Physical.Public.compile root.input cut (.execute word)).next.raw.clock =
      query.raw.clock + 1 := by
    have sameClock : cut.raw.clock = query.raw.clock := rfl
    simpa only [duration, max_eq_right (zero_le_one : (0 : ℚ) ≤ 1), sameClock] using step.1
  rw [Current.advance_eq_epoch _ ready, Transition.next_state_reads_the_same_actual_material_target,
    Optimality.Programme.Epoch.the_epoch_physical_result_is_the_original_selected_compilation, choice]
  change (Physical.Public.compile root.input cut route).next.raw.clock = _
  rw [effective]
  exact realClock

set_option maxHeartbeats 800000 in
theorem any_checked_handoff_on_the_original_source_takes_until_clock_six
    (candidate : Handoff.Proposal Bool Bool Bool Unit Unit) (checked : Checked source candidate) :
    (6 : ℚ) ≤ handoffTime source candidate := by
  let first := migrationQuery source candidate
  let second := renewalQuery source candidate
  have originalInput : source.native.input = input := rfl
  have frontInput : first.native.input = input :=
    (Execution.endAt_input source (preparedScript source candidate)).trans originalInput
  have tailInput : second.native.input = input :=
    (Execution.endAt_input (migrated source candidate) (Execution.drain (migrated source candidate))).trans
      (first.advance_parameters.1.trans frontInput)
  have firstClock := a_paid_complete_word_on_this_source_spends_one_period first candidate.pair.1
    (preparation_is_ready source candidate) frontInput (checked_migration_installs_its_original_renewal _ _ checked).1
    checked.migrationPaid
  have secondClock := a_paid_complete_word_on_this_source_spends_one_period second candidate.pair.2
    (renewal_is_ready source candidate) tailInput (checked_renewal_executes_the_same_word _ _ checked)
    checked.renewalPaid
  have material : (renewalStart source candidate).raw = (migrated source candidate).raw :=
    (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain (migrated source candidate)).2.1
  have queried := Execution.query_physical (renewalStart source candidate) (some .advance)
  have noExtraClock : second.raw.clock = first.advance.raw.clock := by
    calc
      second.raw.clock = (renewalStart source candidate).raw.clock :=
        congrArg (fun state => state.raw.clock) queried
      _ = (migrated source candidate).raw.clock := congrArg (fun (raw : Raw) => raw.clock) material
      _ = first.advance.raw.clock := rfl
  have before : source.raw.clock ≤ first.raw.clock :=
    Execution.the_actual_script_never_runs_the_clock_backwards source (preparedScript source candidate)
  have sourceClock : source.raw.clock = 4 :=
    congrArg (fun (raw : Raw) => raw.clock) source_reads_the_paid_opening
  have opening : (4 : ℚ) ≤ first.raw.clock := sourceClock ▸ before
  have elapsed : second.advance.raw.clock = (first.raw.clock + 1) + 1 :=
    secondClock.trans (congrArg (fun value => value + 1) (noExtraClock.trans firstClock))
  change (6 : ℚ) ≤ second.advance.raw.clock
  exact (by linarith only [opening] : (6 : ℚ) ≤ (first.raw.clock + 1) + 1).trans_eq elapsed.symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
