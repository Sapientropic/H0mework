import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual.Path

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch

noncomputable section

theorem paid : Checked source proposal :=
  ⟨the_original_front_is_selected, the_front_physically_pays_the_original_word.1,
    the_installed_renewal_is_selected, the_renewal_physically_pays_the_same_word.1⟩

theorem the_same_original_root_pays_two_periods_at_clocks_five_and_six :
    source.raw.clock = 4 ∧ (migrated source proposal).raw.clock = 5 ∧
      handoffTime source proposal = 6 ∧ (completed source proposal).raw.clock = 6 ∧
      Recorded source (script source proposal) := by
  have clock : handoffTime source proposal = 6 := by
    unfold handoffTime
    rw [the_renewal_physically_pays_the_same_word.2.1]
    decide +kernel
  refine ⟨congrArg (fun raw => raw.clock) source_reads_the_paid_opening, ?_, clock,
    (the_handoff_time_is_the_completed_root_clock source proposal).trans clock,
    the_handoff_uses_one_original_ledger source proposal⟩
  rw [the_front_physically_pays_the_original_word.2.1]
  decide +kernel

theorem the_two_paid_periods_do_not_fit_the_short_window :
    ¬ handoffTime source proposal ≤ 5 := by
  rw [the_same_original_root_pays_two_periods_at_clocks_five_and_six.2.2.1]
  norm_num

theorem the_external_service_is_in_each_actual_body_inventory :
    service ∈ migration.physicalResult.execution.items.map ExecutionItem.request ∧
      service ∈ renewal.physicalResult.execution.items.map ExecutionItem.request := by
  rw [the_front_physically_pays_the_original_word.2.2, the_renewal_physically_pays_the_same_word.2.2]
  unfold RawLaw.rawItems
  rw [publicLaw.inventory_requests_exact, publicLaw.inventory_requests_exact]
  simp [period]

def emptyFront : Handoff.Proposal Bool Bool Bool Unit Unit := ⟨[], ([], period)⟩

private theorem the_original_recipient_is_still_present :
    false ∈ (migrationQuery source emptyFront).members := by
  have inherited : false ∈ Abolition.Root.Epoch.Interface.Actors.Census.parties input 0 19 0 0
      (Physical.Prefix.cursor []) := by decide +kernel
  unfold migrationQuery
  rw [no_preparation_is_needed emptyFront rfl]
  change false ∈ source.members
  exact Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
    input 0 19 0 0 [] source.native.actual.snapshot false inherited

theorem the_empty_front_cannot_skip_the_original_necessity :
    selectedMigration (migrationQuery source emptyFront).choice = false := by
  let query := migrationQuery source emptyFront
  obtain ⟨owned, raw, _⟩ := opening_route_reads_original_source emptyFront rfl
  cases selected : selectedMigration query.choice with
  | false => rfl
  | true =>
    obtain ⟨checked, _⟩ := selectedMigration_exact _ selected
    have absent : ¬ Exit.Necessity.BundlePaid (Public.Scope.checkInput query.native.input).law
        query.raw [] false ((Public.Scope.checkInput query.native.input).law.necessities query.raw false) .necessity := by
      have owned' : query.native.input = input := owned
      have raw' : query.raw = opening := raw
      rw [owned', raw']
      decide +kernel
    exact (absent (checked.1.2.1 false the_original_recipient_is_still_present).1).elim

theorem the_empty_front_returns_the_original_typed_refusal :
    inspectPath source emptyFront = .inr (.migrationRoute the_empty_front_cannot_skip_the_original_necessity) ∧
      Current.ClosedAt (migrationQuery source emptyFront) := by
  refine ⟨?_, (migrationQuery source emptyFront).the_source_generates_its_whole_ledger_actual_epoch⟩
  unfold inspectPath
  split
  · rename_i accepted
    have impossible : false = true := the_empty_front_cannot_skip_the_original_necessity.symm.trans accepted
    cases impossible
  · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
