import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual.Material

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolving.Epoch Quantities

noncomputable section

abbrev C := Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)

theorem no_preparation_is_needed (candidate : Handoff.Proposal Bool Bool Bool Unit Unit)
    (empty : candidate.preparation = []) :
    prepared source candidate = source := by
  have zero : Execution.remainingNative source = 0 := Nat.eq_zero_of_not_pos
    (fun active => source_is_ready ((Execution.pending_iff_positive_original_positions source).mpr active))
  unfold prepared preparedScript
  rw [empty]
  change Execution.endAt source (Execution.drain source) = source
  unfold Execution.drain Execution.nativePayments
  rw [zero]
  rfl

theorem opening_route_reads_original_source (candidate : Handoff.Proposal Bool Bool Bool Unit Unit)
    (empty : candidate.preparation = []) :
    (migrationQuery source candidate).native.input = input ∧
      (migrationQuery source candidate).raw = opening ∧
      (migrationQuery source candidate).control.review = none := by
  have same := no_preparation_is_needed candidate empty
  refine ⟨?_, ?_, ?_⟩
  · change (prepared source candidate).native.input = input
    rw [same]
    rfl
  · change (prepared source candidate).raw = opening
    rw [same]
    exact source_reads_the_paid_opening
  · unfold migrationQuery
    rw [same]
    exact congrArg (fun control => control.review)
      (source.requery_keeps_control_and_complete_account (fun _ _ => .migrate candidate.pair)).1

abbrev migration := migrationQuery source proposal
abbrev renewal := renewalQuery source proposal

theorem the_original_front_is_selected : selectedMigration migration.choice = true := by
  obtain ⟨owned, raw, noReview⟩ := opening_route_reads_original_source proposal rfl
  have admits : Abolition.Root.Actual.Migration.Checks (Public.Scope.checkInput migration.native.input)
      (Abolition.Root.Actual.origin migration.native.input migration.native.depth migration.native.count)
      migration.raw migration.members proposal.pair := by
    rw [owned, raw]
    exact original_migration_checks _ _
  obtain ⟨checked, found⟩ := Abolition.Root.Actual.Migration.inspect_selects_every_checked_pair _ _ _ _ _ admits
  unfold Current.choice Evolving.Epoch.select
  split
  · change selectedMigration (.ordinary (Dispatch.compile _ _ _ _ _ _ _ _ (.migrate proposal.pair))) = _
    dsimp only [Dispatch.compile, Control.atRaw]
    rw [found]
    rfl
  · rename_i cursor someReview
    rw [noReview] at someReview
    cases someReview

theorem the_selected_front_is_the_original_word : migration.executionRaw = .execute period := by
  obtain ⟨checked, picked⟩ := selectedMigration_exact _ the_original_front_is_selected
  unfold Current.executionRaw
  rw [picked]
  rfl

private theorem the_forwarded_period_is_a_real_body (query : C)
    (ready : ¬ Pending query) (owned : query.native.input = input)
    (raw : query.raw = opening ∨ query.raw = firstRaw) (runs : query.executionRaw = .execute period) :
    query.physicalResult.isAccepted = true ∧
      query.advance.raw = publicLaw.next query.raw period ∧
      query.physicalResult.execution.items = publicLaw.rawItems query.raw period := by
  have guarded : Execution.PeriodChecks query period := by
    change Abolition.Review.Guarded.Checks (Public.Scope.checkInput query.native.input)
      (Abolition.Root.Actual.origin query.native.input query.native.depth query.native.count)
      query.raw _ period
    rw [show Public.Scope.checkInput query.native.input = checkInput from congrArg Public.Scope.checkInput owned]
    exact original_guard _ query.raw _ raw
  have forwards := (Public.Scope.every_checked_period_executes_the_original_proposal query.native.input
    query.native.depth query.native.count query.native.prefixLimit query.native.renewalLimit query.native.oldPast
    query.native.actual.snapshot (.execute period) period rfl guarded).1
  let cut := Evolving.Epoch.Source.originalState query.native
  let result := Physical.Public.compile query.native.input cut (.execute period)
  have sameResult : query.physicalResult.isAccepted = result.isAccepted ∧
      query.physicalResult.next.raw = result.next.raw ∧
      query.physicalResult.execution.items = result.execution.items := by
    unfold Current.physicalResult Public.Scope.actualResult Public.Scope.selectedCursor
    rw [runs, forwards]
    exact ⟨rfl, rfl, rfl⟩
  have valid : ∀ item ∈ (Physical.Public.interpreter query.native.input).rawItems query.raw period,
      (Physical.Public.interpreter query.native.input).Valid item.before item.request :=
    fun item present => (guarded.2.2.1 item present).1
  have values : result.isAccepted = true ∧
      result.next.raw = (Physical.Public.interpreter query.native.input).next query.raw period ∧
      result.execution.items = (Physical.Public.interpreter query.native.input).rawItems query.raw period := by
    dsimp only [result]
    cases Physical.Public.compile query.native.input cut (.execute period) with
    | accepted actual selected _ =>
      have exactWord : actual = period := Option.some.inj (selected.symm.trans rfl)
      subst actual
      exact ⟨rfl, rfl, rfl⟩
    | refused actual selected item listed rejected =>
      have exactWord : actual = period := Option.some.inj (selected.symm.trans rfl)
      subst actual
      exact (rejected (valid item listed)).elim
    | metadata selected => cases selected
  rw [show Physical.Public.interpreter query.native.input = publicLaw from
    congrArg Physical.Public.interpreter owned] at values
  have step := Transition.next_state_reads_the_same_actual_material_target query ready
  have stepAt := congrArg Current.raw (Current.advance_eq_epoch query ready)
  exact ⟨sameResult.1.trans values.1, stepAt.trans (step.trans (sameResult.2.1.trans values.2.1)),
    sameResult.2.2.trans values.2.2⟩

theorem the_front_physically_pays_the_original_word :
    migration.physicalResult.isAccepted = true ∧
      (migrated source proposal).raw = firstRaw ∧
      migration.physicalResult.execution.items = publicLaw.rawItems opening period := by
  obtain ⟨owned, raw, _⟩ := opening_route_reads_original_source proposal rfl
  have actual := the_forwarded_period_is_a_real_body migration (preparation_is_ready source proposal)
    owned (Or.inl raw) the_selected_front_is_the_original_word
  rw [raw] at actual
  exact actual

/- open private drain_preserves_control from SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Routing -/

theorem the_paid_front_installs_the_same_renewal :
    renewal.control.phase = .renewal period ∧ renewal.control.review = none := by
  obtain ⟨checked, picked⟩ := selectedMigration_exact _ the_original_front_is_selected
  have ready : ¬ Public.Inquiry.HasWork migration.native.frame migration.native.actual.actual :=
    preparation_is_ready source proposal
  have queried := ((renewalStart source proposal).requery_keeps_control_and_complete_account
    (fun _ _ => .advance)).1
  change renewal.control = (renewalStart source proposal).control at queried
  rw [queried, renewalStart, drain_preserves_control, migrated, Current.advance_eq_epoch _ ready,
    Transition.next_reads_the_written_control]
  unfold Current.afterControl
  rw [picked, the_front_physically_pays_the_original_word.1]
  exact ⟨rfl, rfl⟩

theorem renewal_reads_the_paid_front :
    renewal.native.input = input ∧ renewal.raw = firstRaw := by
  obtain ⟨owned, _, _⟩ := opening_route_reads_original_source proposal rfl
  have kept := Execution.endAt_input (migrated source proposal) (Execution.drain (migrated source proposal))
  have drained := (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain
    (migrated source proposal)).2.1
  exact ⟨kept.trans (migration.advance_parameters.1.trans owned),
    drained.trans the_front_physically_pays_the_original_word.2.1⟩

theorem the_installed_renewal_is_selected : selectedRenewal renewal.choice = true := by
  obtain ⟨owned, raw⟩ := renewal_reads_the_paid_front
  obtain ⟨phase, noReview⟩ := the_paid_front_installs_the_same_renewal
  have checked : Abolition.Review.Guarded.Checks (Public.Scope.checkInput renewal.native.input)
      (Abolition.Root.Actual.origin renewal.native.input renewal.native.depth renewal.native.count)
      renewal.raw renewal.members period := by
    rw [owned, raw]
    exact original_guard _ firstRaw _ (Or.inr rfl)
  obtain ⟨proof, found⟩ := Abolition.Review.Guarded.inspect_selects_checked _ _ _ _ _ checked
  have checkedAt : Abolition.Review.Guarded.inspect (Public.Scope.checkInput renewal.native.input)
      (Abolition.Root.Actual.origin renewal.native.input renewal.native.depth renewal.native.count)
      (renewal.control.atRaw renewal.raw).raw renewal.members period = .accepted proof := found
  have atPhase : (renewal.control.atRaw renewal.raw).phase = .renewal period := phase
  have decided : ∃ guard, Decision.compile (Public.Scope.checkInput renewal.native.input)
      (Abolition.Root.Actual.origin renewal.native.input renewal.native.depth renewal.native.count)
      renewal.members renewal.native.depth renewal.native.count renewal.native.prefixLimit renewal.native.renewalLimit
      (renewal.control.atRaw renewal.raw) = .action (.renewal period phase guard) := by
    unfold Decision.compile
    split
    · rename_i seeking
      cases atPhase.symm.trans seeking
    · rename_i word route
      have exactWord := Abolition.Root.Actual.Phase.renewal.inj (route.symm.trans atPhase)
      subst word
      rw [checkedAt]
      exact ⟨proof, rfl⟩
  obtain ⟨guard, chosen⟩ := decided
  unfold Current.choice Evolving.Epoch.select
  split
  · change selectedRenewal (.ordinary (Dispatch.compile _ _ _ _ _ _ _ _ .advance)) = _
    dsimp only [Dispatch.compile]
    split
    · rename_i operation literal
      cases Decision.Outcome.action.inj (literal.symm.trans chosen)
      rfl
    · rename_i issue literal
      cases literal.symm.trans chosen
  · rename_i cursor present
    rw [noReview] at present
    cases present

theorem the_renewal_physically_pays_the_same_word :
    renewal.physicalResult.isAccepted = true ∧
      (renewed source proposal).raw = secondRaw ∧
      renewal.physicalResult.execution.items = publicLaw.rawItems firstRaw period := by
  obtain ⟨owned, raw⟩ := renewal_reads_the_paid_front
  obtain ⟨word, phase, runs, _⟩ := selectedRenewal_exact _ the_installed_renewal_is_selected
  have same := Abolition.Root.Actual.Phase.renewal.inj (phase.symm.trans the_paid_front_installs_the_same_renewal.1)
  cases same
  have actual := the_forwarded_period_is_a_real_body renewal (renewal_is_ready source proposal)
    owned (Or.inr raw) runs
  rw [raw] at actual
  exact actual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
