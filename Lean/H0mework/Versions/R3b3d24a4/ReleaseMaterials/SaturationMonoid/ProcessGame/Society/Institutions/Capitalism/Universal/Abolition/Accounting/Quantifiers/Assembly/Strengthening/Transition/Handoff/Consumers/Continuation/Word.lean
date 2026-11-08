import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Material

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch Actual

noncomputable section

structure InstalledAt (cut : C) (periods : Nat) : Prop where
  originalInput : cut.native.input = input
  raw : cut.raw = materialAt periods
  ready : ¬ Public.Inquiry.HasWork cut.native.frame cut.native.actual.actual
  reader : AdvanceReader cut
  phase : cut.control.phase = .renewal period
  review : cut.control.review = none

theorem start_is_installed : InstalledAt start 0 :=
  ⟨start_input, start_raw.trans material_starts_at_the_paid_handoff.symm, start_ready, start_reader,
    start_control.1, start_control.2⟩

def advanceChoice (cut : C) :=
  Evolving.Epoch.select (Public.Scope.checkInput cut.native.input)
    (Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count)
    cut.raw cut.members cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit
    cut.control .advance

theorem the_reader_selects_its_paid_renewal (cut : C) (periods : Nat) (installed : InstalledAt cut periods) :
    selectedRenewal (advanceChoice cut) = true := by
  have checks : Abolition.Review.Guarded.Checks (Public.Scope.checkInput cut.native.input)
      (Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count)
      (cut.control.atRaw cut.raw).raw cut.members period := by
    change Abolition.Review.Guarded.Checks (Public.Scope.checkInput cut.native.input) _ cut.raw cut.members period
    rw [show Public.Scope.checkInput cut.native.input = checkInput from
      congrArg Public.Scope.checkInput installed.originalInput, installed.raw]
    exact each_material_restriction_checks_the_original_period _ _ periods
  obtain ⟨guard, found⟩ := Abolition.Review.Guarded.inspect_selects_checked _ _ _ _ _ checks
  have phase : (cut.control.atRaw cut.raw).phase = .renewal period := installed.phase
  have generated : ∃ guard, Decision.compile (Public.Scope.checkInput cut.native.input)
      (Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count) cut.members
      cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit
      (cut.control.atRaw cut.raw) = .action (.renewal period phase guard) := by
    unfold Decision.compile
    split
    · rename_i seeking
      cases phase.symm.trans seeking
    · rename_i word selected
      have same := Abolition.Root.Actual.Phase.renewal.inj (selected.symm.trans phase)
      subst word
      rw [found]
      exact ⟨guard, rfl⟩
  obtain ⟨guard, chosen⟩ := generated
  unfold advanceChoice Evolving.Epoch.select
  split
  · dsimp only [Dispatch.compile]
    split
    · rename_i operation literal
      cases Decision.Outcome.action.inj (literal.symm.trans chosen)
      rfl
    · rename_i issue literal
      cases literal.symm.trans chosen
  · rename_i cursor observed
    rw [installed.review] at observed
    cases observed

private theorem original_scope_accepts (cut : C) (periods : Nat) (installed : InstalledAt cut periods) :
    Execution.PeriodChecks cut period := by
  change Abolition.Review.Guarded.Checks (Public.Scope.checkInput cut.native.input)
    (Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count) cut.raw _ period
  rw [show Public.Scope.checkInput cut.native.input = checkInput from
    congrArg Public.Scope.checkInput installed.originalInput, installed.raw]
  exact each_material_restriction_checks_the_original_period _ _ periods

open private checked_period_has_the_literal_physical_result from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

structure PaidBody (cut : C) (periods : Nat) : Prop where
  originalProposal : cut.proposal = .advance
  originalWord : cut.executionRaw = .execute period
  paid : cut.physicalResult.isAccepted = true
  inventory : cut.physicalResult.execution.items = publicLaw.rawItems (materialAt periods) period
  successor : cut.advance.raw = materialAt (periods + 1)
  phase : cut.advance.control.phase = .renewal period
  review : cut.advance.control.review = none

theorem the_original_advance_pays_its_installed_word (cut : C) (periods : Nat)
    (installed : InstalledAt cut periods) : PaidBody cut periods := by
  have proposal := an_advance_reader_submits_its_own_input cut installed.reader
  have selected := the_reader_selects_its_paid_renewal cut periods installed
  obtain ⟨word, phase, executes, _⟩ := selectedRenewal_exact _ selected
  have same := Abolition.Root.Actual.Phase.renewal.inj (phase.symm.trans installed.phase)
  subst word
  have originalWord : cut.executionRaw = .execute period := by
    unfold Current.executionRaw Current.choice
    rw [proposal]
    exact executes
  have checked := original_scope_accepts cut periods installed
  have passes := (Public.Scope.every_checked_period_executes_the_original_proposal cut.native.input
    cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast
    cut.native.actual.snapshot (.execute period) period rfl checked).1
  let before := Evolving.Epoch.Source.originalState cut.native
  let result := Physical.Public.compile cut.native.input before (.execute period)
  have physical :
      cut.physicalResult.isAccepted = result.isAccepted ∧
        cut.physicalResult.next.raw = result.next.raw ∧ cut.physicalResult.execution.items = result.execution.items := by
    unfold Current.physicalResult Public.Scope.actualResult Public.Scope.selectedCursor
    rw [originalWord, passes]
    exact ⟨rfl, rfl, rfl⟩
  have values : result.next.raw = publicLaw.next (materialAt periods) period ∧
      result.execution.items = publicLaw.rawItems (materialAt periods) period := by
    have real := checked_period_has_the_literal_physical_result cut period checked
    change result.next.raw = (Physical.Public.interpreter cut.native.input).next cut.raw period ∧
      result.execution.items = (Physical.Public.interpreter cut.native.input).rawItems cut.raw period at real
    rw [show Physical.Public.interpreter cut.native.input = publicLaw from
      congrArg Physical.Public.interpreter installed.originalInput, installed.raw] at real
    exact real
  have noneImpossible : result.execution.items ≠ [] := by
    rw [values.2]
    intro empty
    have count := congrArg List.length empty
    change ((publicLaw.execute (materialAt periods) 0 period).items).length = 0 at count
    rw [publicLaw.inventory_length] at count
    cases count
  have accepted : result.isAccepted = true := by
    dsimp only [result] at noneImpossible ⊢
    generalize computed : Physical.Public.compile cut.native.input before (.execute period) = body at noneImpossible ⊢
    cases body with
    | accepted => rfl
    | refused => exact (noneImpossible rfl).elim
    | metadata => exact (noneImpossible rfl).elim
  have paid := physical.1.trans accepted
  have wrote := congrArg (fun current : C => current.raw) (Current.advance_eq_epoch cut installed.ready)
  have changed := Transition.next_state_reads_the_same_actual_material_target cut installed.ready
  have keeps := a_paid_renewal_keeps_its_phase_and_review (advanceChoice cut) selected cut.physicalResult.next.raw
  have control : cut.afterControl.phase = .renewal period ∧ cut.afterControl.review = none := by
    unfold Current.afterControl Current.choice
    rw [proposal, paid]
    exact ⟨keeps.1.trans installed.phase, keeps.2.trans installed.review⟩
  refine ⟨proposal, originalWord, paid, physical.2.2.trans values.2,
    wrote.trans (changed.trans (physical.2.1.trans (values.1.trans (material_successor periods).symm))), ?_, ?_⟩
  · rw [Current.advance_eq_epoch _ installed.ready, Transition.next_reads_the_written_control]
    exact control.1
  · rw [Current.advance_eq_epoch _ installed.ready, Transition.next_reads_the_written_control]
    exact control.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
