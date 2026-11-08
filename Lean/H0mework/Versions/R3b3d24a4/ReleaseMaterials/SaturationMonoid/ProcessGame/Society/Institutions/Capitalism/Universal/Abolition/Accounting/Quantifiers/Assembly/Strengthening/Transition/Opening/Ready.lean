import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation
open Financial.Installation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem inherited_row_has_no_instruction (current : (ProgrammeSource.V input).Current) :
    Registered.originalInstruction input ⟨ProgrammeSource.emitted input current, rfl⟩
      (ProgrammeSource.sourceEntry input current .inherited) = none := by
  cases current with
  | bootstrap => rfl
  | running state past =>
    cases emission : input.emission? with
    | none => exact Registered.originalInstruction_running_fixed input state past .inherited emission
    | some emit => exact Registered.originalInstruction_generated_none input _ _ emit emission

private theorem original_admin_position_keeps_account (cursor : Cursor.State input)
    (atFirst : cursor.position = 0) :
    (Cursor.next input cursor).account = cursor.account := by
  let visit := Cursor.originalVisit input cursor
  let origin := Financial.originAt input visit (0 : Fin (ProgrammeSource.registrationSize input + 2))
  have item : Cursor.originalItem? input cursor = some origin := by
    unfold Cursor.originalItem?
    rw [atFirst]
    change (Financial.inventoryAt input visit)[0]? = some origin
    cases emission : input.emission? with
    | none => simp [Financial.inventoryAt, Financial.administrativeInventoryAt, emission, origin]
    | some emit =>
      rw [Financial.inventoryAt, emission, List.getElem?_append_left]
      · simp [Financial.administrativeInventoryAt, origin]
      · simp [Financial.administrativeInventoryAt]
  have inert : origin.instruction? input = none := by
    change Registered.originalInstruction input ⟨ProgrammeSource.emitted input visit.current, rfl⟩
      (ProgrammeSource.sourceEntry input visit.current .inherited) = none
    exact inherited_row_has_no_instruction input visit.current
  change (Cursor.action input cursor).next input cursor.account = cursor.account
  cases phase : cursor.phase with
  | entering => simp only [Cursor.action, phase, Action.next]
  | accounting =>
    simp only [Cursor.action, phase, item]
    rw [sourceAction_is_actual_consumer]
    exact Financial.BalanceConservation.consume_without_instruction input origin cursor.account inert

theorem the_original_next_reads_the_same_opening_GS (depth start : Nat) :
    (Cursor.next input (Runtime.cursorAt input depth (cut input depth start))).account =
      originalAccount input depth start := by
  apply original_admin_position_keeps_account
  rcases (PendingDrain.drain input depth start).stoppedBeforeFresh with entering | ready
  · rw [Runtime.cursorAt_accounting input depth _] at entering
    cases entering
  · exact ready.1

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening
