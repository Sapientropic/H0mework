import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Quantities Evolving.Epoch Actual

noncomputable section

/-- The continuation begins at the committed handoff, after its original
native queue has been paid. -/
abbrev start : C := completed source proposal

theorem start_raw : start.raw = secondRaw := by
  unfold start
  rw [end_is_the_original_renewal_and_its_accounting,
    (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain _).2.1]
  exact the_renewal_physically_pays_the_same_word.2.1

theorem start_input : start.native.input = input :=
  Execution.endAt_input source (script source proposal)

theorem start_ready : ¬ Pending start := by
  unfold start
  rw [end_is_the_original_renewal_and_its_accounting]
  exact (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain _).1

theorem start_clock : start.raw.clock = 6 :=
  the_same_original_root_pays_two_periods_at_clocks_five_and_six.2.2.2.1

theorem start_stock :
    start.raw.stock false false = 117 ∧ start.raw.stock false true = 0 ∧
      start.raw.stock true false = 143 ∧ start.raw.stock true true = 16 := by
  rw [start_raw]
  decide +kernel

abbrev ControlAt := Control (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)

theorem a_paid_renewal_keeps_its_phase_and_review
    {owner : ProgrammeSource.Input Bool Bool Bool Unit Unit}
    {origin raw : RawCurrent Bool Bool Unit Unit} {members : List Bool}
    {depth count prefixLimit renewalLimit : Nat} {control : ControlAt}
    (choice : Evolving.Epoch.Selection owner origin raw members depth count prefixLimit renewalLimit control .advance)
    (selected : selectedRenewal choice = true) (after : RawCurrent Bool Bool Unit Unit) :
    (choice.controlAfter after true).phase = control.phase ∧
      (choice.controlAfter after true).review = control.review := by
  cases choice with
  | reviewing cursor found review => simp [selectedRenewal] at selected
  | ordinary original =>
    cases original with
    | exhausted issue computed => simp [selectedRenewal] at selected
    | automatic operation computed =>
      cases operation with
      | renewal word phase guarded => exact ⟨phase.symm, rfl⟩
      | migration plan certificate => simp [selectedRenewal] at selected
      | repair cause attempt => simp [selectedRenewal] at selected

theorem start_control : start.control.phase = .renewal period ∧ start.control.review = none := by
  have ready : ¬ Public.Inquiry.HasWork renewal.native.frame renewal.native.actual.actual :=
    renewal_is_ready source proposal
  have kept := a_paid_renewal_keeps_its_phase_and_review renewal.choice the_installed_renewal_is_selected
    renewal.physicalResult.next.raw
  have written : (renewed source proposal).control = renewal.afterControl := by
    unfold renewed
    rw [Current.advance_eq_epoch _ ready]
    exact Transition.next_reads_the_written_control _ _
  have after : renewal.afterControl.phase = .renewal period ∧ renewal.afterControl.review = none := by
    unfold Current.afterControl
    rw [the_renewal_physically_pays_the_same_word.1]
    exact ⟨kept.1.trans the_paid_front_installs_the_same_renewal.1,
      kept.2.trans the_paid_front_installs_the_same_renewal.2⟩
  unfold start
  rw [end_is_the_original_renewal_and_its_accounting, drain_preserves_control, written]
  exact after

abbrev AdvanceReader (current : C) : Prop := current.native.reader = fun _ _ => .advance

private theorem advance_reader_transport
    {before after : ProgrammeSource.Input Bool Bool Bool Unit Unit} {beforeDepth beforeCount afterDepth afterCount : Nat}
    (first : Macro.Raw.Reader before beforeDepth beforeCount)
    (second : Macro.Raw.Reader after afterDepth afterCount)
    (input : after = before) (depth : afterDepth = beforeDepth) (count : afterCount = beforeCount)
    (reader : HEq second first) (constant : first = fun _ _ => .advance) :
    second = fun _ _ => .advance := by
  subst after afterDepth afterCount
  exact (eq_of_heq reader).trans constant

theorem advance_keeps_the_actual_reader (current : C) (installed : AdvanceReader current) :
    AdvanceReader current.advance := by
  have identity := current.advance_parameters
  exact advance_reader_transport current.native.reader current.advance.native.reader identity.1 identity.2.1
    identity.2.2.1 identity.2.2.2.2.2.2 installed

theorem native_payments_keep_the_actual_reader (current : C) (installed : AdvanceReader current) (count : Nat) :
    AdvanceReader (Execution.endAt current (Execution.nativePayments count)) := by
  induction count generalizing current with
  | zero => exact installed
  | succ count prior =>
    exact prior current.advance (advance_keeps_the_actual_reader current installed)

theorem start_reader : AdvanceReader start := by
  unfold start
  rw [end_is_the_original_renewal_and_its_accounting]
  exact native_payments_keep_the_actual_reader _ (advance_keeps_the_actual_reader renewal rfl) _

theorem an_advance_reader_submits_its_own_input (current : C) (reader : AdvanceReader current) :
    current.proposal = .advance := by
  unfold Current.proposal Public.Inquiry.ActualAt.proposal
  rw [reader]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
