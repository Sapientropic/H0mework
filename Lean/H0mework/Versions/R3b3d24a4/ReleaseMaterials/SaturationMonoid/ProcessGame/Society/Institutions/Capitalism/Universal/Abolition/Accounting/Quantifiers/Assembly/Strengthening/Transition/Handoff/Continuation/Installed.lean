import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Routing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def installedQuery (current : C) : C := Execution.query current (some .advance)

def renewalSuffix (current : C) : Script :=
  some .advance :: Execution.drain (installedQuery current).advance

theorem renewalSuffix_ends_at_the_original_native_drain (current : C) :
    Execution.endAt current (renewalSuffix current) =
      Execution.endAt (installedQuery current).advance (Execution.drain (installedQuery current).advance) :=
  rfl

structure InstalledPaid (current : C) : Prop where
  selected : selectedRenewal (installedQuery current).choice = true
  physical : (installedQuery current).physicalResult.isAccepted = true

theorem InstalledPaid.executes_the_original_installed_word (current : C) (paid : InstalledPaid current) :
    ∃ word, current.control.phase = .renewal word ∧ (installedQuery current).executionRaw = .execute word := by
  obtain ⟨word, phase, execute, _⟩ := selectedRenewal_exact _ paid.selected
  have control : (installedQuery current).control = current.control :=
    (current.requery_keeps_control_and_complete_account (fun _ _ => .advance)).1
  exact ⟨word, control ▸ phase, execute⟩

section

variable {input : Universal.Root.ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw : RawCurrent Party Good Technology Instrument} {members : List Party}
  {depth count prefixLimit renewalLimit : Nat}
  {control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology)
    (Instrument := Instrument)}

private theorem selected_after_phase
    (choice : Selection input origin raw members depth count prefixLimit renewalLimit control .advance)
    (selected : selectedRenewal choice = true) (after : RawCurrent Party Good Technology Instrument) :
    (choice.controlAfter after true).phase = control.phase := by
  cases choice with
  | ordinary selectedChoice =>
    cases selectedChoice with
    | automatic operation ready =>
      cases operation with
      | renewal word phase checked => exact phase.symm
      | migration _ _ => simp [selectedRenewal] at selected
      | repair _ _ => simp [selectedRenewal] at selected
    | exhausted _ _ => simp [selectedRenewal] at selected
  | reviewing _ _ _ => simp [selectedRenewal] at selected

end

theorem InstalledPaid.keeps_the_phase_after_the_actual_drain (current : C)
    (paid : InstalledPaid current) (ready : ¬ Pending current) :
    (Execution.endAt current (renewalSuffix current)).control.phase = current.control.phase := by
  let query := installedQuery current
  have readyQuery : ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual := ready
  rw [renewalSuffix_ends_at_the_original_native_drain, drain_preserves_control,
    Current.advance_eq_epoch query readyQuery, Transition.next_reads_the_written_control]
  change (query.choice.controlAfter query.physicalResult.next.raw query.physicalResult.isAccepted).phase =
    current.control.phase
  rw [paid.physical]
  exact (selected_after_phase query.choice paid.selected _).trans
    (congrArg Control.phase (current.requery_keeps_control_and_complete_account (fun _ _ => .advance)).1)

theorem the_installed_attempt_has_the_original_write_and_successor (current : C) :
    Evolving.Epoch.Current.ClosedAt (installedQuery current) ∧ Recorded current (renewalSuffix current) :=
  ⟨Execution.actual_step current (some .advance), record current _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation
