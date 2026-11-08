import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Path

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

section
variable {input : Universal.Root.ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw : RawCurrent Party Good Technology Instrument} {members : List Party}
  {depth count prefixLimit renewalLimit : Nat}
  {control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
  {pair : Material.Migration.CodePair Party Good Port Technology Instrument}

def selectedMigration :
    Selection input origin raw members depth count prefixLimit renewalLimit control (.migrate pair) → Bool
  | .ordinary (.migrate ..) => true
  | _ => false

theorem selectedMigration_exact
    (choice : Selection input origin raw members depth count prefixLimit renewalLimit control (.migrate pair))
    (selected : selectedMigration choice = true) :
    ∃ checked : Actual.Migration.Checks input origin raw members pair,
      choice = .ordinary (.migrate pair checked) := by
  cases choice with
  | ordinary choice =>
    cases choice with
    | migrate _ checked => exact ⟨checked, rfl⟩
    | migrationBlocked _ _ => simp [selectedMigration] at selected
  | reviewing _ _ _ => simp [selectedMigration] at selected

def selectedRenewal :
    Selection input origin raw members depth count prefixLimit renewalLimit control .advance → Bool
  | .ordinary (.automatic (.renewal ..) _) => true
  | _ => false

theorem selectedRenewal_exact
    (choice : Selection input origin raw members depth count prefixLimit renewalLimit control .advance)
    (selected : selectedRenewal choice = true) :
    ∃ word, control.phase = .renewal word ∧ choice.executionRaw = .execute word ∧
      Abolition.Review.Guarded.Checks input origin raw members word := by
  cases choice with
  | ordinary choice =>
    cases choice with
    | automatic operation _ =>
      cases operation with
      | renewal word phase checked => exact ⟨word, phase, rfl, checked⟩
      | migration _ _ => simp [selectedRenewal] at selected
      | repair _ _ => simp [selectedRenewal] at selected
    | exhausted _ _ => simp [selectedRenewal] at selected
  | reviewing _ _ _ => simp [selectedRenewal] at selected
end

private theorem pending_preserves_control (current : C) (pending : Pending current) :
    (Execution.next current none).control = current.control := by
  change current.advance.control = current.control
  unfold Pending at pending
  unfold Current.advance
  rw [dif_pos pending]
  split
  · exact current.native_birth_keeps_the_same_source_phase _
  · exact current.the_unconsumed_source_phase_is_not_reset_by_ordinary_accounting

theorem drain_preserves_control (current : C) :
    (Execution.endAt current (Execution.drain current)).control = current.control := by
  suffices prefixes : ∀ (length : Nat) (start : C), length ≤ Execution.remainingNative start →
      (Execution.endAt start (Execution.nativePayments length)).control = start.control by
    exact prefixes _ _ le_rfl
  intro length
  induction length with
  | zero => intros; rfl
  | succ length ih =>
    intro start fits
    have pending := (Execution.pending_iff_positive_original_positions start).mpr (by omega)
    have spent := (Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length
      start 1 (by omega)).1
    change Execution.remainingNative (Execution.next start none) + 1 = Execution.remainingNative start at spent
    change (Execution.endAt (Execution.next start none) (Execution.nativePayments length)).control = start.control
    exact (ih _ (by omega)).trans (pending_preserves_control start pending)

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (proposal : Proposal Party Good Port Technology Instrument)

structure Checked : Prop where
  migrationSelected : selectedMigration (migrationQuery source proposal).choice = true
  migrationPaid : (migrationQuery source proposal).physicalResult.isAccepted = true
  renewalSelected : selectedRenewal (renewalQuery source proposal).choice = true
  renewalPaid : (renewalQuery source proposal).physicalResult.isAccepted = true

theorem checked_migration_installs_its_original_renewal (checked : Checked source proposal) :
    (migrationQuery source proposal).executionRaw = .execute proposal.pair.1 ∧
      (renewalStart source proposal).control.phase = .renewal proposal.pair.2 := by
  obtain ⟨_, chosen⟩ := selectedMigration_exact _ checked.migrationSelected
  let query := migrationQuery source proposal
  have ready : ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual :=
    preparation_is_ready source proposal
  constructor
  · unfold Current.executionRaw
    rw [chosen]
    rfl
  · rw [renewalStart, drain_preserves_control, migrated, Current.advance_eq_epoch _ ready,
      Transition.next_reads_the_written_control]
    unfold Current.afterControl
    rw [chosen, checked.migrationPaid]
    rfl

theorem checked_renewal_executes_the_same_word (checked : Checked source proposal) :
    (renewalQuery source proposal).executionRaw = .execute proposal.pair.2 := by
  obtain ⟨word, phase, body, _⟩ := selectedRenewal_exact _ checked.renewalSelected
  have sameControl : (renewalQuery source proposal).control = (renewalStart source proposal).control :=
    ((renewalStart source proposal).requery_keeps_control_and_complete_account (fun _ _ => .advance)).1
  rw [sameControl, (checked_migration_installs_its_original_renewal source proposal checked).2] at phase
  cases phase
  exact body

inductive Failure where
  | migrationRoute (issue : selectedMigration (migrationQuery source proposal).choice = false)
  | migrationPayment (issue : (migrationQuery source proposal).physicalResult.isAccepted = false)
  | renewalRoute (issue : selectedRenewal (renewalQuery source proposal).choice = false)
  | renewalPayment (issue : (renewalQuery source proposal).physicalResult.isAccepted = false)

theorem Failure.refutes {source : C} {proposal : Proposal Party Good Port Technology Instrument}
    (issue : Failure source proposal) (checked : Checked source proposal) : False := by
  cases issue with
  | migrationRoute issue => exact Bool.noConfusion (checked.migrationSelected.symm.trans issue)
  | migrationPayment issue => exact Bool.noConfusion (checked.migrationPaid.symm.trans issue)
  | renewalRoute issue => exact Bool.noConfusion (checked.renewalSelected.symm.trans issue)
  | renewalPayment issue => exact Bool.noConfusion (checked.renewalPaid.symm.trans issue)

def inspectPath : PLift (Checked source proposal) ⊕ Failure source proposal :=
  if migration : selectedMigration (migrationQuery source proposal).choice then
    if paid : (migrationQuery source proposal).physicalResult.isAccepted then
      if renewal : selectedRenewal (renewalQuery source proposal).choice then
        if served : (renewalQuery source proposal).physicalResult.isAccepted then
          .inl ⟨⟨migration, paid, renewal, served⟩⟩
        else .inr (.renewalPayment (Bool.eq_false_iff.mpr served))
      else .inr (.renewalRoute (Bool.eq_false_iff.mpr renewal))
    else .inr (.migrationPayment (Bool.eq_false_iff.mpr paid))
  else .inr (.migrationRoute (Bool.eq_false_iff.mpr migration))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
