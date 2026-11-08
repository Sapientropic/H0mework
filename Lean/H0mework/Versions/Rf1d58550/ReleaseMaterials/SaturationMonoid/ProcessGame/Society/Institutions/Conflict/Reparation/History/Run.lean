import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Root
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.RecordedBalance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

variable (script : List (Option (Capitalism.Universal.Abolition.Root.Registered.Compile.RawInput
    Party Good Port Technology Instrument))) (safe : NoFinancialBirths (Birth.attacked claim) script)

def runVisit : Nat → SourceNativeTemporalVisitAt
    (livingRoot claim script safe).toAuthoritativeRoot.toLedgerRoot
  | 0 => initial claim script safe
  | count + 1 =>
    let original := runVisit count
    original.next (Compiler.successor (flow claim script safe) original.current).next_eq

theorem runVisit_reads_the_original_position (count : Nat) (within : count ≤ script.length) :
    (runVisit claim script safe count).current = positionAt claim script count := by
  induction count with
  | zero => rfl
  | succ count prior =>
    let actual := runVisit claim script safe count
    change (Compiler.successor (flow claim script safe) actual.current).targetCurrent = _
    exact (Compiler.successor_current (flow claim script safe) actual.current).trans
      ((congrArg (nextCursor claim script) (prior (Nat.le_of_lt within))).trans
        (positionAt_step claim script count within))

theorem the_last_visit_reads_the_original_mixed_cut :
    (runVisit claim script safe script.length).current = .inr (finalCut claim script).native.visit.current ∧
    finalCut claim script = Quantities.Execution.endAt (Birth.attacked claim) script := by
  refine ⟨(runVisit_reads_the_original_position claim script safe _ le_rfl).trans (dif_neg (lt_irrefl _)), ?_⟩
  change Quantities.Execution.endAt (Birth.attacked claim) (script.take script.length) = _
  rw [List.take_length]

theorem each_visit_writes_the_original_whole_ledger
    (count : Nat) :
    let atVisit := runVisit claim script safe count
    HEq (Compiler.successor (flow claim script safe) atVisit.current).ledgerEvolution.destination
      (joint claim script safe atVisit.current).val.destination ∧
    (livingRoot claim script safe).generatedNextCurrentAt atVisit =
      ⟨Compiler.V (flow claim script safe), (livingRoot claim script safe).toAuthoritativeRoot,
        runVisit claim script safe (count + 1)⟩ :=
  ⟨Compiler.successor_destination _ _, Compiler.every_step_generates_the_same_root_next _ _⟩

theorem each_whole_write_carries_the_same_original_debt
    (current : Cursor claim script) :
    ((joint claim script safe current).val.destination
      (debtEntry (N := (Birth.originalFrame claim).N) (law := Birth.law claim)
        (oldSupport claim script safe current) (debtAt claim script current))).1 =
      debtEntry (N := (Birth.originalFrame claim).N) (law := Birth.law claim)
        (oldSupport claim script safe (nextCursor claim script current))
        (debtAt claim script (nextCursor claim script current)) := by
  unfold joint
  cases disposition claim script current <;> rfl

theorem terminal_debt_stage :
    debtAt claim script (runVisit claim script safe script.length).current = .recorded script :=
  congrArg (debtAt claim script) (the_last_visit_reads_the_original_mixed_cut claim script safe).1

theorem terminal_debt_has_exact_settlement :
    Nonempty ((Birth.law claim).SettlementAt (debtAt claim script (runVisit claim script safe script.length).current)) ↔
      recordedDue source attack script community key = 0 := by
  rw [terminal_debt_stage claim script safe]
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | actualRecorded _ zero => exact zero
  · intro zero
    exact ⟨Birth.Settlement.actualRecorded (Quantities.record (Birth.attacked claim) script) zero⟩

variable (nonempty : 0 < script.length)
  (paid : Quantities.Settled (Birth.attacked claim) script)

theorem the_first_actual_action_enters_the_same_mixed_runtime :
    (generated claim script safe nonempty paid).target.targetAnswerAndNext.nextCurrent =
      ⟨Compiler.V (flow claim script safe), (livingRoot claim script safe).toAuthoritativeRoot,
        runVisit claim script safe 1⟩ :=
  (generated claim script safe nonempty paid).target.targetAnswerAndNext_next_eq

theorem the_same_born_amount_survives_the_complete_original_script (noReceipt : NoReceipt claim script) :
    recordedDue source attack script community key = gross source attack community key := by
  have unchanged := recordedDue_append_without_receipts source attack [] script community key noReceipt
  exact unchanged.trans (recordedDue_at_opening claim)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
