import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Examples.TransferAndRepayment

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.MigrationRegression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

abbrev Party := Fin 3
abbrev issue := Financial.Examples.TransferAndRepayment.request 0 (.issue () 0 1 2)
abbrev assign := Financial.Examples.TransferAndRepayment.request 1 (.assign () 0 1 2 1)
abbrev payFirst := Financial.Examples.TransferAndRepayment.request 0 (.settle () 0 1 1)
abbrev paySecond := Financial.Examples.TransferAndRepayment.request 0 (.settle () 0 2 1)

def code : Code Party Unit Unit Unit Unit where
  law := Financial.Examples.TransferAndRepayment.law
  initial := Financial.Examples.TransferAndRepayment.initial
  task := ⟨[⟨1, [((), 1)], .necessity⟩], 0, 10, by decide⟩
  actions := []
  actionLimit := 0
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => 0
  readLocal := fun _ _ => 0
  historyAlphabet := [[issue], [assign], [payFirst], [paySecond]]
  historyLimit := 4
  eventAlphabet := []
  eventLimit := 0
  eligible := fun _ => true
  parties := List.finRange 3
  goods := [()]
  instruments := [()]
  parties_cover := List.mem_finRange
  goods_cover := by simp
  instruments_cover := by simp

def policy : code.Policy := fun _ _ => []
def source : Machine Party Unit Unit Unit Unit where
  code := code
  reference := policy
  reference_generated := by
    apply code.every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp [policy])
  history := [[issue], [assign], [payFirst], [paySecond]]
  original := by decide +kernel
  opponent := fun _ _ _ => none
  side := .original

def oldSlot := (Financial.accountAt source.input 2).current.slots[0]'(by decide +kernel)
def evolution := Financial.Migration.actual source.input 2 3 0 oldSlot
  (List.getElem?_eq_getElem (by decide +kernel))

theorem actual_assignment_and_two_material_payments :
    (source.actualExecution 1).submitted = [assign] ∧
      (source.actualExecution 2).submitted = [payFirst] ∧
      (source.actualExecution 3).submitted = [paySecond] ∧
      (source.actualExecution 3).after.stock 0 () = 0 ∧
      (source.actualExecution 3).after.stock 1 () = 1 ∧
      (source.actualExecution 3).after.stock 2 () = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem original_slot_is_live : ∃ obligation, oldSlot = .live obligation := by
  let isLive : ObligationSlot (Financial.vocabulary source.input) → Bool
    | .live _ => true | .terminal _ => false
  have live : isLive oldSlot = true := by decide +kernel
  cases slot : oldSlot with
  | live obligation => exact ⟨obligation, rfl⟩
  | terminal archive => simp only [slot, isLive, Bool.false_eq_true] at live

theorem exact_paid_receipts :
    (evolution.path.events source.input).map (Financial.Migration.retired source.input) = [0, 1, 1] := by
  decide +kernel

theorem actual_slot_migration_changes_residual_without_rewriting_admission :
    Financial.Migration.identity source.input evolution.slot = Financial.Migration.identity source.input oldSlot ∧
      Financial.total source.input (Financial.slotBalance source.input oldSlot) = 2 ∧
      Financial.total source.input (Financial.slotBalance source.input evolution.slot) = 0 ∧
      evolution.path.paid source.input = 2 ∧
      List.Sublist (evolution.path.events source.input)
        ((Financial.BalanceConservation.fromActualCut source.input 2 3).events.map
          (Financial.Migration.sourceEvent source.input)) := by
  refine ⟨evolution.path.preserves_identity source.input, by decide +kernel, by decide +kernel, ?_, evolution.sourced source.input⟩
  simp only [Financial.Migration.Path.paid, exact_paid_receipts, List.sum_cons, List.sum_nil]
  norm_num

theorem original_debt_is_archived_and_no_new_debt_replaces_it :
    (generate source 0).finance.current.slots.length = 1 ∧
      (generate source 3).finance.current.slots.length = 1 ∧
      ∃ archive, evolution.slot = .terminal archive := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  let isTerminal : ObligationSlot (Financial.vocabulary source.input) → Bool
    | .live _ => false | .terminal _ => true
  have terminal : isTerminal evolution.slot = true := by decide +kernel
  cases slot : evolution.slot with
  | live obligation => simp only [slot, isTerminal, Bool.false_eq_true] at terminal
  | terminal archive => exact ⟨archive, rfl⟩

theorem terminal_archive_and_complete_admission_survive_every_later_cut (later : Nat) :
    let next := Financial.Migration.actual source.input 5 later 0 evolution.slot evolution.present
    next.slot = evolution.slot ∧ Financial.Migration.identity source.input next.slot =
      Financial.Migration.identity source.input oldSlot := by
  obtain ⟨archive, archived⟩ := original_debt_is_archived_and_no_new_debt_replaces_it.2.2
  let next := Financial.Migration.actual source.input 5 later 0 evolution.slot evolution.present
  have same : next.slot = evolution.slot := by
    have path : Financial.Migration.Path source.input (.terminal archive) next.slot := archived ▸ next.path
    exact (path.terminal_is_unchanged source.input).trans archived.symm
  exact ⟨same, (congrArg (Financial.Migration.identity source.input) same).trans
    (evolution.path.preserves_identity source.input)⟩

def control (word : RawEvent Party Unit Unit Unit Unit) : Machine Party Unit Unit Unit Unit :=
  { source with history := [[issue]], original := by decide +kernel, continuation := [word] }

def controlSlot (word : RawEvent Party Unit Unit Unit Unit) :=
  (Financial.accountAt (control word).input 2).current.slots[0]'(by change 0 < 1; decide)

def controlEvolution (word : RawEvent Party Unit Unit Unit Unit) :=
  Financial.Migration.actual (control word).input 2 2 0 (controlSlot word)
    (List.getElem?_eq_getElem (by change 0 < 1; decide))

abbrev forged := [Financial.Examples.TransferAndRepayment.request 0 (.assign () 0 1 2 1)]
abbrev zero := [Financial.Examples.TransferAndRepayment.request 0 (.settle () 0 1 0)]
abbrev excessive := [Financial.Examples.TransferAndRepayment.request 0 (.settle () 0 1 3)]

theorem refused_assignment_and_overdraw_do_not_retire_the_original_debt :
    ((control forged).actualExecution 2).submitted = forged ∧
      (controlEvolution forged).path.paid (control forged).input = 0 ∧
      Financial.total (control forged).input
        (Financial.slotBalance (control forged).input (controlEvolution forged).slot) = 2 ∧
      ((control excessive).actualExecution 2).submitted = excessive ∧
      (controlEvolution excessive).path.paid (control excessive).input = 0 ∧
      Financial.total (control excessive).input
        (Financial.slotBalance (control excessive).input (controlEvolution excessive).slot) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem zero_payment_cannot_forge_strict_retirement :
    ((control zero).actualExecution 2).submitted = zero ∧
      (controlEvolution zero).path.paid (control zero).input = 0 ∧
      Financial.total (control zero).input
        (Financial.slotBalance (control zero).input (controlEvolution zero).slot) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.MigrationRegression
