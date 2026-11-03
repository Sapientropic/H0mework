import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers.Source
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Zero
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Native.Complete

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers.ZeroCounter

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

def birthWord : RawEvent Party Unit Unit Unit Unit := [request 0 (.issue () 0 1 0)]
def history : List (Compile.RawInput Party Unit Unit Unit Unit) := [.execute birthWord]
def start := Physical.receive (Physical.initial (Party := Party) (Good := Unit) (Port := Unit)
  (Technology := Unit) (Instrument := Unit)) (.execute birthWord)
def tag : Epoch.Interface.Tag input 0 0 := .publicActual 0 0 [] start
def visit := (Epoch.Interface.root input 0 0 tag).initialVisit
def before := Epoch.Finance.consumeVisit input 0 0 tag visit
  (NativeResponsibilityProcess.GeneratedState.initial (Epoch.Finance.process input 0 0))

theorem an_actual_zero_issue_is_a_live_row_with_no_positive_principal :
    before.current.slots.map isTerminal = [false] ∧
      ∀ slot ∈ before.current.slots, Epoch.Finance.slotBalance input 0 0 slot = 0 := by
  have matrix : ∀ instrument debtor holder, ledgerClaims input 0 0 before.current instrument debtor holder = 0 := by decide +kernel
  exact ⟨by decide +kernel,fun slot listed => a_zero_full_matrix_clears_every_original_slot_balance input 0 0 before matrix slot listed⟩

theorem the_original_positive_share_compiler_has_no_payment_to_request :
    Native.word input 0 0 before = [] :=
  zero_balances_cannot_generate_another_positive_payment input 0 0 _ before
    an_actual_zero_issue_is_a_live_row_with_no_positive_principal.2

theorem empty_financial_consumption_does_not_fabricate_a_terminal_archive :
    (Native.after input 0 0 history before).current.slots.map isTerminal = [false] := by
  unfold Native.after Native.visit Native.tag Native.start
  rw [the_original_positive_share_compiler_has_no_payment_to_request]
  decide +kernel

theorem the_stronger_source_generates_the_real_zero_boundary :
    ArchiveNative.word input 0 0 before = [request 0 (.settle () 0 0 0)] := by
  change Native.word input 0 0 before ++ archiveWord input 0 0 (Physical.Public.interpreter input) before = _
  rw [the_original_positive_share_compiler_has_no_payment_to_request]
  have borrower : ∀ slot ∈ before.current.slots,
      (Epoch.Finance.slotClaim input 0 0 slot).debtor input 0 0 = 0 := by decide +kernel
  rw [fixed_address_zero_boundaries_read_only_the_actual_live_flags before borrower,
    an_actual_zero_issue_is_a_live_row_with_no_positive_principal.1]
  rfl

theorem the_zero_boundary_has_its_own_primitive_source_resources :
    ArchiveNative.Conditions input 0 0 history before := by
  unfold ArchiveNative.Conditions
  rw [the_stronger_source_generates_the_real_zero_boundary]
  decide +kernel

theorem the_actual_zero_review_archives_the_original_zero_row :
    (ArchiveNative.after input 0 0 history before).current.slots.map isTerminal = [true] := by
  unfold ArchiveNative.after ArchiveNative.visit ArchiveNative.tag ArchiveNative.start
  rw [the_stronger_source_generates_the_real_zero_boundary]
  decide +kernel

theorem actual_archival_keeps_the_original_claim_and_history :
    (ArchiveNative.after input 0 0 history before).current.slots.map (Epoch.Finance.slotClaim input 0 0) =
      before.current.slots.map (Epoch.Finance.slotClaim input 0 0) ∧
      before.current.history <+: (ArchiveNative.after input 0 0 history before).current.history :=
  (ArchiveNative.primitive_resources_pay_every_original_share_and_preserve_the_whole_ledger
    input 0 0 history before the_zero_boundary_has_its_own_primitive_source_resources).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers.ZeroCounter
