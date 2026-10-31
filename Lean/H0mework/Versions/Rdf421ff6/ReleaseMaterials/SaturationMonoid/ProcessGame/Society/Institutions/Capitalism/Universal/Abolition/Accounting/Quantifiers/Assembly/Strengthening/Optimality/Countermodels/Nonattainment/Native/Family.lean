import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native.Prefix

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (accountAfter tag visit oneItems events actualNativeRun)
noncomputable section

def originalObligation := (Abolition.Root.Epoch.Finance.admission input 0 0 (.inr originalClaim)).toObligation

theorem the_same_original_live_slot_is_not_replaced : originalAccount.current.slots = [.live originalObligation] := by
  with_unfolding_all rfl

theorem the_original_live_slot_has_its_actual_single_share : originalObligation.residual = Finsupp.single true 1 := by
  change Abolition.Root.Epoch.Finance.claimInitial input 0 0 (.inr originalClaim) = _
  rw [Abolition.Root.Epoch.Finance.new_initial_balance_is_the_same_single]
  have holder : originalClaim.holder = true := by decide +kernel
  have quantity : originalClaim.quantity = 1 := by decide +kernel
  rw [holder,quantity]

theorem the_original_borrower_is_still_the_same_source_party :
    originalObligation.content.debtor input 0 0 = false := by decide +kernel

def afterAccount (n : Nat) := accountAfter input 0 0 initialHistory (word n) originalAccount

def run (n : Nat) : finance.Run originalAccount.current (afterAccount n).current :=
  actualNativeRun input 0 0 initialHistory (word n) originalAccount

theorem every_candidate_keeps_the_exact_source_native_history (n : Nat) :
    originalAccount.current.history <+: (afterAccount n).current.history :=
  Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.every_actual_primitive_keeps_the_entire_previous_native_history
    input 0 0 initialHistory (word n) originalAccount

theorem every_family_inventory_is_its_original_actual_requests (n : Nat) :
    (events input 0 0 initialHistory (word n)).map
      (fun item => (item.instruction input 0 0).request) = word n ∧
    (∀ item ∈ events input 0 0 initialHistory (word n),
      (item.interpreter input 0 0).Valid (item.instruction input 0 0).before (item.instruction input 0 0).request) := by
  have valid : ∀ item ∈ ((Physical.Public.interpreter input).execute
      (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.state input 0 0 initialHistory).raw 0 (word n)).items,
      (Physical.Public.interpreter input).Valid item.before item.request := by
    unfold Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.state
    rw [← the_physical_cut_is_the_same_original_source_suffix,the_active_physical_interpreter_is_the_same_source_law]
    exact every_original_family_request_is_actually_accepted n
  have noConsents : ∀ instruction ∈ word n,instruction.consents = [] := by
    intro instruction member
    simp only [word,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  have actual := Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.the_actual_primitive_prefixes_retain_the_whole_original_word
    input 0 0 initialHistory 0 (word n) noConsents valid
  exact ⟨actual.1,actual.2.1⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
