import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem the_original_single_slot_allocator_generates_its_terminal_archive
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
    (single : before.current.slots = [.live obligation])
    (item : Epoch.Finance.ActualItem input depth count) (movement : Epoch.Finance.Movement input depth count item)
    (receipt : Epoch.Finance.Review input depth count obligation.content)
    (read : Epoch.Finance.readReview input depth count obligation.content item = some receipt)
    (holder : Party) (payment : receipt.kind = .payment holder)
    (sameQuantity : receipt.quantity = movement.quantity)
    (balance : obligation.residual = Finsupp.single holder movement.quantity) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary input depth count),
      (Epoch.Finance.allocate input depth count item movement before).after.current.slots = [.terminal archive] ∧
      archive.obligation = obligation := by
  have positive : 0 < before.current.slots.length := by rw [single]; exact Nat.zero_lt_succ 0
  have present : before.current.slots.get ⟨0,positive⟩ = .live obligation := by simp only [single,List.get_eq_getElem,List.getElem_cons_zero]
  have sound := Epoch.Finance.live_sound input depth count before ⟨0,positive⟩ obligation present
  let cap := min movement.quantity receipt.quantity
  have capEq : cap = movement.quantity := min_eq_left (le_of_eq sameQuantity.symm)
  have receiptCap : receipt.quantity = cap := sameQuantity.trans capEq.symm
  have balanceCap : obligation.residual = Finsupp.single holder cap := by rw [capEq]; exact balance
  obtain ⟨archive,terminal,identity,_⟩ := the_actual_full_payment_generates_the_original_terminal_archive
    input depth count obligation sound.1 receipt holder cap payment receiptCap balanceCap
  refine ⟨archive,?_,identity⟩
  rcases before with ⟨⟨slots,history⟩,generated⟩
  change slots = [.live obligation] at single
  cases single
  simp! only [Epoch.Finance.allocate]
  run_tac
    let owner := (``Epoch.Finance.allocate).getPrefix
    let names := #[owner ++ `allocateAt,owner ++ `allocateLive,
      owner ++ `Allocation.append,owner ++ `Allocation.idle]
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let expanded ← Lean.Meta.deltaExpand target (fun name => names.contains (Lean.privateToUserName name))
    Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq expanded]
  simp only [List.length_cons,List.length_nil,Nat.zero_lt_succ,↓reduceDIte,List.get_eq_getElem,
    List.getElem_cons_zero,read]
  simp only [NativeResponsibilityProcess.GeneratedState.step,NativeResponsibilityProcess.Edge.target,
    Epoch.Finance.process,List.set_cons_zero]
  simpa only [boundary,cap] using congrArg (fun slot => [slot]) terminal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
