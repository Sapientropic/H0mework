import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Instruction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Slot

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

omit [DecidableEq Good] in
private theorem pay_apply (balance : Financial.Balance source) (holder party : Party) (quantity : ℚ) :
    Financial.pay source balance holder quantity party =
      balance party + if party = holder then -quantity else 0 := rfl

omit [DecidableEq Good] in
theorem pay_zero (balance : Financial.Balance source) (holder : Party) :
    Financial.pay source balance holder 0 = balance := by
  ext party
  simp [pay_apply]

omit [DecidableEq Good] in
theorem pay_single (holder : Party) (quantity : ℚ) :
    Financial.pay source (Finsupp.single holder quantity) holder quantity = 0 := by
  ext party
  simp only [pay_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply]
  split <;> simp_all [eq_comm]

theorem zero_use_keeps_the_same_original_balance
    {claim : Epoch.Finance.Claim source depth count}
    (receipt : Epoch.Finance.Review source depth count claim)
    (balance : Financial.Balance source) (available : ℚ) (holder : Party)
    (kind : receipt.kind = .payment holder)
    (unused : receipt.allocated source depth count balance available = 0) :
    receipt.after source depth count balance available = balance := by
  simp only [Epoch.Finance.Review.after,kind,unused,pay_zero]

theorem exact_use_pays_the_same_original_singleton
    {claim : Epoch.Finance.Claim source depth count}
    (receipt : Epoch.Finance.Review source depth count claim)
    (balance : Financial.Balance source) (available : ℚ) (holder : Party) (quantity : ℚ)
    (kind : receipt.kind = .payment holder)
    (original : balance = Finsupp.single holder quantity)
    (used : receipt.allocated source depth count balance available = quantity) :
    receipt.after source depth count balance available = 0 := by
  simp only [Epoch.Finance.Review.after,kind]
  rw [used,original]
  exact pay_single source holder quantity

theorem an_unchanged_nonzero_original_boundary_keeps_the_same_live_obligation
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (boundary : Epoch.Finance.Boundary source depth count obligation)
    (unchanged : boundary.event.after source depth count = obligation.residual)
    (nonzero : obligation.residual ≠ 0) :
    (Epoch.Finance.boundaryDisposition source depth count boundary).targetSlot = .live obligation := by
  unfold Epoch.Finance.boundaryDisposition
  rw [dif_neg (fun cleared => nonzero (unchanged.symm.trans cleared))]
  simp only [BoundaryDisposition.targetSlot,ActiveCarryDisposition.target,unchanged]

theorem a_cleared_original_boundary_retains_its_exact_terminal_obligation
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (boundary : Epoch.Finance.Boundary source depth count obligation)
    (cleared : boundary.event.after source depth count = 0) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary source depth count),
      (Epoch.Finance.boundaryDisposition source depth count boundary).targetSlot = .terminal archive ∧
      archive.obligation = obligation ∧ archive.sourceEvent = boundary.event := by
  unfold Epoch.Finance.boundaryDisposition
  rw [dif_pos cleared]
  exact ⟨_,rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Slot
