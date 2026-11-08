import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut

open Source.Program Institutions.Capitalism.Universal.Root PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action Current base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

variable {epoch : Epoch}

abbrev stagedCurrent (inventory : Inventory epoch) :=
  World.current epoch (World.staged inventory).inputs

def originalBalancesClear (inventory : Inventory epoch) : Prop :=
  ∀ position : Repayment.Position Bool Unit,
    Financial.Family.ledgerClaims sources (World.staged inventory).finance.current
      position.instrument position.debtor position.creditor ≤ 0

private theorem position_is_original (position : Repayment.Position Bool Unit) :
    position ∈ Settlement.addresses := by
  rcases position with ⟨instrument, debtor, creditor⟩
  cases instrument
  cases debtor <;> cases creditor <;> simp [Settlement.addresses]

private theorem positive_address_has_a_native_attempt
    (law : RawLaw Bool Financed.Good Mandate.Source.Port (State Bool Unit) Unit)
    (position : Repayment.Position Bool Unit) (current : Current)
    (positive : 0 < Repayment.balance position current) :
    Repayment.Portfolio.Repair.word law position current ≠ [] := by
  unfold Repayment.Portfolio.Repair.word Repayment.respond
  rw [dif_pos positive]
  by_cases paid : Repayment.Ready law position current
  · rw [dif_pos paid]
    simp [Repayment.candidate]
  · rw [dif_neg paid]
    simp [Repayment.candidate]

theorem no_added_repayment_iff_all_original_staged_balances_clear (inventory : Inventory epoch) :
    World.repaymentWord inventory = [] ↔ originalBalancesClear inventory := by
  let current := stagedCurrent inventory
  have matrix := (World.staged inventory).matrix
  change Repayment.Portfolio.word (Mandate.law base epoch.scope) (Handoff.debtPositions current) current = [] ↔ _
  constructor
  · intro empty position
    have amount := congrFun (congrFun (congrFun matrix position.instrument) position.debtor) position.creditor
    rw [amount]
    apply le_of_not_gt
    intro positive
    have inside : position ∈ Handoff.debtPositions current :=
      List.mem_filter.mpr ⟨position_is_original position, decide_eq_true positive⟩
    cases debts : Handoff.debtPositions current with
    | nil => exact List.not_mem_nil (debts ▸ inside)
    | cons first rest =>
      have original : first ∈ Handoff.debtPositions current := debts.symm ▸ List.mem_cons_self
      have owed : 0 < Repayment.balance first current := of_decide_eq_true (List.mem_filter.mp original).2
      rw [debts] at empty
      exact positive_address_has_a_native_attempt (Mandate.law base epoch.scope) first current owed
        (List.append_eq_nil_iff.mp empty).1
  · intro clear
    have none : Handoff.debtPositions current = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro position inside
      have positive : 0 < Repayment.balance position current := of_decide_eq_true (List.mem_filter.mp inside).2
      have budget := clear position
      rw [matrix] at budget
      exact (not_lt_of_ge budget) positive
    rw [none]
    rfl

theorem a_required_repayment_has_an_original_positive_address (inventory : Inventory epoch)
    (owed : World.repaymentWord inventory ≠ []) :
    ∃ position ∈ Handoff.debtPositions (stagedCurrent inventory),
      0 < Financial.Family.ledgerClaims sources (World.staged inventory).finance.current
        position.instrument position.debtor position.creditor := by
  have noEmpty : Handoff.debtPositions (stagedCurrent inventory) ≠ [] := by
    intro empty
    apply owed
    unfold World.repaymentWord
    rw [empty]
    rfl
  cases debt : Handoff.debtPositions (stagedCurrent inventory) with
  | nil => exact (noEmpty debt).elim
  | cons position _ =>
    have original : position ∈ Handoff.debtPositions (stagedCurrent inventory) := debt.symm ▸ List.mem_cons_self
    refine ⟨position, List.mem_cons_self, ?_⟩
    rw [(World.staged inventory).matrix]
    exact of_decide_eq_true (List.mem_filter.mp original).2

theorem an_expired_native_service_cannot_require_an_extra_pre_handoff_word
    (inventory : Inventory epoch) (review : Handoff.Ready epoch.bound inventory.inputs)
    (word : List Action) (slot : epoch.source.Slot) :
    ¬ epoch.source.SlotPaid (World.current epoch inventory.inputs) word slot := by
  intro paid
  have late : epoch.source.seed.task.deadline < (World.current epoch inventory.inputs).clock :=
    review.actual_successor_is_after_the_expired_scope
  exact (not_le_of_gt (late.trans_le (epoch.source.seed.law.next_clock_nondecreasing _ _))) paid.2.1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut
