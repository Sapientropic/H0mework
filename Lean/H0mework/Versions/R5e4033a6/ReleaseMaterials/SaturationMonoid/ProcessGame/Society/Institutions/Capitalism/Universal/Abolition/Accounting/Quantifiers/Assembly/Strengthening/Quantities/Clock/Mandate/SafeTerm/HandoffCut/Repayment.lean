import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Cut

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut

open Source.Program Institutions.Capitalism.Universal.Root PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev Address := Repayment.Position Bool Unit

def rawRepaymentItems :=
  (Mandate.law base epoch.scope).rawItems (stagedCurrent inventory) (World.repaymentWord inventory)

def afterBalance (position : Address) :=
  Repayment.balance position (World.current epoch (oldCut inventory).inputs)

def stagedBalance (position : Address) := Repayment.balance position (stagedCurrent inventory)

structure CheckedRepayment : Prop where
  legal : ∀ item ∈ rawRepaymentItems inventory, (Mandate.law base epoch.scope).Valid item.before item.request
  progress : ∀ address ∈ Handoff.debtPositions (stagedCurrent inventory),
    afterBalance inventory address < stagedBalance inventory address

inductive RepaymentIssue where
  | instruction (item : {item // item ∈ rawRepaymentItems inventory})
      (refused : ¬ (Mandate.law base epoch.scope).Valid item.val.before item.val.request)
  | address (address : Address) (original : address ∈ Handoff.debtPositions (stagedCurrent inventory))
      (noPayment : stagedBalance inventory address ≤ afterBalance inventory address)

inductive RepaymentCheck where
  | paid (settled : CheckedRepayment inventory)
  | blocked (issue : RepaymentIssue inventory)

def inspectRepayment : RepaymentCheck inventory :=
  match Material.inspectList (fun item => (Mandate.law base epoch.scope).Valid item.before item.request)
      (rawRepaymentItems inventory) with
  | .failure item member refused => .blocked (.instruction ⟨item, member⟩ refused)
  | .clear legal =>
    match Material.inspectList (fun position => afterBalance inventory position < stagedBalance inventory position)
        (Handoff.debtPositions (stagedCurrent inventory)) with
    | .failure address original unpaid => .blocked (.address address original (le_of_not_gt unpaid))
    | .clear progress => .paid ⟨legal, progress⟩

theorem RepaymentIssue.rules_out (issue : RepaymentIssue inventory) : ¬ CheckedRepayment inventory := by
  intro paid
  cases issue with
  | instruction item refused => exact refused (paid.legal item.val item.property)
  | address address original unpaid => exact (not_lt_of_ge unpaid) (paid.progress address original)

theorem a_refused_repayment_item_is_in_the_original_appended_word
    (item : {item // item ∈ rawRepaymentItems inventory}) :
    World.repaymentWord inventory ≠ [] ∧
      (oldCut inventory).inputs = (World.reviewed inventory).inputs ∧
      item.val ∈ (World.repaymentExecution inventory).interpreted.items := by
  have owed : World.repaymentWord inventory ≠ [] := by
    intro empty
    have member := (congrArg (fun word => item.val ∈
      (Mandate.law base epoch.scope).rawItems (stagedCurrent inventory) word) empty).mp item.property
    exact List.not_mem_nil member
  have different := fun clear => owed ((no_added_repayment_iff_all_original_staged_balances_clear inventory).mpr clear)
  refine ⟨owed, congrArg World.Inventory.inputs (actual_debt_uses_the_existing_paid_repayment_cut inventory different), ?_⟩
  have same : (World.repaymentExecution inventory).interpreted.items = rawRepaymentItems inventory := by
    rw [(World.repaymentExecution inventory).interpreted_exact]
    change (Mandate.law base epoch.scope).rawItems _ _ = _
    rw [(World.actual_repayment_word_and_cut inventory).1, (World.actual_repayment_word_and_cut inventory).2]
    rfl
  exact (congrArg (fun original => item.val ∈ original) same.symm).mp item.property

theorem an_unpaid_address_is_a_positive_original_ledger_line
    (address : Address) (original : address ∈ Handoff.debtPositions (stagedCurrent inventory))
    (noPayment : stagedBalance inventory address ≤ afterBalance inventory address) :
    0 < Financial.Family.ledgerClaims sources (World.staged inventory).finance.current
      address.instrument address.debtor address.creditor ∧
    Financial.Family.ledgerClaims sources (World.staged inventory).finance.current
      address.instrument address.debtor address.creditor ≤
    Financial.Family.ledgerClaims sources (oldCut inventory).finance.current
      address.instrument address.debtor address.creditor := by
  rw [(World.staged inventory).matrix, (oldCut inventory).matrix]
  exact ⟨of_decide_eq_true (List.mem_filter.mp original).2, noPayment⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut
