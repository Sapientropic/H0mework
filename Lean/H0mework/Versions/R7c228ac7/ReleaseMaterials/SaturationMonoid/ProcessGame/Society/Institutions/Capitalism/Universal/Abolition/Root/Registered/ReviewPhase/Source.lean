import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.Micro

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

open Source.Program PublicFunction
open Macro.Services

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (origin : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- A pending review is a dependent view of one existing physical prefix.
The original code inventory and original service receipts remain fixed. -/
structure PendingAt (current : Physical.Cursor Party Good Port Technology Instrument) where
  private mk ::
  paidCount : Nat
  remaining : List (Material.Migration.CodePair Party Good Port Technology Instrument)
  rejected : Migration.Budget.RejectedPrefix source depth count prefixLimit renewalLimit origin code
    (state source depth count prefixLimit renewalLimit origin).raw
    (Migration.candidates source depth count prefixLimit renewalLimit origin)
    (state source depth count prefixLimit renewalLimit current).raw remaining paidCount
  actualPast : current.past = origin.past ++
    List.replicate paidCount (Compile.RawInput.primitive code.request)

def initial : PendingAt source depth count prefixLimit renewalLimit origin code origin :=
  ⟨0, Migration.candidates source depth count prefixLimit renewalLimit origin, .nil _ _, by simp⟩

theorem actual_fee_target (current : Physical.Cursor Party Good Port Technology Instrument)
    (payment : Review.PaymentAt source.seed.law code.request
      (state source depth count prefixLimit renewalLimit current).raw) :
    (state source depth count prefixLimit renewalLimit
      (Migration.Budget.feeTarget current code)).raw = payment.microNext := by
  have actual := Migration.Budget.original_fee_compiler_uses_the_same_paid_microstep
    source depth count prefixLimit renewalLimit current code
  cases attempted : Review.attempt source.seed.law code.request code.scope
      (state source depth count prefixLimit renewalLimit current).raw with
  | inl paid =>
      rw [attempted] at actual
      exact actual.1
  | inr obstruction =>
      exact (obstruction.request_is_actually_rejected payment.accepted).elim

namespace PendingAt

variable {source depth count prefixLimit renewalLimit origin code}
  {current : Physical.Cursor Party Good Port Technology Instrument}
  (pending : PendingAt source depth count prefixLimit renewalLimit origin code current)

def afterRejected (pair : Material.Migration.CodePair Party Good Port Technology Instrument)
    (tail : List (Material.Migration.CodePair Party Good Port Technology Instrument))
    (head : pending.remaining = pair :: tail)
    (payment : Review.PaymentAt source.seed.law code.request
      (state source depth count prefixLimit renewalLimit current).raw)
    (issue : Migration.Budget.Issue source depth count prefixLimit renewalLimit origin code
      (pending.paidCount + 1) payment.microNext pair)
    (generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
      pending.paidCount (state source depth count prefixLimit renewalLimit current).raw pair =
        .rejected payment issue) :
    PendingAt source depth count prefixLimit renewalLimit origin code
      (Migration.Budget.feeTarget current code) := by
  refine ⟨pending.paidCount + 1, tail, ?_, ?_⟩
  · rw [actual_fee_target source depth count prefixLimit renewalLimit code current payment]
    exact .snoc (head ▸ pending.rejected) payment issue generated
  · change current.past ++ [Compile.RawInput.primitive code.request] = _
    rw [pending.actualPast, List.replicate_succ']
    exact List.append_assoc _ _ _

theorem actual_fee_budget : pending.paidCount ≤
    min (Review.physicalBudget code.request code.scope
      (state source depth count prefixLimit renewalLimit origin).raw)
      (Migration.candidates source depth count prefixLimit renewalLimit origin).length :=
  pending.rejected.finite_pending_bound

theorem exact_original_material_payment :
    (state source depth count prefixLimit renewalLimit current).raw.stock code.scope.payer code.scope.good +
      (pending.paidCount : ℚ) * code.scope.amount =
      (state source depth count prefixLimit renewalLimit origin).raw.stock code.scope.payer code.scope.good :=
  pending.rejected.original_material_payment

theorem original_candidate_inventory : pending.paidCount + pending.remaining.length =
    (Migration.candidates source depth count prefixLimit renewalLimit origin).length :=
  pending.rejected.inventory_exact

theorem every_paid_review_is_in_the_original_past :
    current.past.length = origin.past.length + pending.paidCount := by
  rw [pending.actualPast]
  simp

end PendingAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.initial
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.PendingAt.actual_fee_budget
