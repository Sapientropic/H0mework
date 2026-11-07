import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

inductive Verdict (paidCount : Nat) (before : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) : Type
  | selected (payment : Review.PaymentAt source.seed.law code.request before)
      (checked : Checks source depth count prefixLimit renewalLimit current code (paidCount + 1) payment.microNext pair)
  | rejected (payment : Review.PaymentAt source.seed.law code.request before)
      (issue : Issue source depth count prefixLimit renewalLimit current code (paidCount + 1) payment.microNext pair)
  | blocked (obstruction : Review.Blockage source.seed.law code.request code.scope before)

def evaluate (paidCount : Nat) (before : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) :
    Verdict source depth count prefixLimit renewalLimit current code paidCount before pair :=
  match Review.attempt source.seed.law code.request code.scope before with
  | .inr obstruction => .blocked obstruction
  | .inl payment =>
      match inspect source depth count prefixLimit renewalLimit current code (paidCount + 1) payment.microNext pair with
      | .accepted checked => .selected payment checked
      | .rejected issue => .rejected payment issue

/-- This finite calculation trace records paid rejections. It is not a
responsibility process, and candidate instructions are not executed here. -/
inductive RejectedPrefix : RawCurrent Party Good Technology Instrument →
    List (Material.Migration.CodePair Party Good Port Technology Instrument) →
    RawCurrent Party Good Technology Instrument →
    List (Material.Migration.CodePair Party Good Port Technology Instrument) → Nat → Type
  | nil (before pairs) : RejectedPrefix before pairs before pairs 0
  | snoc {start candidates before pair remaining paidCount}
      (prior : RejectedPrefix start candidates before (pair :: remaining) paidCount)
      (payment : Review.PaymentAt source.seed.law code.request before)
      (issue : Issue source depth count prefixLimit renewalLimit current code (paidCount + 1) payment.microNext pair)
      (generated : evaluate source depth count prefixLimit renewalLimit current code paidCount before pair = .rejected payment issue) :
      RejectedPrefix start candidates payment.microNext remaining (paidCount + 1)

namespace RejectedPrefix

variable {source depth count prefixLimit renewalLimit current code}
  {start afterFees : RawCurrent Party Good Technology Instrument}
  {candidates remaining : List (Material.Migration.CodePair Party Good Port Technology Instrument)}
  {paidCount : Nat}
  (trace : RejectedPrefix source depth count prefixLimit renewalLimit current code start candidates afterFees remaining paidCount)

def payments : Review.PaidMicroRun source.seed.law code.request start afterFees paidCount := by
  induction trace with
  | nil => exact .nil _
  | snoc _ payment _ _ prior => exact .snoc prior payment

include trace

theorem inventory_exact : paidCount + remaining.length = candidates.length := by
  induction trace with
  | nil => simp
  | snoc _ _ _ _ previous => simp only [List.length_cons] at previous; omega

theorem original_material_payment :
    afterFees.stock code.scope.payer code.scope.good + (paidCount : ℚ) * code.scope.amount =
      start.stock code.scope.payer code.scope.good :=
  trace.payments.material_balance code.scope

theorem finite_pending_bound : paidCount ≤ min (Review.physicalBudget code.request code.scope start) candidates.length :=
  le_min (trace.payments.count_le_original_budget code.scope) (by have := trace.inventory_exact; omega)

theorem paid_rejections_retain_the_original_period :
    afterFees.clock = start.clock ∧ afterFees.round = start.round := trace.payments.same_period

end RejectedPrefix

inductive CompletedAt (start : RawCurrent Party Good Technology Instrument)
    (candidates : List (Material.Migration.CodePair Party Good Port Technology Instrument)) : Type
  | selected {before pair remaining paidCount}
      (prior : RejectedPrefix source depth count prefixLimit renewalLimit current code start candidates before (pair :: remaining) paidCount)
      (payment : Review.PaymentAt source.seed.law code.request before)
      (checked : Checks source depth count prefixLimit renewalLimit current code (paidCount + 1) payment.microNext pair)
      (generated : evaluate source depth count prefixLimit renewalLimit current code paidCount before pair = .selected payment checked)
  | exhausted {before paidCount}
      (prior : RejectedPrefix source depth count prefixLimit renewalLimit current code start candidates before [] paidCount)
  | blocked {before pair remaining paidCount}
      (prior : RejectedPrefix source depth count prefixLimit renewalLimit current code start candidates before (pair :: remaining) paidCount)
      (obstruction : Review.Blockage source.seed.law code.request code.scope before)
      (generated : evaluate source depth count prefixLimit renewalLimit current code paidCount before pair = .blocked obstruction)

def completePending {start candidates}
    (remaining : List (Material.Migration.CodePair Party Good Port Technology Instrument))
    (before : RawCurrent Party Good Technology Instrument) (paidCount : Nat)
    (prior : RejectedPrefix source depth count prefixLimit renewalLimit current code start candidates before remaining paidCount) :
    CompletedAt source depth count prefixLimit renewalLimit current code start candidates :=
  match remaining with
  | [] => .exhausted prior
  | pair :: tail =>
      match produced : evaluate source depth count prefixLimit renewalLimit current code paidCount before pair with
      | .selected payment checked => .selected prior payment checked produced
      | .blocked obstruction => .blocked prior obstruction produced
      | .rejected payment issue =>
          completePending tail payment.microNext (paidCount + 1) (.snoc prior payment issue produced)

/-- Only the source fee opcode and finite original candidate code are
inputs. Payments, rejection causes, the selected pair and its target are
computed at the currents actually produced by the fee steps. -/
def compile := completePending source depth count prefixLimit renewalLimit current code
  (Migration.candidates source depth count prefixLimit renewalLimit current)
  (state source depth count prefixLimit renewalLimit current).raw 0 (.nil _ _)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.compile
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.RejectedPrefix.original_material_payment
