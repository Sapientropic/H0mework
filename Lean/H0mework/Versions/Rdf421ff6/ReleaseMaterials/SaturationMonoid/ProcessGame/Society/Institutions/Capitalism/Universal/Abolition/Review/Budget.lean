import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation
import Mathlib.Data.Rat.Floor

/-! The review budget is read from one original stock cell and the positive
fee in one fixed source request.  A paid step executes that request through
the original law.  This bounds paid reviews; forcing an arbitrary attempted
action to pay or expose its obstruction is the enclosing source's job. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- A dependent readout of the original payment opcode, not a budget or an
authority token.  Every payment below has its own actual before-current. -/
structure FeeScope (request : Request Party Good Port Technology Instrument) where
  payer : Party
  good : Good
  amount : ℚ
  operation : request.operation = .use payer [(good, amount)] .external
  positive : 0 < amount

variable (law : RawLaw Party Good Port Technology Instrument)
  (request : Request Party Good Port Technology Instrument) (fee : FeeScope request)

def physicalBudget (current : RawCurrent Party Good Technology Instrument) : Nat :=
  Nat.floor (current.stock fee.payer fee.good / fee.amount)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem zero_budget_is_real_shortage (current : RawCurrent Party Good Technology Instrument)
    (zero : physicalBudget request fee current = 0) : current.stock fee.payer fee.good < fee.amount := by
  have fraction := Nat.lt_floor_add_one (current.stock fee.payer fee.good / fee.amount)
  change current.stock fee.payer fee.good / fee.amount <
    (physicalBudget request fee current : ℚ) + 1 at fraction
  rw [zero, Nat.cast_zero, zero_add] at fraction
  simpa only [one_mul] using (div_lt_iff₀ fee.positive).mp fraction

def PermissionAt (current : RawCurrent Party Good Technology Instrument) : Prop :=
  law.operationAllowed current request = true ∧
    ∀ port ∈ law.requiredPorts current request,
      law.allowed current.technology port request.signer = true ∨
        law.controller current.technology port ∈ request.consents

instance (current : RawCurrent Party Good Technology Instrument) :
    Decidable (PermissionAt law request current) := by unfold PermissionAt; infer_instance

omit [DecidableEq Instrument] in
theorem valid_iff_permission_and_stock (current : RawCurrent Party Good Technology Instrument) :
    law.Valid current request ↔
      PermissionAt law request current ∧ fee.amount ≤ current.stock fee.payer fee.good := by
  simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.debit, RawLaw.credit,
    fee.operation, locate, flowAt, amount, NonnegativeBundle, PermissionAt, fee.positive.le, and_assoc]

structure PaymentAt (current : RawCurrent Party Good Technology Instrument) : Type u where
  accepted : law.Valid current request

namespace PaymentAt
variable {law request} {current : RawCurrent Party Good Technology Instrument}
  (payment : PaymentAt law request current)

def next (_payment : PaymentAt law request current) : RawCurrent Party Good Technology Instrument :=
  law.next current [request]

theorem original_item : (⟨0, current, request⟩ : ExecutionItem Party Good Port Technology Instrument) ∈
    law.rawItems current [request] := List.mem_cons_self

include payment fee

omit [DecidableEq Instrument] in
theorem actual_debit : flowAt (law.actualDebit current request) fee.payer fee.good = fee.amount := by
  simp [RawLaw.actualDebit, payment.accepted, RawLaw.debit, fee.operation, locate, flowAt, amount]

omit [DecidableEq Instrument] in
theorem actual_credit : flowAt (law.actualCredit current request) fee.payer fee.good = 0 := by
  simp [RawLaw.actualCredit, payment.accepted, RawLaw.credit, fee.operation, flowAt, amount]

theorem stock_balance : payment.next.stock fee.payer fee.good + fee.amount = current.stock fee.payer fee.good := by
  have balance := law.actual_next_material_balance current [request] fee.payer fee.good
  simpa only [next, RawLaw.rawItems, RawLaw.execute, RawLaw.totalDebit, RawLaw.totalCredit,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    payment.actual_debit fee, payment.actual_credit fee] using balance

theorem next_nonnegative : 0 ≤ payment.next.stock fee.payer fee.good := by
  have affordable := ((valid_iff_permission_and_stock law request fee current).mp payment.accepted).2
  have balance := payment.stock_balance fee
  linarith

theorem original_claims_unchanged : payment.next.claims = current.claims := by
  simp only [next, RawLaw.next, RawLaw.execute, RawLaw.step, if_pos payment.accepted,
    RawLaw.paidStep, RawLaw.nextClaims, fee.operation]

/-- The natural rank is proved to decrease because the original material
cell paid its fee; no endpoint inequality is accepted as input. -/
theorem physical_budget_debits_one :
    physicalBudget request fee current = physicalBudget request fee payment.next + 1 := by
  have ratio : current.stock fee.payer fee.good / fee.amount =
      payment.next.stock fee.payer fee.good / fee.amount + 1 := by
    rw [← payment.stock_balance fee, add_div, div_self (ne_of_gt fee.positive)]
  unfold physicalBudget
  rw [ratio]
  exact Nat.floor_add_one (div_nonneg (payment.next_nonnegative fee) fee.positive.le)

end PaymentAt

/-- A finite consumer of actual paid source steps.  Its endpoint is always
the original law's next, and it introduces no responsibility ledger. -/
inductive PaidRun : RawCurrent Party Good Technology Instrument →
    RawCurrent Party Good Technology Instrument → Nat → Type u
  | nil (current) : PaidRun current current 0
  | snoc {start middle count}
      (prior : PaidRun start middle count) (payment : PaymentAt law request middle) :
      PaidRun start payment.next (count + 1)

namespace PaidRun
variable {law request} {start target : RawCurrent Party Good Technology Instrument} {count : Nat}
  (run : PaidRun law request start target count)

include run fee

theorem material_balance : target.stock fee.payer fee.good + (count : ℚ) * fee.amount =
    start.stock fee.payer fee.good := by
  induction run with
  | nil => simp
  | snoc prior payment previous =>
      have actual := payment.stock_balance fee
      push_cast
      nlinarith

theorem original_claims_unchanged : target.claims = start.claims := by
  induction run with
  | nil => rfl
  | snoc prior payment previous => exact (payment.original_claims_unchanged fee).trans previous

theorem count_add_remaining_budget :
    count + physicalBudget request fee target = physicalBudget request fee start := by
  induction run with
  | nil => simp
  | snoc prior payment previous =>
      have actual := payment.physical_budget_debits_one fee
      omega

theorem count_le_original_stock_budget : count ≤ physicalBudget request fee start := by
  have exactBudget := run.count_add_remaining_budget fee
  omega

theorem no_extension_after_budget (spent : count = physicalBudget request fee start) :
    IsEmpty (PaymentAt law request target) := by
  constructor
  intro payment
  have remaining := run.count_add_remaining_budget fee
  have next := payment.physical_budget_debits_one fee
  omega

end PaidRun

inductive Blockage (current : RawCurrent Party Good Technology Instrument) : Type u
  | stock (shortage : current.stock fee.payer fee.good < fee.amount)
  | authority (denied : ¬ PermissionAt law request current)

def attempt (current : RawCurrent Party Good Technology Instrument) :
    PaymentAt law request current ⊕ Blockage law request fee current :=
  if affordable : fee.amount ≤ current.stock fee.payer fee.good then
    if permitted : PermissionAt law request current then
      .inl ⟨(valid_iff_permission_and_stock law request fee current).mpr ⟨permitted, affordable⟩⟩
    else .inr (.authority permitted)
  else .inr (.stock (lt_of_not_ge affordable))

namespace Blockage
variable {law request fee} {current : RawCurrent Party Good Technology Instrument}
  (blocked : Blockage law request fee current)

include blocked

omit [DecidableEq Instrument] in
theorem request_is_actually_rejected : ¬ law.Valid current request := by
  intro valid
  have original := (valid_iff_permission_and_stock law request fee current).mp valid
  cases blocked with
  | stock shortage => exact (not_lt_of_ge original.2) shortage
  | authority denied => exact denied original.1

theorem actual_source_preserves_current : law.step current request = current :=
  law.rejected_preserves_current current request blocked.request_is_actually_rejected

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem exact_cause : current.stock fee.payer fee.good < fee.amount ∨
    law.operationAllowed current request ≠ true ∨
      ∃ port ∈ law.requiredPorts current request,
        law.allowed current.technology port request.signer ≠ true ∧
          law.controller current.technology port ∉ request.consents := by
  classical
  cases blocked with
  | stock shortage => exact Or.inl shortage
  | authority denied =>
      right
      by_cases policy : law.operationAllowed current request = true
      · right
        have missing : ¬ ∀ port ∈ law.requiredPorts current request,
            law.allowed current.technology port request.signer = true ∨
              law.controller current.technology port ∈ request.consents := fun gates => denied ⟨policy, gates⟩
        simpa only [not_forall, exists_prop, not_or] using missing
      · exact Or.inl policy

end Blockage

theorem spent_budget_emits_original_stock_obstruction
    {start target : RawCurrent Party Good Technology Instrument} {count : Nat}
    (run : PaidRun law request start target count)
    (spent : count = physicalBudget request fee start) :
    ∃ shortage : target.stock fee.payer fee.good < fee.amount,
      attempt law request fee target = .inr (.stock shortage) := by
  have remaining := run.count_add_remaining_budget fee
  have zero : physicalBudget request fee target = 0 := by omega
  have shortage := zero_budget_is_real_shortage request fee target zero
  exact ⟨shortage, by simp only [attempt, dif_neg (not_le_of_gt shortage)]⟩

#print axioms PaymentAt.physical_budget_debits_one
#print axioms PaidRun.material_balance
#print axioms PaidRun.count_le_original_stock_budget
#print axioms attempt
#print axioms Blockage.exact_cause
#print axioms spent_budget_emits_original_stock_obstruction

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review
