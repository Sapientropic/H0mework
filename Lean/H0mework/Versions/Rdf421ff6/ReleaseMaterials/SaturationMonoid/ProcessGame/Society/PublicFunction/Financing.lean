import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Compiler

/-! Financing is an accepted liability issuance followed by an accepted,
lender-signed material disbursement in the same actual instruction trace.
Principal is denominated in one instrument and converted only through its
source settlement unit/rate. Issuance alone supplies no material funds. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Financing

open Institutions.Capitalism.Universal.Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure Terms (Party Instrument : Type u) where
  borrower : Party
  lender : Party
  instrument : Instrument
  principal : ℚ

def IssueMatches (terms : Terms Party Instrument)
    (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .issue code debtor creditor quantity => code = terms.instrument ∧
      debtor = terms.borrower ∧ creditor = terms.lender ∧ quantity = terms.principal
  | _ => False

def PayoutMatches (law : RawLaw Party Good Port Technology Instrument)
    (terms : Terms Party Instrument) (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .transfer sender recipient goods => request.signer = terms.lender ∧
      sender = terms.lender ∧ recipient = terms.borrower ∧
      goods = [(law.settlementUnit terms.instrument, terms.principal * law.settlementRate terms.instrument)]
  | _ => False

instance (terms : Terms Party Instrument) (request : Request Party Good Port Technology Instrument) :
    Decidable (IssueMatches terms request) := by
  unfold IssueMatches
  cases request.operation <;> infer_instance

instance (law : RawLaw Party Good Port Technology Instrument) (terms : Terms Party Instrument)
    (request : Request Party Good Port Technology Instrument) :
    Decidable (PayoutMatches law terms request) := by
  unfold PayoutMatches
  cases request.operation <;> infer_instance

structure Disbursement (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (terms : Terms Party Instrument) where
  private mk ::
  principal_positive : 0 < terms.principal
  rate_positive : 0 < law.settlementRate terms.instrument
  distinct : terms.lender ≠ terms.borrower
  issue : ExecutionItem Party Good Port Technology Instrument
  issue_mem : issue ∈ law.rawItems current word
  issue_accepted : law.Valid issue.before issue.request
  issue_matches : IssueMatches terms issue.request
  payout : ExecutionItem Party Good Port Technology Instrument
  payout_mem : payout ∈ law.rawItems current word
  payout_accepted : law.Valid payout.before payout.request
  payout_matches : PayoutMatches law terms payout.request
  ordered : issue.index < payout.index

def readDisbursement? (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (terms : Terms Party Instrument) :
    Option (Disbursement law current word terms) :=
  if positive : 0 < terms.principal ∧ 0 < law.settlementRate terms.instrument ∧
      terms.lender ≠ terms.borrower then
    (law.rawItems current word).attach.findSome? fun issue =>
      if issued : law.Valid issue.val.before issue.val.request ∧ IssueMatches terms issue.val.request then
        (law.rawItems current word).attach.findSome? fun payout =>
          if disbursed : law.Valid payout.val.before payout.val.request ∧
              PayoutMatches law terms payout.val.request ∧ issue.val.index < payout.val.index then
            some ⟨positive.1, positive.2.1, positive.2.2, issue.val, issue.property,
              issued.1, issued.2, payout.val, payout.property, disbursed.1,
              disbursed.2.1, disbursed.2.2⟩
          else none
      else none
  else none

namespace Disbursement

variable {law : RawLaw Party Good Port Technology Instrument}
  {current : RawCurrent Party Good Technology Instrument}
  {word : RawEvent Party Good Port Technology Instrument} {terms : Terms Party Instrument}
  (receipt : Disbursement law current word terms)

theorem issue_kind : receipt.issue.request.operation =
    .issue terms.instrument terms.borrower terms.lender terms.principal := by
  have matched := receipt.issue_matches
  cases kind : receipt.issue.request.operation <;> simp only [IssueMatches, kind] at matched
  rcases matched with ⟨rfl, rfl, rfl, rfl⟩
  rfl

theorem payout_kind : receipt.payout.request.operation = .transfer terms.lender terms.borrower
    [(law.settlementUnit terms.instrument, terms.principal * law.settlementRate terms.instrument)] := by
  have matched := receipt.payout_matches
  cases kind : receipt.payout.request.operation <;> simp only [PayoutMatches, kind] at matched
  rcases matched with ⟨_signed, rfl, rfl, rfl⟩
  rfl

theorem lender_signed : receipt.payout.request.signer = terms.lender := by
  have matched := receipt.payout_matches
  rw [PayoutMatches, receipt.payout_kind] at matched
  exact matched.1

theorem issuance_supplies_no_material :
    (law.step receipt.issue.before receipt.issue.request).stock = receipt.issue.before.stock :=
  law.issuance_creates_no_material _ _ _ _ _ _ receipt.issue_kind

theorem actual_principal_created :
    law.actualClaimDelta receipt.issue.before receipt.issue.request
      terms.instrument terms.borrower terms.lender = terms.principal := by
  simp only [RawLaw.actualClaimDelta, if_pos receipt.issue_accepted,
    RawLaw.claimDelta, receipt.issue_kind]
  exact if_pos True.intro

theorem borrower_received_material :
    (law.step receipt.payout.before receipt.payout.request).stock
        terms.borrower (law.settlementUnit terms.instrument) =
      receipt.payout.before.stock terms.borrower (law.settlementUnit terms.instrument) +
        terms.principal * law.settlementRate terms.instrument := by
  simp [RawLaw.step, receipt.payout_accepted, RawLaw.paidStep,
    RawLaw.debit, RawLaw.credit, receipt.payout_kind, locate, flowAt, amount, receipt.distinct]

theorem lender_paid_material :
    (law.step receipt.payout.before receipt.payout.request).stock
        terms.lender (law.settlementUnit terms.instrument) =
      receipt.payout.before.stock terms.lender (law.settlementUnit terms.instrument) -
        terms.principal * law.settlementRate terms.instrument := by
  simp [RawLaw.step, receipt.payout_accepted, RawLaw.paidStep,
    RawLaw.debit, RawLaw.credit, receipt.payout_kind, locate, flowAt, amount, Ne.symm receipt.distinct]

end Disbursement

def FundingCovers (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (terms : Terms Party Instrument)
    (receipt : Disbursement law current word terms) : Prop :=
  law.totalDebit (law.rawItems current word) terms.borrower (law.settlementUnit terms.instrument) ≤
      terms.principal * law.settlementRate terms.instrument ∧
  ∀ item ∈ law.rawItems current word,
    0 < flowAt (law.actualDebit item.before item.request) terms.borrower
        (law.settlementUnit terms.instrument) → receipt.payout.index < item.index

instance (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (terms : Terms Party Instrument)
    (receipt : Disbursement law current word terms) : Decidable (FundingCovers law current word terms receipt) := by
  unfold FundingCovers
  infer_instance

def OnlyThisLoan (terms : Terms Party Instrument)
    (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .issue .. => IssueMatches terms request
  | .assign .. | .settle .. => False
  | _ => True

instance (terms : Terms Party Instrument) (request : Request Party Good Port Technology Instrument) :
    Decidable (OnlyThisLoan terms request) := by
  unfold OnlyThisLoan
  cases request.operation <;> infer_instance

/-- An exact net principal, with no other liability issuance, assignment or
repayment hidden in the service word. Existing claims are not a funding fee. -/
def CleanExposure (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (terms : Terms Party Instrument) : Prop :=
  law.totalFinancialDelta (law.rawItems current word) terms.instrument terms.borrower terms.lender =
      terms.principal ∧
  ∀ item ∈ law.rawItems current word, OnlyThisLoan terms item.request

instance (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (terms : Terms Party Instrument) :
    Decidable (CleanExposure law current word terms) := by
  unfold CleanExposure
  infer_instance

structure FinancedPlan (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (task : PublicTaskSpec Party Good)
    (alphabet : List (Request Party Good Port Technology Instrument)) (budget : Nat)
    (terms : Terms Party Instrument) where
  private mk ::
  service : PaidServicePlan law current task alphabet budget
  finance : Disbursement law current service.word terms
  covers : FundingCovers law current service.word terms finance
  exposure : CleanExposure law current service.word terms
  borrower_served : ∃ slot ∈ task.slots, slot.bearer = terms.borrower

/-- Observe financing in the service plan already generated by a source.
This checker preserves that exact plan; it does not select another word. -/
def readFinancedService? {law : RawLaw Party Good Port Technology Instrument}
    {current : RawCurrent Party Good Technology Instrument} {task : PublicTaskSpec Party Good}
    {alphabet : List (Request Party Good Port Technology Instrument)} {budget : Nat}
    (service : PaidServicePlan law current task alphabet budget) (terms : Terms Party Instrument) :
    Option (FinancedPlan law current task alphabet budget terms) :=
  if served : ∃ slot ∈ task.slots, slot.bearer = terms.borrower then
    match readDisbursement? law current service.word terms with
    | none => none
    | some receipt =>
        if covers : FundingCovers law current service.word terms receipt then
          if exposure : CleanExposure law current service.word terms then
            some ⟨service, receipt, covers, exposure, served⟩
          else none
        else none
  else none

theorem readFinancedService_preserves_service
    {law : RawLaw Party Good Port Technology Instrument}
    {current : RawCurrent Party Good Technology Instrument} {task : PublicTaskSpec Party Good}
    {alphabet : List (Request Party Good Port Technology Instrument)} {budget : Nat}
    (service : PaidServicePlan law current task alphabet budget) (terms : Terms Party Instrument)
    (funded : FinancedPlan law current task alphabet budget terms)
    (checked : readFinancedService? service terms = some funded) : funded.service = service := by
  unfold readFinancedService? at checked
  split at checked
  · split at checked
    · cases checked
    · split at checked
      · split at checked
        · cases Option.some.inj checked; rfl
        · cases checked
      · cases checked
  · cases checked

def compileFinanced? (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (task : PublicTaskSpec Party Good)
    (alphabet : List (Request Party Good Port Technology Instrument)) (budget : Nat)
    (terms : Terms Party Instrument) : Option (FinancedPlan law current task alphabet budget terms) :=
  if served : ∃ slot ∈ task.slots, slot.bearer = terms.borrower then
    (words alphabet budget).attach.findSome? fun word =>
      match readDisbursement? law current word.val terms with
      | none => none
      | some receipt =>
          if covers : FundingCovers law current word.val terms receipt then
            if exposure : CleanExposure law current word.val terms then
            match checked : PaidServicePlan.checkCandidate word.val word.property with
            | none => none
            | some service =>
                have same := PaidServicePlan.checkCandidate_word word.val word.property service checked
                let funded : {r : Disbursement law current service.word terms //
                    FundingCovers law current service.word terms r ∧
                      CleanExposure law current service.word terms} :=
                  same.symm ▸ (⟨receipt, covers, exposure⟩ : {r : Disbursement law current word.val terms //
                    FundingCovers law current word.val terms r ∧ CleanExposure law current word.val terms})
                some ⟨service, funded.val, funded.property.1, funded.property.2, served⟩
            else none
          else none
  else none

namespace FinancedPlan

variable {law : RawLaw Party Good Port Technology Instrument}
  {current : RawCurrent Party Good Technology Instrument} {task : PublicTaskSpec Party Good}
  {alphabet : List (Request Party Good Port Technology Instrument)} {budget : Nat}
  {terms : Terms Party Instrument} (plan : FinancedPlan law current task alphabet budget terms)

theorem actual_net_principal :
    plan.service.next.claims terms.instrument terms.borrower terms.lender =
      current.claims terms.instrument terms.borrower terms.lender + terms.principal := by
  have balance := law.execute_financial_balance current 0 plan.service.word
    terms.instrument terms.borrower terms.lender
  change plan.service.next.claims terms.instrument terms.borrower terms.lender =
    current.claims terms.instrument terms.borrower terms.lender +
      law.totalFinancialDelta (law.rawItems current plan.service.word)
        terms.instrument terms.borrower terms.lender at balance
  rw [plan.exposure.1] at balance
  exact balance

theorem other_claims_unchanged (code : Instrument) (debtor creditor : Party)
    (other : (code, debtor, creditor) ≠ (terms.instrument, terms.borrower, terms.lender)) :
    plan.service.next.claims code debtor creditor = current.claims code debtor creditor := by
  have delta_zero : ∀ item ∈ law.rawItems current plan.service.word,
      law.actualClaimDelta item.before item.request code debtor creditor = 0 := by
    intro item inside
    rw [law.accepted_delta _ _ (plan.service.sound.2 item inside)]
    have clean := plan.exposure.2 item inside
    cases kind : item.request.operation <;> simp only [OnlyThisLoan, kind, IssueMatches] at clean
    case issue instrument issuer beneficiary quantity =>
      rcases clean with ⟨rfl, rfl, rfl, rfl⟩
      simp only [RawLaw.claimDelta, kind, if_neg other]
    all_goals simp only [RawLaw.claimDelta, kind]
  have total_zero : law.totalFinancialDelta (law.rawItems current plan.service.word) code debtor creditor = 0 := by
    unfold RawLaw.totalFinancialDelta
    have mapped : ((law.rawItems current plan.service.word).map
        (fun item => law.actualClaimDelta item.before item.request code debtor creditor)) =
        (law.rawItems current plan.service.word).map (fun _ => (0 : ℚ)) := by
      apply List.map_congr_left
      exact delta_zero
    rw [mapped]
    induction law.rawItems current plan.service.word with
    | nil => rfl
    | cons item rest ih =>
        change 0 + (rest.map (fun _ => (0 : ℚ))).sum = 0
        rw [ih, zero_add]
  have balance := law.execute_financial_balance current 0 plan.service.word code debtor creditor
  change plan.service.next.claims code debtor creditor = current.claims code debtor creditor +
    law.totalFinancialDelta (law.rawItems current plan.service.word) code debtor creditor at balance
  rw [total_zero, add_zero] at balance
  exact balance

end FinancedPlan

end SaturationMonoid.ProcessGame.Society.PublicFunction.Financing
