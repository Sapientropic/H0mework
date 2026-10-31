import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Assessment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Reparation uses actual material rather than a new IOU or assignment.
The original root's claim-focused source chooses this channel. Actual law
authorizes the debit; the old controller need not endorse its own obligation. -/
def compensationOperation (cohort : List Party) (beneficiary : Party)
    (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .transfer sender receiver _ =>
      sender ∈ cohort ∧ receiver = beneficiary
  | .produce operator | .revise operator _ => operator ∈ cohort
  | .use bearer _ purpose =>
      bearer ∈ cohort ∨ purpose = .necessity ∨ purpose = .maintenance
  | .present => True
  | .issue .. | .assign .. | .settle .. => False

instance (cohort : List Party) (beneficiary : Party)
    (request : Request Party Good Port Technology Instrument) : Decidable (compensationOperation cohort beneficiary request) := by
  unfold compensationOperation
  cases request.operation <;> infer_instance

def localRepairOperation (beneficiary : Party)
    (request : Request Party Good Port Technology Instrument) : Prop :=
  request.signer = beneficiary ∧ match request.operation with
    | .produce operator | .revise operator _ => operator = beneficiary
    | .use bearer _ _ => bearer = beneficiary
    | .present => True
    | .transfer .. | .issue .. | .assign .. | .settle .. => False

instance (beneficiary : Party) (request : Request Party Good Port Technology Instrument) :
    Decidable (localRepairOperation beneficiary request) := by
  unfold localRepairOperation
  cases request.operation <;> infer_instance

def compensationCash (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (beneficiary : Party) (good : Good) : ℚ :=
  (items.map fun item => match item.request.operation with
    | .transfer .. => flowAt (law.actualCredit item.before item.request) beneficiary good -
        flowAt (law.actualDebit item.before item.request) beneficiary good
    | _ => 0).sum

inductive ReparationBlocker (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (cohort : List Party) (beneficiary : Party) (word : RawEvent Party Good Port Technology Instrument)
    (good : Good)
  | rejected (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ law.rawItems before word) (invalid : ¬ law.Valid item.before item.request)
  | noQualifyingMaterial
      (noCash : ¬ ((∀ request ∈ word, compensationOperation cohort beneficiary request) ∧
        0 < compensationCash law (law.rawItems before word) beneficiary good))
      (noRepair : ¬ (beneficiary ∈ cohort ∧ (∀ request ∈ word, localRepairOperation beneficiary request) ∧
        0 < productiveNetFor law (law.rawItems before word) beneficiary good))

inductive ReparationResult (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (cohort : List Party) (beneficiary : Party) (word : RawEvent Party Good Port Technology Instrument)
    (good : Good)
  | compensation
      (valid : ∀ item ∈ law.rawItems before word, law.Valid item.before item.request)
      (source : ∀ request ∈ word, compensationOperation cohort beneficiary request)
      (positive : 0 < compensationCash law (law.rawItems before word) beneficiary good)
  | repair
      (valid : ∀ item ∈ law.rawItems before word, law.Valid item.before item.request)
      (own : beneficiary ∈ cohort)
      (source : ∀ request ∈ word, localRepairOperation beneficiary request)
      (positive : 0 < productiveNetFor law (law.rawItems before word) beneficiary good)
  | blocked (issue : ReparationBlocker law before cohort beneficiary word good)

inductive MaterialAdmission (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : Type
  | accepted (valid : ∀ item ∈ items, law.Valid item.before item.request)
  | rejected (item : ExecutionItem Party Good Port Technology Instrument)
      (member : item ∈ items) (invalid : ¬ law.Valid item.before item.request)

def inspectMaterial (law : RawLaw Party Good Port Technology Instrument) :
    (items : List (ExecutionItem Party Good Port Technology Instrument)) → MaterialAdmission law items
  | [] => .accepted (by simp)
  | item :: rest =>
    if valid : law.Valid item.before item.request then
      match inspectMaterial law rest with
      | .accepted later => .accepted (by
          intro next member
          rcases List.mem_cons.mp member with same | old
          · exact same ▸ valid
          · exact later next old)
      | .rejected next member invalid => .rejected next (List.mem_cons_of_mem item member) invalid
    else .rejected item List.mem_cons_self valid

def reparationResult (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (cohort : List Party) (beneficiary : Party) (word : RawEvent Party Good Port Technology Instrument)
    (good : Good) : ReparationResult law before cohort beneficiary word good :=
  match inspectMaterial law (law.rawItems before word) with
  | .accepted accepted =>
    if cash : (∀ request ∈ word, compensationOperation cohort beneficiary request) ∧
        0 < compensationCash law (law.rawItems before word) beneficiary good then
      .compensation accepted cash.1 cash.2
    else if repaired : beneficiary ∈ cohort ∧ (∀ request ∈ word, localRepairOperation beneficiary request) ∧
        0 < productiveNetFor law (law.rawItems before word) beneficiary good then
      .repair accepted repaired.1 repaired.2.1 repaired.2.2
    else .blocked (.noQualifyingMaterial cash repaired)
  | .rejected item member invalid => .blocked (.rejected item member invalid)

def ReparationResult.credit
    {law : RawLaw Party Good Port Technology Instrument} {before : RawCurrent Party Good Technology Instrument}
    {cohort : List Party} {beneficiary : Party} {word : RawEvent Party Good Port Technology Instrument} {good : Good} :
    ReparationResult law before cohort beneficiary word good → ℚ
  | .compensation .. => compensationCash law (law.rawItems before word) beneficiary good
  | .repair .. => productiveNetFor law (law.rawItems before word) beneficiary good
  | .blocked _ => 0

theorem ReparationResult.credit_nonnegative
    {law : RawLaw Party Good Port Technology Instrument} {before : RawCurrent Party Good Technology Instrument}
    {cohort : List Party} {beneficiary : Party} {word : RawEvent Party Good Port Technology Instrument} {good : Good}
    (result : ReparationResult law before cohort beneficiary word good) : 0 ≤ result.credit := by
  cases result with
  | compensation _ _ positive => exact le_of_lt positive
  | repair _ _ _ positive => exact le_of_lt positive
  | blocked _ => exact le_rfl

def NonFinancialOperation (operation : Operation Party Good Technology Instrument) : Prop :=
  match operation with
  | .issue .. | .assign .. | .settle .. => False
  | _ => True

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem compensation_has_no_new_or_retired_financial_claim
    (cohort : List Party) (beneficiary : Party) (request : Request Party Good Port Technology Instrument)
    (source : compensationOperation cohort beneficiary request) : NonFinancialOperation request.operation := by
  cases operation : request.operation <;> simp_all [compensationOperation,NonFinancialOperation]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem local_repair_has_no_new_or_retired_financial_claim
    (beneficiary : Party) (request : Request Party Good Port Technology Instrument)
    (source : localRepairOperation beneficiary request) : NonFinancialOperation request.operation := by
  cases operation : request.operation <;> simp_all [localRepairOperation,NonFinancialOperation]

theorem nonfinancial_word_keeps_every_original_claim
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (neutral : ∀ request ∈ word, NonFinancialOperation request.operation) :
    (law.next before word).claims = before.claims := by
  change (law.execute before 0 word).final.claims = before.claims
  have all : ∀ (current : RawCurrent Party Good Technology Instrument) (index : Nat),
      (law.execute current index word).final.claims = current.claims := by
    induction word with
    | nil => exact fun _ _ => rfl
    | cons request rest inherited =>
      intro current index
      have first : (law.step current request).claims = current.claims := by
        have nf := neutral request List.mem_cons_self
        by_cases valid : law.Valid current request
        · cases operation : request.operation <;>
            simp_all [NonFinancialOperation,RawLaw.step,RawLaw.paidStep,RawLaw.nextClaims]
        · exact congrArg RawCurrent.claims (law.rejected_preserves_current current request valid)
      change (law.execute (law.step current request) (index + 1) rest).final.claims = current.claims
      have later := inherited (fun request member => neutral request (List.mem_cons_of_mem _ member)) (law.step current request) (index + 1)
      exact later.trans first
  exact all before 0


theorem reparation_keeps_every_original_claim
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (cohort : List Party) (beneficiary : Party) (word : RawEvent Party Good Port Technology Instrument) (good : Good)
    (result : ReparationResult law before cohort beneficiary word good)
    (performed : 0 < result.credit) : (law.next before word).claims = before.claims := by
  apply nonfinancial_word_keeps_every_original_claim
  cases result with
  | compensation _ source _ => exact fun request member =>
      compensation_has_no_new_or_retired_financial_claim cohort beneficiary request (source request member)
  | repair _ _ source _ => exact fun request member =>
      local_repair_has_no_new_or_retired_financial_claim beneficiary request (source request member)
  | blocked _ => exact (not_lt_of_ge (le_refl 0) performed).elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
