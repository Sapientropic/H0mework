import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Progress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.MarketReadout

/-! The application statement is computed from an actual execution item.
Raw admission and application eligibility are separate: refusing to attest
a third-party settlement does not undo its material effects. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Settlement

open Distributed Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure StatementData (Actor Commodity Asset : Type) where
  position : Nat
  epoch : Nat
  signer : Actor
  instrument : Asset
  debtor : Actor
  creditor : Actor
  quantity : ℚ
  unit : Commodity
  rate : ℚ
  priorClaim : ℚ
  deriving DecidableEq

abbrev Statement := StatementData Party Good Instrument

def StatementData.scope {Actor Commodity Asset : Type} (statement : StatementData Actor Commodity Asset) : Scope :=
  ⟨statement.epoch, statement.position, 0⟩

def StatementData.amount {Actor Commodity Asset : Type} (statement : StatementData Actor Commodity Asset) : ℚ :=
  statement.quantity * statement.rate

inductive Rejection where
  | notSettlement | invalidRequest | wrongSigner | nonpositive | selfPayment
  deriving DecidableEq

inductive OutcomeData (Body : Type) where
  | rejected (reason : Rejection)
  | settled (statement : Body)
  deriving DecidableEq

variable (law : RawLaw Party Good Port Technology Instrument)

def classify (position : Nat) (item : ExecutionItem Party Good Port Technology Instrument) : OutcomeData (Statement (Party := Party) (Good := Good) (Instrument := Instrument)) :=
  match item.request.operation with
  | .settle instrument debtor creditor quantity =>
      if ¬ law.Valid item.before item.request then .rejected .invalidRequest
      else if item.request.signer ≠ debtor then .rejected .wrongSigner
      else if ¬ 0 < quantity then .rejected .nonpositive
      else if debtor = creditor then .rejected .selfPayment
      else .settled ⟨position, item.before.round, item.request.signer, instrument, debtor, creditor,
        quantity, law.settlementUnit instrument, law.settlementRate instrument,
        item.before.claims instrument debtor creditor⟩
  | _ => .rejected .notSettlement

def issuedAt (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (position : Nat) : Option (Statement (Party := Party) (Good := Good) (Instrument := Instrument)) :=
  match (law.rawItems initial word)[position]? with
  | none => none
  | some item => match classify law position item with
      | .rejected _ => none
      | .settled statement => some statement

def verify (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (candidate : Statement (Party := Party) (Good := Good) (Instrument := Instrument)) : Bool :=
  decide (issuedAt law initial word candidate.position = some candidate)

/-- The audit retains the original item even if its application claim fails. -/
def audit (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :=
  (law.rawItems initial word).mapIdx fun position item => (item, classify law position item)

theorem audit_preserves_every_original_request
    (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    (audit law initial word).map (fun row => row.1.request) = word := by
  calc
    (audit law initial word).map (fun row => row.1.request) =
        (law.rawItems initial word).map ExecutionItem.request := by
      apply List.ext_getElem?
      intro n
      simp [audit, Function.comp_def]
    _ = word := law.inventory_requests_exact initial 0 word

theorem issued_has_actual_paid_origin
    (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (position : Nat)
    (statement : Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (issued : issuedAt law initial word position = some statement) :
    ∃ item : ExecutionItem Party Good Port Technology Instrument,
      (law.rawItems initial word)[position]? = some item ∧
      statement.position = position ∧ statement.epoch = item.before.round ∧
      law.Valid item.before item.request ∧
      item.request.operation = .settle statement.instrument statement.debtor statement.creditor statement.quantity ∧
      item.request.signer = statement.signer ∧ statement.signer = statement.debtor ∧
      statement.debtor ≠ statement.creditor ∧ 0 < statement.quantity ∧
      statement.unit = law.settlementUnit statement.instrument ∧
      statement.rate = law.settlementRate statement.instrument ∧
      statement.priorClaim = item.before.claims statement.instrument statement.debtor statement.creditor := by
  unfold issuedAt at issued
  split at issued <;> try contradiction
  rename_i item actual
  split at issued <;> try contradiction
  rename_i produced classified
  have same := Option.some.inj issued
  subst statement
  unfold classify at classified
  split at classified <;> try contradiction
  rename_i instrument debtor creditor quantity operation
  split_ifs at classified with invalid signer nonpositive self
  have body := OutcomeData.settled.inj classified
  subst produced
  exact ⟨item, actual, rfl, rfl, by simpa only [not_not] using invalid,
    operation, rfl, by simpa only [not_not] using signer, self,
    by simpa only [not_not] using nonpositive, rfl, rfl, rfl⟩

theorem issued_payment_has_actual_material_and_claim_effects
    (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (position : Nat)
    (statement : Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (issued : issuedAt law initial word position = some statement) :
    ∃ item : ExecutionItem Party Good Port Technology Instrument,
      (law.rawItems initial word)[position]? = some item ∧ law.Valid item.before item.request ∧
      0 < statement.amount ∧ statement.quantity ≤ statement.priorClaim ∧
      flowAt (law.actualDebit item.before item.request) statement.debtor statement.unit = statement.amount ∧
      flowAt (law.actualCredit item.before item.request) statement.creditor statement.unit = statement.amount ∧
      (law.step item.before item.request).claims statement.instrument statement.debtor statement.creditor =
        statement.priorClaim - statement.quantity := by
  obtain ⟨item, actual, _, _, accepted, operation, _, _, _, positive, unit, rate, prior⟩ :=
    issued_has_actual_paid_origin law initial word position statement issued
  have inside := List.mem_of_getElem? actual
  let readout : MarketReadout law initial word := MarketReadout.ofAccepted item inside accepted
  have guard := accepted.2.2.1
  simp only [RawLaw.ClaimGuard, operation] at guard
  refine ⟨item, actual, accepted, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos positive (rate.symm ▸ guard.2.2)
  · simpa only [prior] using guard.2.1
  · simpa only [readout, MarketReadout.ofAccepted, unit, StatementData.amount, rate] using readout.quote_eq_actual_debit
      statement.instrument statement.debtor statement.creditor statement.quantity operation
  · simpa only [readout, MarketReadout.ofAccepted, unit, StatementData.amount, rate] using readout.quote_eq_actual_credit
      statement.instrument statement.debtor statement.creditor statement.quantity operation
  · rw [law.step_financial_balance, law.accepted_delta _ _ accepted]
    simp [RawLaw.claimDelta, operation, prior, sub_eq_add_neg]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Settlement
