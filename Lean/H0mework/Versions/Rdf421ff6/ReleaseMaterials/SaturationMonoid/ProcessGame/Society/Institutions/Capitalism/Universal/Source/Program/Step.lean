import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Raw
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local instruction execution with real stock and claim debits

Every material change comes from this instruction's computed finite debit
and credit.  Issuance changes financial claims alone.  Repayment extinguishes
only an existing claim and simultaneously transfers its source-fixed payment.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

abbrev Flow (Party Good : Type u) := List ((Party × Good) × ℚ)

def locate (party : Party) (bundle : Bundle Good) : Flow Party Good :=
  bundle.map (fun item => ((party, item.1), item.2))

def flowAt (flow : Flow Party Good) (party : Party) (good : Good) : ℚ :=
  amount (Party × Good) flow (party, good)

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument)

def debit (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Flow Party Good :=
  match request.operation with
  | .produce operator => locate operator
      ((law.technique current.technology operator).inputs ++
        (law.technique current.technology operator).maintenance)
  | .transfer sender _ goods => locate sender goods
  | .use bearer goods _ => locate bearer goods
  | .settle instrument debtor _ quantity =>
      locate debtor [(law.settlementUnit instrument, quantity * law.settlementRate instrument)]
  | .revise operator technology => locate operator (law.revisionCost current.technology technology)
  | .issue _ _ _ _ | .assign _ _ _ _ _ | .present => []

def credit (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Flow Party Good :=
  match request.operation with
  | .produce operator => locate operator (law.technique current.technology operator).outputs
  | .transfer _ recipient goods => locate recipient goods
  | .settle instrument _ creditor quantity =>
      locate creditor [(law.settlementUnit instrument, quantity * law.settlementRate instrument)]
  | .use _ _ _ | .revise _ _ | .issue _ _ _ _ | .assign _ _ _ _ _ | .present => []

def requiredPorts (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : List Port :=
  request.gates ++
    (law.debit current request).map (fun item =>
      law.stockPort current.technology item.1.1 item.1.2) ++ match request.operation with
    | .produce operator => (law.technique current.technology operator).requiredPorts
    | .issue instrument _ _ _ | .assign instrument _ _ _ _ |
        .settle instrument _ _ _ => [law.issuerPort instrument]
    | .revise _ _ => [law.revisionPort current.technology]
    | _ => []

def SignerMatches (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .assign _ _ sender _ _ => request.signer = sender
  | .issue _ issuer _ _ => request.signer = issuer
  | .produce _ | .transfer _ _ _ | .use _ _ _ | .settle _ _ _ _ | .revise _ _ | .present => True

def ClaimGuard (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .issue _ _ _ quantity => 0 ≤ quantity
  | .assign instrument issuer sender _ quantity =>
      0 ≤ quantity ∧ quantity ≤ current.claims instrument issuer sender
  | .settle instrument debtor creditor quantity =>
      0 ≤ quantity ∧ quantity ≤ current.claims instrument debtor creditor ∧
        0 < law.settlementRate instrument
  | .use bearer goods .necessity => goods = law.necessities current bearer
  | .use bearer goods .maintenance => goods = law.mandatoryMaintenance current bearer
  | _ => True

def Valid (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Prop :=
  (SignerMatches request ∧ law.operationAllowed current request = true) ∧
  (∀ port ∈ law.requiredPorts current request,
    law.allowed current.technology port request.signer = true ∨
      law.controller current.technology port ∈ request.consents) ∧
  law.ClaimGuard current request ∧
  NonnegativeBundle (Party × Good) (law.debit current request) ∧
  NonnegativeBundle (Party × Good) (law.credit current request) ∧
  (∀ item ∈ law.debit current request,
    flowAt (law.debit current request) item.1.1 item.1.2 ≤ current.stock item.1.1 item.1.2)

instance (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Decidable (law.Valid current request) := by
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  unfold Valid SignerMatches ClaimGuard
  cases operation with
  | use _ _ purpose => cases purpose <;> infer_instance
  | _ => infer_instance

def nextClaims (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Instrument → Party → Party → ℚ :=
  match request.operation with
  | .issue instrument issuer beneficiary quantity => fun code debtor creditor =>
      current.claims code debtor creditor +
        if (code, debtor, creditor) = (instrument, issuer, beneficiary) then quantity else 0
  | .assign instrument issuer sender recipient quantity => fun code debtor creditor =>
      current.claims code debtor creditor -
        (if (code, debtor, creditor) = (instrument, issuer, sender) then quantity else 0) +
        (if (code, debtor, creditor) = (instrument, issuer, recipient) then quantity else 0)
  | .settle instrument debtor creditor quantity => fun code oldDebtor oldCreditor =>
      current.claims code oldDebtor oldCreditor -
        if (code, oldDebtor, oldCreditor) = (instrument, debtor, creditor) then quantity else 0
  | _ => current.claims

def paidStep (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    RawCurrent Party Good Technology Instrument where
  stock := fun party good => current.stock party good - flowAt (law.debit current request) party good +
    flowAt (law.credit current request) party good
  claims := nextClaims current request
  technology := match request.operation with
    | .revise _ technology => technology
    | _ => current.technology
  clock := current.clock
  round := current.round

def step (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    RawCurrent Party Good Technology Instrument :=
  if law.Valid current request then law.paidStep current request else current

def actualDebit (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Flow Party Good :=
  if law.Valid current request then law.debit current request else []

def actualCredit (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Flow Party Good :=
  if law.Valid current request then law.credit current request else []

theorem rejected_preserves_current (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (rejected : ¬ law.Valid current request) : law.step current request = current := by
  simp [step, rejected]

theorem material_step_balance (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (party : Party) (good : Good) :
    (law.step current request).stock party good + flowAt (law.actualDebit current request) party good =
      current.stock party good + flowAt (law.actualCredit current request) party good := by
  by_cases accepted : law.Valid current request
  · simp only [step, actualDebit, actualCredit, if_pos accepted, paidStep]
    ring
  · simp [step, actualDebit, actualCredit, accepted, flowAt, amount]

theorem issuance_creates_no_material (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (instrument : Instrument) (issuer beneficiary : Party) (quantity : ℚ)
    (kind : request.operation = .issue instrument issuer beneficiary quantity) :
    (law.step current request).stock = current.stock := by
  by_cases accepted : law.Valid current request
  · funext party good
    simp [step, accepted, paidStep, debit, credit, kind, flowAt, amount]
  · rw [law.rejected_preserves_current current request accepted]

theorem presentation_preserves_material_and_claims
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (kind : request.operation = .present) : law.step current request = current := by
  by_cases accepted : law.Valid current request
  · cases current
    simp [step, accepted, paidStep, debit, credit, nextClaims, kind, flowAt, amount]
  · exact law.rejected_preserves_current current request accepted

end RawLaw

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
