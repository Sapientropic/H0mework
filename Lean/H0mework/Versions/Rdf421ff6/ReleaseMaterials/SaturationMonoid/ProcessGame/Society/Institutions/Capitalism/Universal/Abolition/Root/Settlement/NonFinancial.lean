import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def NonFinancialRequest (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .issue .. | .assign .. | .settle .. => False
  | _ => True

instance (request : Request Party Good Port Technology Instrument) : Decidable (NonFinancialRequest request) := by
  unfold NonFinancialRequest
  cases request.operation <;> infer_instance

def NonFinancial (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ request ∈ word, NonFinancialRequest request

instance (word : RawEvent Party Good Port Technology Instrument) : Decidable (NonFinancial word) := by
  unfold NonFinancial
  infer_instance

inductive FinancialCheck (word : RawEvent Party Good Port Technology Instrument) : Type
  | accepted (checked : NonFinancial word)
  | rejected (request : Request Party Good Port Technology Instrument)
      (present : request ∈ word) (financial : ¬ NonFinancialRequest request)

def checkFinancial : (word : RawEvent Party Good Port Technology Instrument) → FinancialCheck word
  | [] => .accepted (by simp [NonFinancial])
  | head :: tail =>
      if safe : NonFinancialRequest head then
        match checkFinancial tail with
        | .accepted tailSafe => .accepted (by
            intro request member
            rcases List.mem_cons.mp member with same | prior
            · exact same ▸ safe
            · exact tailSafe request prior)
        | .rejected request present financial =>
            .rejected request (List.mem_cons_of_mem _ present) financial
      else .rejected head List.mem_cons_self safe

omit [DecidableEq Good] in
theorem NonFinancialRequest.claim_delta_zero
    (request : Request Party Good Port Technology Instrument) (safe : NonFinancialRequest request)
    (instrument : Instrument) (debtor creditor : Party) : RawLaw.claimDelta request instrument debtor creditor = 0 := by
  cases observed : request.operation <;> simp_all [NonFinancialRequest, RawLaw.claimDelta]

theorem NonFinancialRequest.step_claims
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (safe : NonFinancialRequest request) :
    (law.step current request).claims = current.claims := by
  funext instrument debtor creditor
  rw [law.step_financial_balance]
  have delta : law.actualClaimDelta current request instrument debtor creditor = 0 := by
    unfold RawLaw.actualClaimDelta
    split
    · exact safe.claim_delta_zero request instrument debtor creditor
    · rfl
  rw [delta, add_zero]

theorem NonFinancial.execute_claims
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument) (safe : NonFinancial word) :
    (law.execute current index word).final.claims = current.claims := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail induction =>
      have head := safe request List.mem_cons_self
      have remaining : NonFinancial tail := fun item member => safe item (List.mem_cons_of_mem _ member)
      exact (induction (law.step current request) (index + 1) remaining).trans
        (head.step_claims law current request)

theorem NonFinancial.next_claims
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (safe : NonFinancial word) :
    (law.next current word).claims = current.claims :=
  safe.execute_claims law current 0 word

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement
