import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Reciprocity

/-! A financial return is an original controlled material advance, an
original issue (and optional assignment), and an actual settlement returning
more of that same good.  These are relation-level source observations, not
a replacement allocator or a certificate that a particular loan is closed. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

structure ReturnPath where
  issuance : OriginalItem law current word
  assignment : Option (OriginalItem law current word)
  payment : OriginalItem law current word

namespace ReturnPath

def claimOrigin (path : ReturnPath law current word) : OriginalItem law current word :=
  path.assignment.getD path.issuance

def Advance (access : AccessProposal law current word) : Prop :=
  law.Valid access.access.val.before access.access.val.request ∧
  access.access.val.request.signer = access.controller law current word ∧
  access.access.val.request.consents = [] ∧
  law.stockPort access.access.val.before.technology (access.controller law current word) access.accessGood = access.port ∧
  match access.access.val.request.operation with
  | .transfer sender receiver _ => sender = access.controller law current word ∧ receiver = access.accessHolder ∧
      sender ≠ receiver ∧
      0 < flowAt (law.actualDebit access.access.val.before access.access.val.request) sender access.accessGood ∧
      flowAt (law.actualCredit access.access.val.before access.access.val.request) receiver access.accessGood =
        flowAt (law.actualDebit access.access.val.before access.access.val.request) sender access.accessGood
  | _ => False

instance (access : AccessProposal law current word) : Decidable (Advance law current word access) := by
  unfold Advance
  cases access.access.val.request.operation <;> infer_instance

def ClaimPath (access : AccessProposal law current word) (path : ReturnPath law current word) : Prop :=
  law.Valid path.issuance.val.before path.issuance.val.request ∧
  law.Valid path.payment.val.before path.payment.val.request ∧
  access.access.val.index < path.payment.val.index ∧
  law.controller path.payment.val.before.technology access.port = access.controller law current word ∧
  match path.issuance.val.request.operation, path.payment.val.request.operation with
  | .issue instrument debtor firstHolder issued, .settle paidInstrument payer recipient paid =>
      paidInstrument = instrument ∧ payer = debtor ∧ recipient = access.controller law current word ∧
      0 < paid ∧ payer ≠ recipient ∧ path.issuance.val.index < path.payment.val.index ∧
      match path.assignment with
      | none => debtor = access.accessHolder ∧ firstHolder = recipient ∧ paid ≤ issued
      | some assigned => law.Valid assigned.val.before assigned.val.request ∧
          path.issuance.val.index < assigned.val.index ∧ assigned.val.index < path.payment.val.index ∧
          firstHolder = access.accessHolder ∧
          match assigned.val.request.operation with
          | .assign assignedInstrument assignedDebtor sender holder quantity =>
              assignedInstrument = instrument ∧ assignedDebtor = debtor ∧ sender = firstHolder ∧
              holder = recipient ∧ paid ≤ quantity ∧ quantity ≤ issued
          | _ => False
  | _, _ => False

instance (access : AccessProposal law current word) (path : ReturnPath law current word) :
    Decidable (ClaimPath law current word access path) := by
  unfold ClaimPath
  cases path.issuance.val.request.operation <;> cases path.payment.val.request.operation <;>
    dsimp only <;> try infer_instance
  cases path.assignment with
  | none => dsimp only; infer_instance
  | some assigned =>
      dsimp only
      cases assigned.val.request.operation <;> dsimp only <;> infer_instance

def Checks (access : AccessProposal law current word) (path : ReturnPath law current word) : Prop :=
  Advance law current word access ∧ ClaimPath law current word access path ∧
  flowAt (law.actualDebit access.access.val.before access.access.val.request)
      (access.controller law current word) access.accessGood <
    flowAt (law.actualCredit path.payment.val.before path.payment.val.request)
      (access.controller law current word) access.accessGood

instance (access : AccessProposal law current word) (path : ReturnPath law current word) :
    Decidable (Checks law current word access path) := by unfold Checks; infer_instance

def Aligned (path : ReturnPath law current word) : ReciprocityProposal law current word → Prop
  | .claim item => item.val.index = (path.claimOrigin law current word).val.index
  | _ => False

instance (path : ReturnPath law current word) (reciprocity : ReciprocityProposal law current word) :
    Decidable (Aligned law current word path reciprocity) := by
  cases reciprocity <;> unfold Aligned <;> infer_instance

omit [DecidableEq Port] in
theorem aligned_is_exact_original_claim (path : ReturnPath law current word)
    (reciprocity : ReciprocityProposal law current word)
    (aligned : Aligned law current word path reciprocity) :
    reciprocity.financialOrigin law current word = some (path.claimOrigin law current word) := by
  cases reciprocity with
  | claim item =>
      have same := original_index_injective law current word aligned
      exact congrArg some same
  | _ => cases aligned

omit [DecidableEq Port] in
theorem actual_financial_return_has_original_payment (access : AccessProposal law current word)
    (path : ReturnPath law current word) (checked : Checks law current word access path) :
    law.Valid path.payment.val.before path.payment.val.request ∧
    ∃ instrument debtor principal, path.payment.val.request.operation =
      .settle instrument debtor (access.controller law current word) principal ∧
      0 < principal ∧
      flowAt (law.actualDebit access.access.val.before access.access.val.request)
          (access.controller law current word) access.accessGood <
        flowAt (law.actualCredit path.payment.val.before path.payment.val.request)
          (access.controller law current word) access.accessGood := by
  refine ⟨checked.2.1.2.1, ?_⟩
  have matched := checked.2.1.2.2.2.2
  cases issued : path.issuance.val.request.operation <;>
    cases paid : path.payment.val.request.operation <;> simp only [issued, paid] at matched
  rcases matched with ⟨_sameInstrument, _sameDebtor, rfl, positive, _rest⟩
  exact ⟨_, _, _, rfl, positive, checked.2.2⟩

end ReturnPath

/-- Only original financial requests become candidates; no permission or
claim certificate is accepted from a caller. -/
def returnPaths : List (ReturnPath law current word) :=
  (law.rawItems current word).attach.flatMap (fun payment =>
    match payment.val.request.operation with
    | .settle .. => (law.rawItems current word).attach.flatMap (fun issued =>
        match issued.val.request.operation with
        | .issue .. => ⟨issued, none, payment⟩ ::
            (law.rawItems current word).attach.filterMap (fun assigned =>
              match assigned.val.request.operation with
              | .assign .. => some ⟨issued, some assigned, payment⟩
              | _ => none)
        | _ => [])
    | _ => [])

#print axioms ReturnPath.aligned_is_exact_original_claim
#print axioms ReturnPath.actual_financial_return_has_original_payment

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial
