import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.ActualInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Relations.GeneratedRelationRole

/-! The right is computed from an actual gate and a source-legal disposition
of the source's existing material or claim.  This is a present disposition
right, not a profit label or an executed second event.  Actual invocation is
the original instruction's authorization.  Physical and financial effects
remain in their separate units. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder

open Program ProgrammeFace Relations

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

abbrev MaterialLot (Party Good : Type u) := (Party × Good) × ℚ
abbrev ClaimReference (Party Instrument : Type u) := Instrument × Party × Party

def claimReferences : Operation Party Good Technology Instrument → List (ClaimReference Party Instrument)
  | .issue instrument debtor holder _ | .settle instrument debtor holder _ =>
      [(instrument, debtor, holder)]
  | .assign instrument debtor oldHolder newHolder _ =>
      [(instrument, debtor, oldHolder), (instrument, debtor, newHolder)]
  | _ => []

inductive RightBasis (Party Good Port Technology Instrument : Type u)
  | material (side : EdgeSide) (lot : MaterialLot Party Good)
  | financial (original : ExecutionItem Party Good Port Technology Instrument)
      (reference : ClaimReference Party Instrument)

def dispositionContext (item : ExecutionItem Party Good Port Technology Instrument) : EdgeSide →
    RawCurrent Party Good Technology Instrument
  | .source => item.before
  | .target => law.step item.before item.request

def isProduction : Operation Party Good Technology Instrument → Bool
  | .produce _ => true
  | _ => false

def rightBases (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) :
    List (RightBasis Party Good Port Technology Instrument) :=
  ((law.actualDebit item.before item.request).map (RightBasis.material .source) ++
    (law.actualCredit item.before item.request).map (RightBasis.material .target)) ++
    (law.rawItems origin.1 origin.2).flatMap (fun original =>
      (claimReferences original.request.operation).map (RightBasis.financial original))

def materialDispositionRequest (controller : Party) (purpose : Port)
    (lot : MaterialLot Party Good) : Request Party Good Port Technology Instrument where
  signer := controller
  consents := []
  purpose := purpose
  gates := []
  operation := if lot.1.1 = controller then .use controller [(lot.1.2, lot.2)] .investment
    else .transfer lot.1.1 controller [(lot.1.2, lot.2)]

def claimDispositionRequest (current : RawCurrent Party Good Technology Instrument)
    (controller beneficiary : Party) (purpose : Port)
    (reference : ClaimReference Party Instrument) : Request Party Good Port Technology Instrument where
  signer := controller
  consents := []
  purpose := purpose
  gates := []
  operation := .assign reference.1 reference.2.1 controller beneficiary
    (current.claims reference.1 reference.2.1 controller)

def DisposalBasisAt (item : ExecutionItem Party Good Port Technology Instrument)
    (beneficiary : Party) (gate : Port) : RightBasis Party Good Port Technology Instrument → Prop
  | .material side lot =>
      0 < lot.2 ∧
      (match side with
        | .source => law.stockPort item.before.technology lot.1.1 lot.1.2 = gate
        | .target => isProduction item.request.operation = true) ∧
      law.controller (dispositionContext law item side).technology
          (law.stockPort (dispositionContext law item side).technology lot.1.1 lot.1.2) =
        law.controller item.before.technology gate ∧
      law.Valid (dispositionContext law item side)
        (materialDispositionRequest (law.controller item.before.technology gate) gate lot)
  | .financial original reference =>
      law.Valid original.before original.request ∧
      law.issuerPort reference.1 = gate ∧
      reference.2.2 = law.controller item.before.technology gate ∧
      0 < item.before.claims reference.1 reference.2.1 reference.2.2 ∧
      law.Valid item.before
        (claimDispositionRequest item.before (law.controller item.before.technology gate)
          beneficiary gate reference)

instance (item : ExecutionItem Party Good Port Technology Instrument)
    (beneficiary : Party) (gate : Port) (basis : RightBasis Party Good Port Technology Instrument) :
    Decidable (DisposalBasisAt law item beneficiary gate basis) := by
  cases basis with
  | material side lot =>
      cases side <;> unfold DisposalBasisAt <;> infer_instance
  | financial original reference => unfold DisposalBasisAt; infer_instance

def ExclusiveDisposalAt (item : ExecutionItem Party Good Port Technology Instrument)
    (beneficiary : Party) (gate : Port) (basis : RightBasis Party Good Port Technology Instrument) : Prop :=
  law.Valid item.before item.request ∧
  gate ∈ law.requiredPorts item.before item.request ∧
  law.allowed item.before.technology gate beneficiary = false ∧
  DisposalBasisAt law item beneficiary gate basis

instance (item : ExecutionItem Party Good Port Technology Instrument)
    (beneficiary : Party) (gate : Port) (basis : RightBasis Party Good Port Technology Instrument) :
    Decidable (ExclusiveDisposalAt law item beneficiary gate basis) := by
  unfold ExclusiveDisposalAt
  infer_instance

abbrev OriginalRight (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) (gate : Port) :=
  { basis : { basis : RightBasis Party Good Port Technology Instrument //
      basis ∈ rightBases law origin item } // ExclusiveDisposalAt law item beneficiary gate basis.val }

def disposalRights (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) (gate : Port) :
    List (OriginalRight law origin item beneficiary gate) :=
  (rightBases law origin item).attach.filterMap (fun basis =>
    if admissible : ExclusiveDisposalAt law item beneficiary gate basis.val then
      some ⟨basis, admissible⟩ else none)

omit [DecidableEq Port] in
theorem right_has_original_gate_and_disposition
    (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) (gate : Port)
    (right : OriginalRight law origin item beneficiary gate) :
    right.val.val ∈ rightBases law origin item ∧
    law.Valid item.before item.request ∧
    gate ∈ law.requiredPorts item.before item.request ∧
    law.allowed item.before.technology gate beneficiary = false ∧
    DisposalBasisAt law item beneficiary gate right.val.val :=
  ⟨right.val.property, right.property⟩

omit [DecidableEq Port] in
theorem right_uses_actual_authorization
    (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (present : item ∈ law.rawItems origin.1 origin.2) (beneficiary : Party) (gate : Port)
    (right : OriginalRight law origin item beneficiary gate) :
    authorizingAction law item gate ∈ actions law origin :=
  authorizingAction_in_original_occurrence law origin item present right.property.1 gate

omit [DecidableEq Port] in
theorem shared_permission_has_no_exclusive_right
    (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) (gate : Port)
    (shared : law.allowed item.before.technology gate beneficiary = true) :
    IsEmpty (OriginalRight law origin item beneficiary gate) :=
  ⟨fun right => Bool.noConfusion (shared.symm.trans right.property.2.2.1)⟩

theorem shared_permission_produces_empty_right_inventory
    (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) (gate : Port)
    (shared : law.allowed item.before.technology gate beneficiary = true) :
    disposalRights law origin item beneficiary gate = [] := by
  unfold disposalRights
  apply List.filterMap_eq_nil_iff.mpr
  intro basis _member
  apply dif_neg
  intro right
  exact Bool.noConfusion (shared.symm.trans right.2.2.1)

omit [DecidableEq Port] in
theorem public_disposition_refusal_has_no_material_right
    (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) (gate : Port)
    (side : EdgeSide) (lot : MaterialLot Party Good)
    (refused : ¬ law.Valid (dispositionContext law item side)
      (materialDispositionRequest (law.controller item.before.technology gate) gate lot)) :
    ¬ ExclusiveDisposalAt law item beneficiary gate (.material side lot) := by
  intro right
  exact refused right.2.2.2.2.2.2

#print axioms right_has_original_gate_and_disposition
#print axioms shared_permission_has_no_exclusive_right

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder
