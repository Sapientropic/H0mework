import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Vocabulary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def origin (event : Financial.Event input) (content : Financial.IssuedClaim input) :
    ObligationOrigin (Financial.vocabulary input) event content →
      ObligationOrigin (vocabulary input depth count) (.legacy event) (.inl content)
  | .producerDemand demand _ _ => demand.obstruction.elim
  | .explicitCommitment receipt => .explicitCommitment receipt
  | .standingMandate impossible | .acceptedTask impossible |
      .activeDependency impossible | .protectedRisk impossible => impossible.elim

def assumption (event : Financial.Event input) (bearer : Financial.BirthActor input)
    (scope : Financial.InstructionOrigin input) :
    BearerAssumption (Financial.vocabulary input) event bearer scope →
      BearerAssumption (vocabulary input depth count) (.legacy event) (.inl bearer) (.original scope)
  | .accepted receipt => .accepted ⟨congrArg Sum.inl receipt.down.1, congrArg Origin.original receipt.down.2⟩
  | .mandated impossible => impossible.elim

def admission (content : Financial.IssuedClaim input)
    (receipt : AdmissionReceipt (Financial.vocabulary input) content) :
    AdmissionReceipt (vocabulary input depth count) (.inl content) where
  sourceEvent := .legacy receipt.sourceEvent
  admittedBearer := .inl receipt.admittedBearer
  admittedScope := .original receipt.admittedScope
  lineage := .original receipt.lineage
  anchor_scope_eq := congrArg Origin.original receipt.anchor_scope_eq
  anchor_lineage_eq := congrArg Origin.original receipt.anchor_lineage_eq
  origin := origin input depth count _ content receipt.origin
  authority := ⟨congrArg Origin.original receipt.authority.down⟩
  assumption := assumption input depth count _ _ _ receipt.assumption

def obligation (old : AdmittedObligation (Financial.vocabulary input)) :
    AdmittedObligation (vocabulary input depth count) where
  content := .inl old.content
  residual := old.residual
  bearer := .inl old.bearer
  beneficiary := .inl old.beneficiary
  scope := .original old.scope
  admission := admission input depth count old.content old.admission
  dischargeJurisdiction := ⟨congrArg Origin.original old.dischargeJurisdiction.down⟩

def payload (old : NativeAdmissionPayload (Financial.vocabulary input)) :
    NativeAdmissionPayload (vocabulary input depth count) where
  sourceEvent := .legacy old.sourceEvent
  content := .inl old.content
  residual := old.residual
  bearer := .inl old.bearer
  beneficiary := .inl old.beneficiary
  scope := .original old.scope
  lineage := .original old.lineage
  anchor_scope_eq := congrArg Origin.original old.anchor_scope_eq
  anchor_lineage_eq := congrArg Origin.original old.anchor_lineage_eq
  origin := origin input depth count _ _ old.origin
  authority := ⟨congrArg Origin.original old.authority.down⟩
  assumption := assumption input depth count _ _ _ old.assumption
  dischargeJurisdiction := ⟨congrArg Origin.original old.dischargeJurisdiction.down⟩

theorem payload_obligation (old : NativeAdmissionPayload (Financial.vocabulary input)) :
    (payload input depth count old).toObligation =
      obligation input depth count old.toObligation := rfl

theorem every_original_coordinate_is_retained (old : AdmittedObligation (Financial.vocabulary input)) :
    (obligation input depth count old).content = .inl old.content ∧
    (obligation input depth count old).residual = old.residual ∧
    (obligation input depth count old).bearer = .inl old.bearer ∧
    (obligation input depth count old).scope = .original old.scope ∧
    (obligation input depth count old).lineage = .original old.lineage ∧
    (obligation input depth count old).beneficiary = .inl old.beneficiary :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy
