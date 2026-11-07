import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Base

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def oldOrigin (row : WorldEntry root boundary) (original : (Original root).Obligation)
    {event : (Original root).base.SourceEvent} :
    ObligationOrigin (Original root).base event original.content →
      ObligationOrigin (base root boundary) (.inl event) (.old row original)
  | .producerDemand demand eventEq contentEq =>
      .producerDemand ⟨.inl demand.sourceEvent,⟨row,original,demand.obstruction,PLift.up contentEq⟩⟩
        (congrArg Sum.inl eventEq) rfl
  | .explicitCommitment receipt => .explicitCommitment receipt
  | .standingMandate receipt => .standingMandate receipt
  | .acceptedTask receipt => .acceptedTask receipt
  | .activeDependency receipt => .activeDependency receipt
  | .protectedRisk receipt => .protectedRisk receipt

def oldAssumption {event : (Original root).base.SourceEvent} {bearer : (Original root).base.Bearer}
    {scope : (Original root).base.Scope} :
    BearerAssumption (Original root).base event bearer scope →
      BearerAssumption (base root boundary) (.inl event) (.inl bearer) (.inl scope)
  | .accepted receipt => .accepted receipt
  | .mandated receipt => .mandated receipt

def oldObligation (row : WorldEntry root boundary) (original : (Original root).Obligation) :
    AdmittedObligation (base root boundary) where
  content := .old row original
  residual := .inl original.residual
  bearer := .inl original.bearer
  beneficiary := .inl original.beneficiary
  scope := .inl original.scope
  admission := {
    sourceEvent := .inl original.admission.sourceEvent
    admittedBearer := .inl original.admission.admittedBearer
    admittedScope := .inl original.admission.admittedScope
    lineage := .inl original.admission.lineage
    anchor_scope_eq := congrArg Sum.inl original.admission.anchor_scope_eq
    anchor_lineage_eq := congrArg Sum.inl original.admission.anchor_lineage_eq
    origin := oldOrigin root boundary row original original.admission.origin
    authority := original.admission.authority
    assumption := oldAssumption root boundary original.admission.assumption }
  dischargeJurisdiction := original.dischargeJurisdiction

theorem every_original_admission_field_survives (row : WorldEntry root boundary)
    (original : (Original root).Obligation) :
    originalAdmission root boundary (oldObligation root boundary row original).content = some original := rfl

def oldAnchorTransport
    {first second : MinimalRegistrableSourceAnchor (Original root).base.SourceObservation
      (Original root).base.Scope (Original root).base.Lineage}
    (receipt : SourceAnchorTransport first second) :
    SourceAnchorTransport (oldAnchor root boundary first) (oldAnchor root boundary second) where
  toFun := Sum.map receipt.toFun id
  injective := Sum.map_injective.mpr ⟨receipt.injective,Function.injective_id⟩
  map_identity := congrArg Sum.inl receipt.map_identity
  map_complement := by rintro (old | added); exact congrArg Sum.inl (receipt.map_complement old); rfl
  scope_eq := congrArg Sum.inl receipt.scope_eq
  lineage_eq := congrArg Sum.inl receipt.lineage_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
