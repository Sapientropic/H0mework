import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Transport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open ResponsibilityLifecycle
noncomputable section

variable (V : ResponsibilityLifecycle.Vocabulary.{0}) (content : V.Content)

abbrev AdmissionBody := Σ source : V.SourceEvent, Σ bearer : V.Bearer,
  ObligationOrigin V source content ×
    V.AdmissionAuthorityAt source (V.sourceAnchor source).scope ×
      BearerAssumption V source bearer (V.sourceAnchor source).scope

def admissionBody (receipt : AdmissionReceipt V content) : AdmissionBody V content := by
  rcases receipt with ⟨source, bearer, scope, lineage, scopeEq, lineageEq, origin, authority, assumption⟩
  cases scopeEq
  cases lineageEq
  exact ⟨source, bearer, origin, authority, assumption⟩

def admissionFromBody (body : AdmissionBody V content) : AdmissionReceipt V content where
  sourceEvent := body.1
  admittedBearer := body.2.1
  admittedScope := (V.sourceAnchor body.1).scope
  lineage := (V.sourceAnchor body.1).lineage
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := body.2.2.1
  authority := body.2.2.2.1
  assumption := body.2.2.2.2

def admissionBodyEquiv : AdmissionReceipt V content ≃ AdmissionBody V content where
  toFun := admissionBody V content
  invFun := admissionFromBody V content
  left_inv := by
    rintro ⟨source, bearer, scope, lineage, scopeEq, lineageEq, origin, authority, assumption⟩
    cases scopeEq
    cases lineageEq
    rfl
  right_inv := by rintro ⟨source, bearer, origin, authority, assumption⟩; rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
