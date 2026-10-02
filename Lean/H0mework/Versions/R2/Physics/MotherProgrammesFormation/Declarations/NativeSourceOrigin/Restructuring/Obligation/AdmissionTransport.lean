import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Admission

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open ResponsibilityLifecycle MotherRestructuringOrigin
noncomputable section

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

def authorityEquiv (source : old 0) :
    (vocabulary old left original).AdmissionAuthorityAt source (original.anchorScope source) ≃
      (vocabulary generated right output).AdmissionAuthorityAt (sorts 0 source) (output.anchorScope (sorts 0 source)) :=
  (families 6 (source, original.anchorScope source, PUnit.unit)).trans
    (Equiv.cast (congrArg ((vocabulary generated right output).AdmissionAuthorityAt (sorts 0 source))
      (p.scope_eq source).symm))

def registeredAssumptionEquiv (source : old 0) (bearer : old 3) :
    BearerAssumption (vocabulary old left original) source bearer (original.anchorScope source) ≃
      BearerAssumption (vocabulary generated right output) (sorts 0 source) (sorts 3 bearer) (output.anchorScope (sorts 0 source)) :=
  (assumptionEquiv sorts families (original := original) (output := output) source bearer (original.anchorScope source)).trans
    (Equiv.cast (congrArg (BearerAssumption (vocabulary generated right output) (sorts 0 source) (sorts 3 bearer))
      (p.scope_eq source).symm))

def admissionEquiv (content : old 1) :
    AdmissionReceipt (vocabulary old left original) content ≃ AdmissionReceipt (vocabulary generated right output) (sorts 1 content) :=
  (admissionBodyEquiv (vocabulary old left original) content).trans
    ((Equiv.sigmaCongr (sorts 0) (fun source => Equiv.sigmaCongr (sorts 3) (fun bearer =>
      Equiv.prodCongr (originEquiv sorts families p source content)
        (Equiv.prodCongr (authorityEquiv sorts families p source) (registeredAssumptionEquiv sorts families p source bearer))))).trans
      (admissionBodyEquiv (vocabulary generated right output) (sorts 1 content)).symm)

theorem admission_source (content : old 1) (receipt : AdmissionReceipt (vocabulary old left original) content) :
    (admissionEquiv sorts families p content receipt).sourceEvent = sorts 0 receipt.sourceEvent := by
  rcases receipt with ⟨source, bearer, scope, lineage, scopeEq, lineageEq, origin, authority, assumption⟩
  cases scopeEq
  cases lineageEq
  rfl

theorem admission_scope (content : old 1) (receipt : AdmissionReceipt (vocabulary old left original) content) :
    (admissionEquiv sorts families p content receipt).admittedScope = sorts 5 receipt.admittedScope := by
  rcases receipt with ⟨source, bearer, scope, lineage, scopeEq, lineageEq, origin, authority, assumption⟩
  cases scopeEq
  cases lineageEq
  exact p.scope_eq source

theorem admission_lineage (content : old 1) (receipt : AdmissionReceipt (vocabulary old left original) content) :
    (admissionEquiv sorts families p content receipt).lineage = sorts 6 receipt.lineage := by
  rcases receipt with ⟨source, bearer, scope, lineage, scopeEq, lineageEq, origin, authority, assumption⟩
  cases scopeEq
  cases lineageEq
  exact p.lineage_eq source

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
