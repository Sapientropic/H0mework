import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.AdmissionTransport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open ResponsibilityLifecycle MotherRestructuringOrigin
noncomputable section

abbrev ObligationBody (V : ResponsibilityLifecycle.Vocabulary.{0}) :=
  Σ content : V.Content, Σ _residual : V.Residual, Σ _bearer : V.Bearer, Σ _beneficiary : V.ProtectedInterest,
    Σ scope : V.Scope, AdmissionReceipt V content × V.DischargeJurisdiction content scope

def obligationBodyEquiv (V : ResponsibilityLifecycle.Vocabulary.{0}) : AdmittedObligation V ≃ ObligationBody V where
  toFun := fun value => ⟨value.content, value.residual, value.bearer, value.beneficiary, value.scope, value.admission, value.dischargeJurisdiction⟩
  invFun := fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩
  left_inv := fun value => by cases value; rfl
  right_inv := fun value => by rcases value with ⟨_, _, _, _, _, _, _⟩; rfl

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

def obligationEquiv : AdmittedObligation (vocabulary old left original) ≃ AdmittedObligation (vocabulary generated right output) :=
  (obligationBodyEquiv (vocabulary old left original)).trans
    ((Equiv.sigmaCongr (sorts 1) (fun content => Equiv.sigmaCongr (sorts 2) (fun _ =>
      Equiv.sigmaCongr (sorts 3) (fun _ => Equiv.sigmaCongr (sorts 4) (fun _ =>
        Equiv.sigmaCongr (sorts 5) (fun scope => Equiv.prodCongr (admissionEquiv sorts families p content)
          (families 9 (content, scope, PUnit.unit)))))))).trans (obligationBodyEquiv (vocabulary generated right output)).symm)

theorem obligation_source (value : AdmittedObligation (vocabulary old left original)) :
    (obligationEquiv sorts families p value).admission.sourceEvent = sorts 0 value.admission.sourceEvent :=
  admission_source sorts families p value.content value.admission

theorem obligation_lineage (value : AdmittedObligation (vocabulary old left original)) :
    (obligationEquiv sorts families p value).lineage = sorts 6 value.lineage :=
  admission_lineage sorts families p value.content value.admission

theorem obligation_anchor (value : AdmittedObligation (vocabulary old left original)) :
    (obligationEquiv sorts families p value).sourceAnchor = anchorEquiv sorts families p value.sourceAnchor := by
  exact (congrArg (vocabulary generated right output).sourceAnchor (obligation_source sorts families p value)).trans
    (sourceAnchor_mapped sorts families p value.admission.sourceEvent).symm

theorem obligation_incidence (value : AdmittedObligation (vocabulary old left original)) :
    (obligationEquiv sorts families p value).sourceIncidence = sorts 7 value.sourceIncidence :=
  (congrArg output.incidence (obligation_source sorts families p value)).trans (p.incidence_eq value.admission.sourceEvent)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
