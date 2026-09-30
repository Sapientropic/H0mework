import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Formation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open ResponsibilityLifecycle ComplementObservation
noncomputable section

private theorem anchor_ext {O : ComplementObservationCarrier} {Scope Lineage : Type}
    (left right : MinimalRegistrableSourceAnchor O Scope Lineage)
    (identity : left.identity = right.identity) (scope : left.scope = right.scope) (lineage : left.lineage = right.lineage) :
    left = right := by
  cases left
  cases right
  cases identity
  cases scope
  cases lineage
  rfl

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

def anchorEquiv :
    MinimalRegistrableSourceAnchor (observation original) (old 5) (old 6) ≃
      MinimalRegistrableSourceAnchor (observation output) (generated 5) (generated 6) where
  toFun := fun anchor => {
    identity := sorts 8 anchor.identity
    identity_ne_complement_identity := by
      intro same
      exact anchor.identity_ne_complement_identity ((sorts 8).injective (same.trans (p.complement_eq anchor.identity)))
    scope := sorts 5 anchor.scope
    lineage := sorts 6 anchor.lineage }
  invFun := fun anchor => {
    identity := (sorts 8).symm anchor.identity
    identity_ne_complement_identity := by
      intro same
      apply anchor.identity_ne_complement_identity
      exact ((sorts 8).apply_symm_apply anchor.identity).symm.trans
        ((congrArg (sorts 8) same).trans ((p.complement_eq ((sorts 8).symm anchor.identity)).symm.trans
          (congrArg output.complement ((sorts 8).apply_symm_apply anchor.identity))))
    scope := (sorts 5).symm anchor.scope
    lineage := (sorts 6).symm anchor.lineage }
  left_inv := fun anchor => anchor_ext _ _ ((sorts 8).symm_apply_apply anchor.identity)
    ((sorts 5).symm_apply_apply anchor.scope) ((sorts 6).symm_apply_apply anchor.lineage)
  right_inv := fun anchor => anchor_ext _ _ ((sorts 8).apply_symm_apply anchor.identity)
    ((sorts 5).apply_symm_apply anchor.scope) ((sorts 6).apply_symm_apply anchor.lineage)

theorem sourceAnchor_mapped (source : old 0) :
    anchorEquiv sorts families p ((vocabulary old left original).sourceAnchor source) =
      (vocabulary generated right output).sourceAnchor (sorts 0 source) :=
  anchor_ext _ _ (p.identity_eq source).symm (p.scope_eq source).symm (p.lineage_eq source).symm

def demandEquiv : ProducerDemand (vocabulary old left original) ≃ ProducerDemand (vocabulary generated right output) where
  toFun := fun demand => ⟨sorts 0 demand.sourceEvent, families 0 (demand.sourceEvent, PUnit.unit) demand.obstruction⟩
  invFun := fun demand =>
    let old := (obstructionEquiv sorts families).symm ⟨demand.sourceEvent, demand.obstruction⟩
    ⟨old.1, old.2⟩
  left_inv := by
    intro demand
    have same := (obstructionEquiv sorts families).symm_apply_apply ⟨demand.sourceEvent, demand.obstruction⟩
    exact congrArg (fun value : Σ source : old 0, left 0 (source, PUnit.unit) =>
      (⟨value.1, value.2⟩ : ProducerDemand (vocabulary old left original))) same
  right_inv := by
    intro demand
    have same := (obstructionEquiv sorts families).apply_symm_apply ⟨demand.sourceEvent, demand.obstruction⟩
    exact congrArg (fun value : Σ source : generated 0, right 0 (source, PUnit.unit) =>
      (⟨value.1, value.2⟩ : ProducerDemand (vocabulary generated right output))) same

include p in
theorem demand_content (demand : ProducerDemand (vocabulary old left original)) :
    (demandEquiv sorts families (original := original) (output := output) demand).content = sorts 1 demand.content :=
  p.content_eq demand.sourceEvent demand.obstruction

include p in
theorem demand_residual (demand : ProducerDemand (vocabulary old left original)) :
    (demandEquiv sorts families (original := original) (output := output) demand).residual = sorts 2 demand.residual :=
  p.residual_eq demand.sourceEvent demand.obstruction

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
