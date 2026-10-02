import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Bodies

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
noncomputable section

theorem list_nonempty_iff {A C : Type} (e : A ≃ C) (values : List A) :
    values ≠ [] ↔ listEquiv e values ≠ [] :=
  ⟨fun nonempty same => nonempty ((listEquiv e).injective same),
    fun nonempty same => nonempty (congrArg (listEquiv e) same)⟩

theorem forall_members_iff {A C : Type} (e : A ≃ C) (values : List A) (P : A → Prop) (Q : C → Prop)
    (each : ∀ value, P value ↔ Q (e value)) :
    (∀ value, value ∈ values → P value) ↔ (∀ value, value ∈ listEquiv e values → Q value) := by
  constructor
  · intro all value member
    obtain ⟨original, member, same⟩ := List.mem_map.mp member
    exact same ▸ (each original).mp (all original member)
  · intro all value member
    exact (each value).mpr (all (e value) (List.mem_map.mpr ⟨value, member, rfl⟩))

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

theorem anchor_ownership_iff (source : old 0) (parent : AdmittedObligation (vocabulary old left original)) :
    (vocabulary old left original).sourceAnchor source = parent.sourceAnchor ↔
      (vocabulary generated right output).sourceAnchor (sorts 0 source) = (obligationEquiv sorts families p parent).sourceAnchor := by
  constructor
  · intro same
    exact (sourceAnchor_mapped sorts families p source).symm.trans
      ((congrArg (anchorEquiv sorts families p) same).trans (obligation_anchor sorts families p parent).symm)
  · intro same
    exact (anchorEquiv sorts families p).injective ((sourceAnchor_mapped sorts families p source).trans
      (same.trans (obligation_anchor sorts families p parent)))

theorem incidence_ownership_iff (source : old 0) (parent : AdmittedObligation (vocabulary old left original)) :
    (vocabulary old left original).sourceIncidence source = parent.sourceIncidence ↔
      (vocabulary generated right output).sourceIncidence (sorts 0 source) = (obligationEquiv sorts families p parent).sourceIncidence := by
  constructor
  · intro same
    exact (p.incidence_eq source).trans ((congrArg (sorts 7) same).trans (obligation_incidence sorts families p parent).symm)
  · intro same
    exact (sorts 7).injective ((p.incidence_eq source).symm.trans (same.trans (obligation_incidence sorts families p parent)))

theorem debt_lineage_iff (parent child : AdmittedObligation (vocabulary old left original)) :
    SameDebtLineage parent child ↔ SameDebtLineage (obligationEquiv sorts families p parent) (obligationEquiv sorts families p child) := by
  constructor
  · intro same
    exact (obligation_lineage sorts families p parent).trans
      ((congrArg (sorts 6) same).trans (obligation_lineage sorts families p child).symm)
  · intro same
    exact (sorts 6).injective ((obligation_lineage sorts families p parent).symm.trans
      (same.trans (obligation_lineage sorts families p child)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
