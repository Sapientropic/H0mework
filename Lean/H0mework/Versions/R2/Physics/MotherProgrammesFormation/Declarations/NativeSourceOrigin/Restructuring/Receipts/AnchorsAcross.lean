import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
noncomputable section

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

include p in
private theorem complement_back (point : generated 8) :
    (sorts 8).symm (output.complement point) = original.complement ((sorts 8).symm point) := by
  apply (sorts 8).injective
  exact ((sorts 8).apply_symm_apply _).trans
    ((congrArg output.complement ((sorts 8).apply_symm_apply point)).symm.trans
      (p.complement_eq ((sorts 8).symm point)))

variable {a b : MinimalRegistrableSourceAnchor (observation original) (old 5) (old 6)}

def anchorForward (transport : SourceAnchorTransport a b) :
    SourceAnchorTransport (anchorEquiv sorts families p a) (anchorEquiv sorts families p b) where
  toFun := fun point => sorts 8 (transport.toFun ((sorts 8).symm point))
  injective := (sorts 8).injective.comp (transport.injective.comp (sorts 8).symm.injective)
  map_identity := by
    change sorts 8 (transport.toFun ((sorts 8).symm (sorts 8 a.identity))) = sorts 8 b.identity
    exact (congrArg (fun value : old 8 => sorts 8 (transport.toFun value)) ((sorts 8).symm_apply_apply a.identity)).trans
      (congrArg (sorts 8) transport.map_identity)
  map_complement := by
    intro point
    change sorts 8 (transport.toFun ((sorts 8).symm (output.complement point))) =
      output.complement (sorts 8 (transport.toFun ((sorts 8).symm point)))
    exact (congrArg (fun value : old 8 => sorts 8 (transport.toFun value)) (complement_back sorts families p point)).trans
      ((congrArg (sorts 8) (transport.map_complement ((sorts 8).symm point))).trans
        (p.complement_eq (transport.toFun ((sorts 8).symm point))).symm)
  scope_eq := congrArg (sorts 5) transport.scope_eq
  lineage_eq := congrArg (sorts 6) transport.lineage_eq

def anchorBackward (transport : SourceAnchorTransport (anchorEquiv sorts families p a) (anchorEquiv sorts families p b)) :
    SourceAnchorTransport a b where
  toFun := fun point => (sorts 8).symm (transport.toFun (sorts 8 point))
  injective := (sorts 8).symm.injective.comp (transport.injective.comp (sorts 8).injective)
  map_identity := (congrArg (sorts 8).symm transport.map_identity).trans ((sorts 8).symm_apply_apply b.identity)
  map_complement := by
    intro point
    change (sorts 8).symm (transport.toFun (sorts 8 (original.complement point))) =
      original.complement ((sorts 8).symm (transport.toFun (sorts 8 point)))
    exact (congrArg (fun value : generated 8 => (sorts 8).symm (transport.toFun value)) (p.complement_eq point).symm).trans
      ((congrArg (sorts 8).symm (transport.map_complement (sorts 8 point))).trans (complement_back sorts families p _))
  scope_eq := (sorts 5).injective transport.scope_eq
  lineage_eq := (sorts 6).injective transport.lineage_eq

private theorem transport_ext (first second : SourceAnchorTransport a b) (same : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  cases same
  rfl

def anchorTransportEquiv : SourceAnchorTransport a b ≃
    SourceAnchorTransport (anchorEquiv sorts families p a) (anchorEquiv sorts families p b) where
  toFun := anchorForward sorts families p
  invFun := anchorBackward sorts families p
  left_inv := fun transport => transport_ext _ _ (by
    funext point
    change (sorts 8).symm (sorts 8 (transport.toFun ((sorts 8).symm (sorts 8 point)))) = transport.toFun point
    exact ((sorts 8).symm_apply_apply _).trans (congrArg transport.toFun ((sorts 8).symm_apply_apply point)))
  right_inv := fun transport => transport_ext _ _ (by
    funext point
    change sorts 8 ((sorts 8).symm (transport.toFun (sorts 8 ((sorts 8).symm point)))) = transport.toFun point
    exact ((sorts 8).apply_symm_apply _).trans (congrArg transport.toFun ((sorts 8).apply_symm_apply point)))

def obligationAnchorTransport (parent child : AdmittedObligation (vocabulary old left original)) :
    SourceAnchorTransport parent.sourceAnchor child.sourceAnchor ≃
      SourceAnchorTransport (obligationEquiv sorts families p parent).sourceAnchor
        (obligationEquiv sorts families p child).sourceAnchor :=
  (anchorTransportEquiv sorts families p).trans (Equiv.cast (congrArg₂ SourceAnchorTransport
    (obligation_anchor sorts families p parent).symm (obligation_anchor sorts families p child).symm))

def ownershipForward {source : old 0} {parent : AdmittedObligation (vocabulary old left original)}
    (ownership : SourceOwnsResponsibilityIncidence (vocabulary old left original) source parent) :
    SourceOwnsResponsibilityIncidence (vocabulary generated right output) (sorts 0 source)
      (obligationEquiv sorts families p parent) where
  anchor_eq := (sourceAnchor_mapped sorts families p source).symm.trans
    ((congrArg (anchorEquiv sorts families p) ownership.anchor_eq).trans (obligation_anchor sorts families p parent).symm)
  incidence_eq := (p.incidence_eq source).trans
    ((congrArg (sorts 7) ownership.incidence_eq).trans (obligation_incidence sorts families p parent).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
