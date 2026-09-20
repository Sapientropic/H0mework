/-
  Proposition 511: concrete support as matter/Higgs component positions.

  P508 proves that the concrete canonical support fibers over the six
  matter/Higgs slots have the expected component multiplicities.  P510 proves
  that the concrete label is endpoint-signature forced on the actual support.

  This file upgrades the cardinality table into a carrier equivalence:

      concrete canonical matrix support
        ~= Σ slot, Fin (component multiplicity of slot).

  Thus the concrete information support is not merely the right size; it is
  equivalent to the finite carrier of typed matter/Higgs component positions.

  Boundary: the component multiplicity function still uses the P459/P508
  matter/Higgs typing.  This closes component-carrier faithfulness relative to
  that typing, not the deeper physical producer for the typing itself.
-/

import H0mework.Physics.SourceContracts.P510

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

/-! ## Component-position carrier -/

/-- The finite typed matter/Higgs component-position carrier: choose a
matter/Higgs slot, then choose one of its component positions. -/
abbrev MatterComponentPosition :=
  Σ s : MatterSlot, Fin (matterSlotComponentMultiplicity s)

/-- The concrete canonical support is equivalent to the sigma of its fibers
over matter/Higgs labels. -/
def concreteSupportFiberSigmaEquiv :
    ConcreteCanonicalOffDiagonalIndexPair ≃
      (Σ s : MatterSlot, ConcreteMatterSlotFiber s) where
  toFun p := ⟨concreteMatterSlotOfIndexPair p, ⟨p, rfl⟩⟩
  invFun q := q.2.1
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro q
    cases q with
    | mk s p =>
        cases p with
        | mk p hp =>
            cases hp
            rfl

/-- Upgrade each concrete fiber to a `Fin` component index using the P508
fiber-card theorem.  The choice of order inside a finite fiber is irrelevant;
the theorem needs only the canonical existence of a finite equivalence. -/
noncomputable def concreteSupportMatterComponentPositionEquiv :
    ConcreteCanonicalOffDiagonalIndexPair ≃ MatterComponentPosition :=
  concreteSupportFiberSigmaEquiv.trans
    (Equiv.sigmaCongrRight fun s =>
      Fintype.equivFinOfCardEq
        (concreteMatterSlotFiber_card_eq_componentMultiplicity s))

/-- THEOREM 1: the component-position carrier has total size `17`. -/
theorem matterComponentPosition_card :
    Fintype.card MatterComponentPosition = 17 := by
  rw [← Fintype.card_congr concreteSupportMatterComponentPositionEquiv,
    concreteCanonicalOffDiagonalIndexPair_card]

/-- THEOREM 2: the concrete-support/component-position equivalence preserves
the matter/Higgs slot label. -/
theorem concreteSupportMatterComponentPositionEquiv_preserves_slot
    (p : ConcreteCanonicalOffDiagonalIndexPair) :
    (concreteSupportMatterComponentPositionEquiv p).1 =
      concreteMatterSlotOfIndexPair p := by
  rfl

/-- Bundled receipt: the concrete information support is equivalent to typed
matter/Higgs component positions and remains endpoint/trace faithful. -/
structure ConcreteSupportComponentCarrierCertificate : Prop where
  component_equiv :
    Nonempty (ConcreteCanonicalOffDiagonalIndexPair ≃ MatterComponentPosition)
  component_card :
    Fintype.card MatterComponentPosition = 17
  preserves_slot :
    ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
      (concreteSupportMatterComponentPositionEquiv p).1 =
        concreteMatterSlotOfIndexPair p
  endpoint_signature_faithful :
    ConcreteSupportEndpointSignatureFaithfulnessCertificate

/-- THEOREM 3: concrete matrix support is the finite typed component carrier
for the current information/matter projection. -/
theorem concreteSupportComponentCarrierCertificate :
    ConcreteSupportComponentCarrierCertificate where
  component_equiv := ⟨concreteSupportMatterComponentPositionEquiv⟩
  component_card := matterComponentPosition_card
  preserves_slot := concreteSupportMatterComponentPositionEquiv_preserves_slot
  endpoint_signature_faithful :=
    concreteSupportEndpointSignatureFaithfulnessCertificate

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
