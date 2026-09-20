/-
  Proposition 510: endpoint-signature faithfulness of the concrete support
  labeling.

  P508 labels each concrete canonical off-diagonal matrix position by the
  existing P459 matter/Higgs schedule.  The definition is intentionally
  totalized by a catch-all branch, because a plain function value cannot carry
  the subtype proof that the endpoint pair is canonical.

  This file proves that the catch-all branch is semantically inert on the
  concrete support: the label of every canonical matrix position preserves the
  actual endpoint signature, and any endpoint-signature-preserving concrete
  labeling is pointwise equal to the current one.

  Boundary: this still does not derive the physical endpoint-signature table
  from SU(7) representation theory.  It proves that, after the endpoint table
  is supplied, the concrete support labeling is forced on the actual concrete
  support and has no extra fallback freedom.
-/

import H0mework.Physics.RepresentationSources.P509

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta
open GaugeProjection.ConcreteBlockDiagonal

/-! ## Concrete endpoint-signature preservation -/

/-- The concrete endpoint signature of a canonical matrix support position. -/
def concreteEndpointSignature
    (p : ConcreteCanonicalOffDiagonalIndexPair) :
    SU7CarrierBlock × SU7CarrierBlock :=
  (blockOfSMBlockIndex p.1.1, blockOfSMBlockIndex p.1.2)

/-- THEOREM 1: the concrete support label preserves the actual concrete
endpoint signature.  Thus the totalized catch-all branch of
`concreteMatterSlotOfIndexPair` is not part of the semantics on
`ConcreteCanonicalOffDiagonalIndexPair`. -/
theorem concreteMatterSlotOfIndexPair_preserves_endpointSignature
    (p : ConcreteCanonicalOffDiagonalIndexPair) :
    generatedSlotEndpointSignature (concreteMatterSlotOfIndexPair p) =
      concreteEndpointSignature p := by
  have hp := p.2
  cases hsrc : blockOfSMBlockIndex p.1.1 <;>
    cases htgt : blockOfSMBlockIndex p.1.2 <;>
    simp [concreteEndpointSignature, concreteMatterSlotOfIndexPair,
      generatedSlotEndpointSignature, IsCanonicalOffDiagonalPair,
      SU7CarrierBlock.code, hsrc, htgt] at hp ⊢

/-- THEOREM 2: any concrete support labeling that preserves endpoint
signatures is pointwise equal to the P508 label. -/
theorem concreteEndpointSignature_preserving_label_unique_pointwise
    (f : ConcreteCanonicalOffDiagonalIndexPair -> MatterSlot)
    (hf : ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
      generatedSlotEndpointSignature (f p) = concreteEndpointSignature p) :
    ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
      f p = concreteMatterSlotOfIndexPair p := by
  intro p
  apply generatedSlotEndpointSignature_injective
  rw [hf p, concreteMatterSlotOfIndexPair_preserves_endpointSignature p]

/-- THEOREM 3: equivalently, the concrete endpoint-signature-preserving label
function is unique. -/
theorem concreteEndpointSignature_preserving_label_unique
    (f : ConcreteCanonicalOffDiagonalIndexPair -> MatterSlot)
    (hf : ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
      generatedSlotEndpointSignature (f p) = concreteEndpointSignature p) :
    f = concreteMatterSlotOfIndexPair := by
  funext p
  exact concreteEndpointSignature_preserving_label_unique_pointwise f hf p

/-- THEOREM 4: the concrete label is the unique endpoint-preserving label on
the concrete canonical support and remains trace-faithful through P509. -/
structure ConcreteSupportEndpointSignatureFaithfulnessCertificate : Prop where
  preserves_endpoint_signature :
    ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
      generatedSlotEndpointSignature (concreteMatterSlotOfIndexPair p) =
        concreteEndpointSignature p
  unique_pointwise :
    ∀ f : ConcreteCanonicalOffDiagonalIndexPair -> MatterSlot,
      (∀ p : ConcreteCanonicalOffDiagonalIndexPair,
        generatedSlotEndpointSignature (f p) = concreteEndpointSignature p) ->
      ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
        f p = concreteMatterSlotOfIndexPair p
  unique_label :
    ∀ f : ConcreteCanonicalOffDiagonalIndexPair -> MatterSlot,
      (∀ p : ConcreteCanonicalOffDiagonalIndexPair,
        generatedSlotEndpointSignature (f p) = concreteEndpointSignature p) ->
      f = concreteMatterSlotOfIndexPair
  trace_faithful :
    ConcreteSupportTraceInputCertificate

/-- THEOREM 5: concrete support labels are forced by endpoint signature and
feed the same one-loop trace input. -/
theorem concreteSupportEndpointSignatureFaithfulnessCertificate :
    ConcreteSupportEndpointSignatureFaithfulnessCertificate where
  preserves_endpoint_signature :=
    concreteMatterSlotOfIndexPair_preserves_endpointSignature
  unique_pointwise :=
    concreteEndpointSignature_preserving_label_unique_pointwise
  unique_label := concreteEndpointSignature_preserving_label_unique
  trace_faithful := concreteSupportTraceInputCertificate

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
