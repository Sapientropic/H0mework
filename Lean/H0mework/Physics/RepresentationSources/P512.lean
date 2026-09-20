/-
  Proposition 512: current concrete information/matter carrier receipt.

  P503-P511 now prove the conservative, Lean-safe content of the slogan
  "information = matter" inside the current formal Standard-Model projection:

    * information incidences and matter/Higgs slots are equivalent;
    * endpoint presentation is unique relative to endpoint signatures;
    * concrete `3+2+1+1` block support realizes those endpoints;
    * full off-block support is canonical support plus conjugate mirror;
    * concrete support fibers reproduce representation component counts;
    * typed concrete support reconstructs the one-loop trace input and `b0`;
    * concrete labels are endpoint-signature forced on actual support;
    * concrete support is equivalent to typed component positions.

  This file bundles those receipts into one theorem.

  Boundary: the theorem is explicitly a current-carrier certificate.  It does
  not supply the deeper physical producer for SU(7) representation breaking,
  low-energy thresholds, mass values, or empirical identification of
  information with matter outside the formal projection.
-/

import H0mework.Physics.RepresentationSources.P511

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta

/-- Bundled current-carrier receipt for the precise, Lean-safe
information/matter theorem.  This is a data receipt rather than a `Prop`,
because it stores universe-polymorphic certificate structures from earlier
layers. -/
structure ConcreteInformationMatterCarrierCertificate where
  slot_equiv :
    Nonempty (InformationSlot ≃ MatterSlot)
  matter_has_information_source :
    ∀ s : MatterSlot, ∃ i : InformationSlot, informationMatterEquiv i = s
  information_has_matter_projection :
    ∀ i : InformationSlot, ∃ s : MatterSlot, informationMatterEquiv i = s
  trace_input :
    ∀ G : StandardModelGaugeFactor,
      incidenceCarrierTraceInput G = multipletCarrierTraceInput G
  b0_projection :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (concreteSupportCarrierTraceInput G) = carrierB0 G
  endpoint_universal_matches_P503 :
    matterEndpointPresentation.incidenceEquiv = informationMatterEquiv
  concrete_endpoint_support :
    ConcreteBlockSupportEndpointCertificate
  full_off_block_support :
    ConcreteFullOffBlockSupportCertificate
  representation_typing :
    ConcreteMatterRepresentationTypingCertificate
  concrete_trace_input :
    ConcreteSupportTraceInputCertificate
  endpoint_signature_faithful :
    ConcreteSupportEndpointSignatureFaithfulnessCertificate
  component_carrier :
    ConcreteSupportComponentCarrierCertificate
  component_equiv :
    Nonempty (ConcreteCanonicalOffDiagonalIndexPair ≃ MatterComponentPosition)
  component_card :
    Fintype.card MatterComponentPosition = 17

/-- Current concrete information/matter carrier certificate.

This is the strongest theorem currently proved by the P503-P511 chain. -/
theorem concreteInformationMatterCarrierCertificate :
    ConcreteInformationMatterCarrierCertificate where
  slot_equiv := ⟨informationMatterEquiv⟩
  matter_has_information_source := every_matter_slot_has_information_source
  information_has_matter_projection :=
    every_information_slot_has_matter_projection
  trace_input := information_trace_input_eq_matter_trace_input
  b0_projection := betaCoeff_concreteSupportCarrierTraceInput_eq_carrierB0
  endpoint_universal_matches_P503 :=
    matterEndpointPresentation_incidenceEquiv_eq_informationMatterEquiv
  concrete_endpoint_support := concreteBlockSupportEndpointCertificate
  full_off_block_support := concreteFullOffBlockSupportCertificate
  representation_typing := concreteMatterRepresentationTypingCertificate
  concrete_trace_input := concreteSupportTraceInputCertificate
  endpoint_signature_faithful :=
    concreteSupportEndpointSignatureFaithfulnessCertificate
  component_carrier := concreteSupportComponentCarrierCertificate
  component_equiv := ⟨concreteSupportMatterComponentPositionEquiv⟩
  component_card := matterComponentPosition_card

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
