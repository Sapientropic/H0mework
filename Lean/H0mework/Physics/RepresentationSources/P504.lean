/-
  Proposition 504: canonicality of the information/matter projection.

  P503 proves that the current SU(7) block-incidence information carrier is
  equivalent to the generated Standard-Model matter/Higgs carrier.

  P460 proves a stronger fact one layer below: once endpoint signatures are
  fixed, there is no remaining schedule permutation freedom.

  This file composes the two facts.  The information/matter projection is not
  merely an equivalence that we chose; among equivalences that preserve the
  endpoint signature table, it is unique.

  Boundary: the endpoint-signature table is still an input at this layer.  The
  theorem proves canonicality relative to that table, not that SU(7) alone
  derives the table.
-/

import H0mework.Physics.RepresentationSources.P503
import H0mework.Physics.RepresentationSources.P460

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta

/-! ## Endpoint-signature preservation -/

/-- THEOREM 1: the P503 information/matter projection preserves the
endpoint-signature table. -/
theorem informationMatterEquiv_preserves_endpointSignature
    (i : InformationSlot) :
    generatedSlotEndpointSignature (informationMatterEquiv i) =
      SU7BlockIncidence.endpoints i := by
  change generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
    SU7BlockIncidence.endpoints i
  exact generatedSlotOfIncidence_preserves_endpointSignature i

/-- THEOREM 2: any endpoint-signature-preserving information/matter
equivalence is pointwise equal to the P503 projection. -/
theorem endpointSignature_preserving_informationMatterEquiv_unique_pointwise
    (e : InformationSlot ≃ MatterSlot)
    (he : ∀ i : InformationSlot,
      generatedSlotEndpointSignature (e i) = SU7BlockIncidence.endpoints i) :
    ∀ i : InformationSlot, e i = informationMatterEquiv i := by
  intro i
  apply generatedSlotEndpointSignature_injective
  rw [he i, informationMatterEquiv_preserves_endpointSignature i]

/-- THEOREM 3: equivalently, any endpoint-signature-preserving
information/matter equivalence is the P503 projection. -/
theorem endpointSignature_preserving_informationMatterEquiv_unique
    (e : InformationSlot ≃ MatterSlot)
    (he : ∀ i : InformationSlot,
      generatedSlotEndpointSignature (e i) = SU7BlockIncidence.endpoints i) :
    e = informationMatterEquiv := by
  ext i
  exact endpointSignature_preserving_informationMatterEquiv_unique_pointwise
    e he i

/-- THEOREM 4: any endpoint-signature-preserving schedule, even before being
packaged as an equivalence, is the P503 information/matter schedule. -/
theorem endpointSignature_preserving_informationMatterSchedule_unique
    (f : InformationSlot -> MatterSlot)
    (hf : ∀ i : InformationSlot,
      generatedSlotEndpointSignature (f i) = SU7BlockIncidence.endpoints i) :
    f = informationMatterEquiv := by
  rw [informationMatterEquiv]
  exact endpointSignature_preserving_schedule_unique f hf

/-! ## Bundled canonicality receipt -/

/-- A bundled receipt: the information/matter projection is canonical relative
to the endpoint-signature table. -/
structure CanonicalInformationMatterProjectionCertificate : Prop where
  projection_nonempty :
    Nonempty (InformationSlot ≃ MatterSlot)
  preserves_signature :
    ∀ i : InformationSlot,
      generatedSlotEndpointSignature (informationMatterEquiv i) =
        SU7BlockIncidence.endpoints i
  unique_pointwise :
    ∀ e : InformationSlot ≃ MatterSlot,
      (∀ i : InformationSlot,
        generatedSlotEndpointSignature (e i) =
          SU7BlockIncidence.endpoints i) ->
      ∀ i : InformationSlot, e i = informationMatterEquiv i
  unique_equiv :
    ∀ e : InformationSlot ≃ MatterSlot,
      (∀ i : InformationSlot,
        generatedSlotEndpointSignature (e i) =
          SU7BlockIncidence.endpoints i) ->
      e = informationMatterEquiv
  unique_schedule :
    ∀ f : InformationSlot -> MatterSlot,
      (∀ i : InformationSlot,
        generatedSlotEndpointSignature (f i) =
          SU7BlockIncidence.endpoints i) ->
      f = informationMatterEquiv

/-- THEOREM 5: the current Standard-Model projection carrier supplies the
canonical information/matter projection receipt. -/
theorem canonicalInformationMatterProjectionCertificate :
    CanonicalInformationMatterProjectionCertificate where
  projection_nonempty := ⟨informationMatterEquiv⟩
  preserves_signature := informationMatterEquiv_preserves_endpointSignature
  unique_pointwise :=
    endpointSignature_preserving_informationMatterEquiv_unique_pointwise
  unique_equiv := endpointSignature_preserving_informationMatterEquiv_unique
  unique_schedule :=
    endpointSignature_preserving_informationMatterSchedule_unique

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
