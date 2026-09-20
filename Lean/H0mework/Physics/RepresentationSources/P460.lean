/-
  Proposition 460: uniqueness of the incidence-to-slot schedule under
  endpoint-signature preservation.

  P459 supplies the concrete schedule from the six off-diagonal `3+2+1+1`
  block incidences to the five Weyl multiplets plus the Higgs doublet.  This
  file proves that the schedule is not arbitrary once the endpoint signatures
  of the six generated slots are fixed: any map from incidences to generated
  slots that preserves those signatures is definitionally the P459 schedule.

  Boundary: the endpoint-signature table is still physical input.  This file
  proves uniqueness of the schedule relative to that table; it does not prove
  that SU(7) alone forces the table.
-/

import H0mework.Physics.RepresentationSources.P459

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Endpoint signatures of generated slots -/

/-- The gauge-block endpoint signature of a generated matter/Higgs slot. -/
def generatedSlotEndpointSignature :
    SU7GeneratedCarrierSlot -> SU7CarrierBlock × SU7CarrierBlock
  | .quarkDoublet => (.color, .weak)
  | .upConjugate => (.color, .positiveSinglet)
  | .downConjugate => (.color, .negativeSinglet)
  | .leptonDoublet => (.weak, .negativeSinglet)
  | .electronConjugate => (.positiveSinglet, .negativeSinglet)
  | .higgsDoublet => (.weak, .positiveSinglet)

/-- THEOREM 1: the P459 inverse schedule is exactly the endpoint-signature
table. -/
theorem generatedSlotEndpointSignature_eq_endpoints_incidenceOfGeneratedSlot
    (s : SU7GeneratedCarrierSlot) :
    generatedSlotEndpointSignature s =
      SU7BlockIncidence.endpoints (incidenceOfGeneratedSlot s) := by
  cases s <;> rfl

/-- THEOREM 2: generated slots are separated by their endpoint signatures. -/
theorem generatedSlotEndpointSignature_injective :
    Function.Injective generatedSlotEndpointSignature := by
  intro a b h
  cases a <;> cases b <;> simp [generatedSlotEndpointSignature] at h ⊢

/-- THEOREM 3: the P459 schedule preserves endpoint signatures. -/
theorem generatedSlotOfIncidence_preserves_endpointSignature
    (i : SU7BlockIncidence) :
    generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
      SU7BlockIncidence.endpoints i := by
  cases i <;> rfl

/-- THEOREM 4: any endpoint-signature-preserving schedule is the P459
schedule. -/
theorem endpointSignature_preserving_schedule_unique
    (f : SU7BlockIncidence -> SU7GeneratedCarrierSlot)
    (hf : ∀ i : SU7BlockIncidence,
      generatedSlotEndpointSignature (f i) = SU7BlockIncidence.endpoints i) :
    f = generatedSlotOfIncidence := by
  funext i
  apply generatedSlotEndpointSignature_injective
  rw [hf i, generatedSlotOfIncidence_preserves_endpointSignature]

/-- THEOREM 5: equivalently, any endpoint-signature-preserving equivalence is
the P459 equivalence. -/
theorem endpointSignature_preserving_equiv_unique
    (e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot)
    (he : ∀ i : SU7BlockIncidence,
      generatedSlotEndpointSignature (e i) = SU7BlockIncidence.endpoints i) :
    e.toFun = blockIncidenceGeneratedSlotEquiv.toFun :=
  endpointSignature_preserving_schedule_unique e.toFun he

/-- THEOREM 6: a generated slot has a canonical incidence with the same
endpoint signature. -/
theorem exists_incidence_with_generated_slot_signature
    (s : SU7GeneratedCarrierSlot) :
    ∃ i : SU7BlockIncidence,
      SU7BlockIncidence.endpoints i = generatedSlotEndpointSignature s := by
  exact ⟨incidenceOfGeneratedSlot s,
    (generatedSlotEndpointSignature_eq_endpoints_incidenceOfGeneratedSlot s).symm⟩

/-- THEOREM 7: endpoint signatures are complete for generated slots; two slots
with the same canonical incidence are equal. -/
theorem incidenceOfGeneratedSlot_injective :
    Function.Injective incidenceOfGeneratedSlot := by
  intro a b h
  apply generatedSlotEndpointSignature_injective
  rw [generatedSlotEndpointSignature_eq_endpoints_incidenceOfGeneratedSlot,
    generatedSlotEndpointSignature_eq_endpoints_incidenceOfGeneratedSlot, h]

/-- Bundled certificate for the current endpoint-signature uniqueness layer. -/
structure SU7IncidenceOrientationUniquenessCertificate where
  slot_signature_injective :
    Function.Injective generatedSlotEndpointSignature
  schedule_preserves_signature :
    ∀ i : SU7BlockIncidence,
      generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
        SU7BlockIncidence.endpoints i
  schedule_unique :
    ∀ f : SU7BlockIncidence -> SU7GeneratedCarrierSlot,
      (∀ i : SU7BlockIncidence,
        generatedSlotEndpointSignature (f i) =
          SU7BlockIncidence.endpoints i) ->
        f = generatedSlotOfIncidence
  incidence_equiv :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot
  b0_formula :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (incidenceCarrierTraceInput G) = carrierB0 G

/-- THEOREM 8: the endpoint-signature uniqueness certificate. -/
def su7IncidenceOrientationUniquenessCertificate :
    SU7IncidenceOrientationUniquenessCertificate where
  slot_signature_injective := generatedSlotEndpointSignature_injective
  schedule_preserves_signature :=
    generatedSlotOfIncidence_preserves_endpointSignature
  schedule_unique := endpointSignature_preserving_schedule_unique
  incidence_equiv := blockIncidenceGeneratedSlotEquiv
  b0_formula := betaCoeff_incidenceCarrierTraceInput_eq_carrierB0

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
