import H0mework.Physics.AlphaSources.P789

/-!
# Proposition 790: no-free SU(7) incidence schedule

P459 defines the six off-diagonal incidences of the `3+2+1+1` SU(7) block
carrier and a generated matter/Higgs slot for each incidence.  P460 proves
that an endpoint-signature-preserving schedule is unique.

This file packages the exact no-free statement needed downstream: once the
four block endpoints and generated endpoint signatures are fixed, there is no
remaining permutation freedom in the six-slot incidence schedule.  The unique
non-Weyl generated slot is the Higgs doublet, and it is exactly the
`weak-positive` incidence.  This is the finite schedule layer used by the
bottomed alpha_s four-source producer.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Endpoint-signature no-free schedule -/

/-- THEOREM 1: any endpoint-signature-preserving incidence schedule is the
canonical generated-slot schedule. -/
theorem generatedSlotSchedule_unique_of_endpointSignature
    (f : SU7BlockIncidence -> SU7GeneratedCarrierSlot)
    (hf : ∀ i : SU7BlockIncidence,
      generatedSlotEndpointSignature (f i) = SU7BlockIncidence.endpoints i) :
    f = generatedSlotOfIncidence :=
  endpointSignature_preserving_schedule_unique f hf

/-- THEOREM 2: equivalently, any endpoint-signature-preserving equivalence
has the canonical underlying function. -/
theorem generatedSlotEquiv_unique_of_endpointSignature
    (e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot)
    (he : ∀ i : SU7BlockIncidence,
      generatedSlotEndpointSignature (e i) = SU7BlockIncidence.endpoints i) :
    e.toFun = blockIncidenceGeneratedSlotEquiv.toFun :=
  endpointSignature_preserving_equiv_unique e he

/-- THEOREM 3: the generated slot of an incidence has the same endpoint
signature as that incidence. -/
theorem generatedSlotOfIncidence_endpointSignature
    (i : SU7BlockIncidence) :
    generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
      SU7BlockIncidence.endpoints i :=
  generatedSlotOfIncidence_preserves_endpointSignature i

/-- THEOREM 4: the unique scalar/non-Weyl incidence is the weak-positive
incidence, and its generated slot is the Higgs doublet. -/
theorem generatedSlotOfIncidence_toWeyl_none_iff
    (i : SU7BlockIncidence) :
    SU7GeneratedCarrierSlot.toWeyl? (generatedSlotOfIncidence i) = none ↔
      i = .weakPositiveSinglet := by
  cases i <;> simp [generatedSlotOfIncidence, SU7GeneratedCarrierSlot.toWeyl?]

/-- THEOREM 5: all other incidences generate Weyl multiplet slots. -/
theorem generatedSlotOfIncidence_toWeyl_some_of_ne_weakPositive
    (i : SU7BlockIncidence)
    (hi : i ≠ .weakPositiveSinglet) :
    ∃ m : StandardModelWeylMultiplet,
      SU7GeneratedCarrierSlot.toWeyl? (generatedSlotOfIncidence i) = some m := by
  cases i <;>
    simp [generatedSlotOfIncidence, SU7GeneratedCarrierSlot.toWeyl?] at hi ⊢

/-- THEOREM 6: the block-incidence equivalence is the unique schedule
preserving endpoint signatures. -/
theorem blockIncidenceGeneratedSlotEquiv_no_free :
    ∀ e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot,
      (∀ i : SU7BlockIncidence,
        generatedSlotEndpointSignature (e i) =
          SU7BlockIncidence.endpoints i) ->
        e.toFun = blockIncidenceGeneratedSlotEquiv.toFun :=
  generatedSlotEquiv_unique_of_endpointSignature

/-! ## Bundled finite schedule certificate -/

/-- No-free certificate for the finite SU(7) incidence-to-matter/Higgs
schedule. -/
structure SU7IncidenceScheduleNoFreeCertificate : Prop where
  block_count :
    Fintype.card SU7CarrierBlock = 4
  incidence_count :
    Fintype.card SU7BlockIncidence = 6
  generated_slot_count :
    Fintype.card SU7GeneratedCarrierSlot = 6
  incidence_endpoints_injective :
    Function.Injective SU7BlockIncidence.endpoints
  incidence_endpoints_complete :
    ∀ a b : SU7CarrierBlock,
      IsCanonicalOffDiagonalPair a b ->
        ∃ s : SU7BlockIncidence, SU7BlockIncidence.endpoints s = (a, b)
  generated_signature_injective :
    Function.Injective generatedSlotEndpointSignature
  canonical_schedule_preserves_signature :
    ∀ i : SU7BlockIncidence,
      generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
        SU7BlockIncidence.endpoints i
  schedule_unique :
    ∀ f : SU7BlockIncidence -> SU7GeneratedCarrierSlot,
      (∀ i : SU7BlockIncidence,
        generatedSlotEndpointSignature (f i) =
          SU7BlockIncidence.endpoints i) ->
        f = generatedSlotOfIncidence
  equivalence_unique :
    ∀ e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot,
      (∀ i : SU7BlockIncidence,
        generatedSlotEndpointSignature (e i) =
          SU7BlockIncidence.endpoints i) ->
        e.toFun = blockIncidenceGeneratedSlotEquiv.toFun
  scalar_incidence_iff :
    ∀ i : SU7BlockIncidence,
      SU7GeneratedCarrierSlot.toWeyl? (generatedSlotOfIncidence i) = none ↔
        i = .weakPositiveSinglet
  bottomed_alpha_four_source :
    StandardModelConstraint.AlphaStrongBottomedFourSourceResidualProducerCertificate

/-- THEOREM 7: no-free SU(7) incidence schedule certificate. -/
theorem su7IncidenceScheduleNoFreeCertificate :
    SU7IncidenceScheduleNoFreeCertificate where
  block_count :=
    SU7CarrierBlock.card
  incidence_count :=
    SU7BlockIncidence.card
  generated_slot_count :=
    SU7GeneratedCarrierSlot.card
  incidence_endpoints_injective :=
    SU7BlockIncidence.endpoints_injective
  incidence_endpoints_complete :=
    SU7BlockIncidence.endpoints_complete
  generated_signature_injective :=
    generatedSlotEndpointSignature_injective
  canonical_schedule_preserves_signature :=
    generatedSlotOfIncidence_endpointSignature
  schedule_unique :=
    generatedSlotSchedule_unique_of_endpointSignature
  equivalence_unique :=
    blockIncidenceGeneratedSlotEquiv_no_free
  scalar_incidence_iff :=
    generatedSlotOfIncidence_toWeyl_none_iff
  bottomed_alpha_four_source :=
    StandardModelConstraint.alphaStrongBottomedFourSourceResidualProducerCertificate

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
