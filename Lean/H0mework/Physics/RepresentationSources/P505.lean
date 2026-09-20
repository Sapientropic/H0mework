/-
  Proposition 505: endpoint-presented matter carriers.

  P504 proves that the current information/matter projection is unique once
  the endpoint-signature table is fixed.  This file lowers that boundary one
  step: a "matter carrier" does not need a hand-picked schedule at all if it
  is presented by the canonical off-diagonal endpoint pairs of the four
  `3+2+1+1` SU(7) blocks.

  The universal object is the finite endpoint carrier

      { (a,b) | code(a) < code(b) }.

  The SU7 block-incidence carrier is equivalent to this endpoint carrier, and
  any slot type equipped with an endpoint presentation is canonically
  equivalent to the incidence carrier.  The current five-Weyl-plus-Higgs
  carrier is an instance.

  Boundary: this still does not derive the physical labels `Q,uᶜ,dᶜ,L,eᶜ,H`
  from pure SU(7) representation theory.  It proves that once a carrier is
  endpoint-presented, the incidence/matter equivalence is canonical.
-/

import H0mework.Physics.RepresentationSources.P504

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta

noncomputable section

/-! ## Canonical endpoint carrier -/

/-- The canonical off-diagonal endpoint carrier of the four `3+2+1+1`
blocks. -/
abbrev CanonicalEndpoint :=
  {p : SU7CarrierBlock × SU7CarrierBlock //
    IsCanonicalOffDiagonalPair p.1 p.2}

/-- The endpoint presentation of a named SU7 block incidence. -/
def incidenceEndpoint (i : SU7BlockIncidence) : CanonicalEndpoint :=
  ⟨SU7BlockIncidence.endpoints i,
    SU7BlockIncidence.endpoints_canonical i⟩

/-- THEOREM 1: endpoint presentation separates incidences. -/
theorem incidenceEndpoint_injective :
    Function.Injective incidenceEndpoint := by
  intro i j h
  apply SU7BlockIncidence.endpoints_injective
  exact congrArg Subtype.val h

/-- THEOREM 2: every canonical endpoint is represented by an incidence. -/
theorem incidenceEndpoint_surjective :
    Function.Surjective incidenceEndpoint := by
  intro p
  rcases p with ⟨⟨a, b⟩, h⟩
  rcases SU7BlockIncidence.endpoints_complete a b h with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi

/-- THEOREM 3: incidences are exactly canonical endpoint pairs. -/
def incidenceEndpointEquiv : SU7BlockIncidence ≃ CanonicalEndpoint :=
  Equiv.ofBijective incidenceEndpoint
    ⟨incidenceEndpoint_injective, incidenceEndpoint_surjective⟩

/-- THEOREM 4: the equivalence preserves the raw endpoint pair. -/
theorem incidenceEndpointEquiv_val
    (i : SU7BlockIncidence) :
    (incidenceEndpointEquiv i).1 = SU7BlockIncidence.endpoints i :=
  rfl

/-- THEOREM 5: the inverse endpoint equivalence has the requested endpoint. -/
theorem incidenceEndpointEquiv_symm_endpoints
    (p : CanonicalEndpoint) :
    SU7BlockIncidence.endpoints (incidenceEndpointEquiv.symm p) = p.1 := by
  exact congrArg Subtype.val
    (Equiv.apply_symm_apply incidenceEndpointEquiv p)

/-! ## Abstract endpoint-presented carriers -/

/-- A slot carrier presented by the canonical endpoint carrier. -/
structure EndpointPresentedCarrier (Slot : Type*) where
  signature : Slot -> CanonicalEndpoint
  slotOfEndpoint : CanonicalEndpoint -> Slot
  left_inv : ∀ s : Slot, slotOfEndpoint (signature s) = s
  right_inv : ∀ p : CanonicalEndpoint, signature (slotOfEndpoint p) = p

namespace EndpointPresentedCarrier

variable {Slot : Type*} (C : EndpointPresentedCarrier Slot)

/-- THEOREM 6: an endpoint presentation is an equivalence with the canonical
endpoint carrier. -/
def endpointEquiv : Slot ≃ CanonicalEndpoint where
  toFun := C.signature
  invFun := C.slotOfEndpoint
  left_inv := C.left_inv
  right_inv := C.right_inv

/-- THEOREM 7: endpoint signatures separate slots. -/
theorem signature_injective :
    Function.Injective C.signature := by
  intro x y h
  have h' : C.slotOfEndpoint (C.signature x) =
      C.slotOfEndpoint (C.signature y) := by
    exact congrArg C.slotOfEndpoint h
  simpa [C.left_inv x, C.left_inv y] using h'

/-- THEOREM 8: every endpoint-presented carrier is canonically equivalent to
the SU7 block-incidence carrier. -/
def incidenceEquiv : SU7BlockIncidence ≃ Slot :=
  incidenceEndpointEquiv.trans (C.endpointEquiv).symm

/-- THEOREM 9: the canonical incidence equivalence preserves endpoint
signatures. -/
theorem incidenceEquiv_preserves_signature
    (i : SU7BlockIncidence) :
    C.signature (C.incidenceEquiv i) = incidenceEndpoint i := by
  change C.signature (C.slotOfEndpoint (incidenceEndpoint i)) =
    incidenceEndpoint i
  exact C.right_inv (incidenceEndpoint i)

/-- THEOREM 10: any schedule preserving the endpoint presentation is the
canonical incidence equivalence. -/
theorem incidenceEquiv_unique
    (f : SU7BlockIncidence -> Slot)
    (hf : ∀ i : SU7BlockIncidence, C.signature (f i) = incidenceEndpoint i) :
    f = C.incidenceEquiv := by
  funext i
  apply C.signature_injective
  rw [hf i, C.incidenceEquiv_preserves_signature i]

end EndpointPresentedCarrier

/-! ## The current Standard-Model matter carrier as an endpoint presentation -/

/-- Generated matter/Higgs endpoint signatures are canonical endpoint pairs. -/
theorem generatedSlotEndpointSignature_canonical
    (s : MatterSlot) :
    IsCanonicalOffDiagonalPair
      (generatedSlotEndpointSignature s).1
      (generatedSlotEndpointSignature s).2 := by
  rw [generatedSlotEndpointSignature_eq_endpoints_incidenceOfGeneratedSlot]
  exact SU7BlockIncidence.endpoints_canonical (incidenceOfGeneratedSlot s)

/-- The current matter/Higgs carrier presented by canonical endpoint pairs. -/
def matterEndpointPresentation :
    EndpointPresentedCarrier MatterSlot where
  signature := fun s =>
    ⟨generatedSlotEndpointSignature s,
      generatedSlotEndpointSignature_canonical s⟩
  slotOfEndpoint := fun p =>
    generatedSlotOfIncidence (incidenceEndpointEquiv.symm p)
  left_inv := by
    intro s
    apply generatedSlotEndpointSignature_injective
    exact
      (generatedSlotOfIncidence_preserves_endpointSignature
        (incidenceEndpointEquiv.symm
          ⟨generatedSlotEndpointSignature s,
            generatedSlotEndpointSignature_canonical s⟩)).trans
        (incidenceEndpointEquiv_symm_endpoints
          ⟨generatedSlotEndpointSignature s,
            generatedSlotEndpointSignature_canonical s⟩)
  right_inv := by
    intro p
    apply Subtype.ext
    exact
      (generatedSlotOfIncidence_preserves_endpointSignature
        (incidenceEndpointEquiv.symm p)).trans
        (incidenceEndpointEquiv_symm_endpoints p)

/-- THEOREM 11: the endpoint-presented canonical equivalence is exactly the
P503 information/matter equivalence. -/
theorem matterEndpointPresentation_incidenceEquiv_eq_informationMatterEquiv :
    matterEndpointPresentation.incidenceEquiv = informationMatterEquiv := by
  ext i
  apply generatedSlotEndpointSignature_injective
  have hleft :
      generatedSlotEndpointSignature
          (matterEndpointPresentation.incidenceEquiv i) =
        SU7BlockIncidence.endpoints i := by
    simpa [matterEndpointPresentation, incidenceEndpoint] using
      congrArg Subtype.val
        (matterEndpointPresentation.incidenceEquiv_preserves_signature i)
  exact hleft.trans (informationMatterEquiv_preserves_endpointSignature i).symm

/-- A bundled receipt for the endpoint-presented carrier universal property. -/
structure EndpointPresentedMatterUniversalCertificate : Prop where
  incidence_endpoint_equiv :
    Nonempty (SU7BlockIncidence ≃ CanonicalEndpoint)
  incidence_endpoint_injective :
    Function.Injective incidenceEndpoint
  incidence_endpoint_surjective :
    Function.Surjective incidenceEndpoint
  generic_equiv :
    ∀ {Slot : Type*}, ∀ _C : EndpointPresentedCarrier Slot,
      Nonempty (SU7BlockIncidence ≃ Slot)
  generic_unique :
    ∀ {Slot : Type*}, ∀ C : EndpointPresentedCarrier Slot,
      ∀ f : SU7BlockIncidence -> Slot,
        (∀ i : SU7BlockIncidence, C.signature (f i) = incidenceEndpoint i) ->
        f = C.incidenceEquiv
  matter_instance :
    Nonempty (EndpointPresentedCarrier MatterSlot)
  matter_equiv_is_P503 :
    matterEndpointPresentation.incidenceEquiv = informationMatterEquiv

/-- THEOREM 12: SU7 endpoint-presented matter carriers are canonical. -/
theorem endpointPresentedMatterUniversalCertificate :
    EndpointPresentedMatterUniversalCertificate where
  incidence_endpoint_equiv := ⟨incidenceEndpointEquiv⟩
  incidence_endpoint_injective := incidenceEndpoint_injective
  incidence_endpoint_surjective := incidenceEndpoint_surjective
  generic_equiv := fun C => ⟨C.incidenceEquiv⟩
  generic_unique := fun C f hf => C.incidenceEquiv_unique f hf
  matter_instance := ⟨matterEndpointPresentation⟩
  matter_equiv_is_P503 :=
    matterEndpointPresentation_incidenceEquiv_eq_informationMatterEquiv

end

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
