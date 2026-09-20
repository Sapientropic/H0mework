/-
  Proposition 508: concrete support fibers reproduce the existing
  matter/Higgs representation component counts.

  P507 proves that the concrete off-block matrix support splits into a
  canonical half of size 17 and a conjugate mirror of size 17.  This file types
  the canonical half by the existing P459 incidence-to-matter schedule, and
  proves that the concrete fibers have exactly the component multiplicities
  already used by P456/P457:

      Q: 6, uᶜ: 3, dᶜ: 3, L: 2, eᶜ: 1, H: 2.

  Boundary: this still does not derive the schedule from SU(7) representation
  theory.  It proves that once the P459 schedule is used, the concrete P286
  block-index support realizes the same finite representation counts that feed
  the one-loop trace and anomaly certificates.  The Stage-7 Phase-0 audit
  further proves that the actual P286 adjoint action does not induce the P458
  hypercharges on this schedule.  Thus the fiber/cardinality theorems remain
  correct conditional typing arithmetic, not an SU(7)-generated chiral matter
  spectrum.
-/

import H0mework.Physics.RepresentationSources.P507

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta
open GaugeProjection.ConcreteBlockDiagonal

/-! ## Concrete support positions typed by the existing generated carrier -/

/-- The totalized matter/Higgs label of a concrete canonical off-diagonal
matrix position.  The final catch-all branch is unreachable on
`ConcreteCanonicalOffDiagonalIndexPair`; it keeps the function computable
without adding proof arguments to the value. -/
def concreteMatterSlotOfIndexPair
    (p : ConcreteCanonicalOffDiagonalIndexPair) : MatterSlot :=
  match blockOfSMBlockIndex p.1.1, blockOfSMBlockIndex p.1.2 with
  | .color, .weak => .quarkDoublet
  | .color, .positiveSinglet => .upConjugate
  | .color, .negativeSinglet => .downConjugate
  | .weak, .positiveSinglet => .higgsDoublet
  | .weak, .negativeSinglet => .leptonDoublet
  | .positiveSinglet, .negativeSinglet => .electronConjugate
  | _, _ => .higgsDoublet

/-- THEOREM 1: the concrete label agrees with the existing P459
incidence-to-generated-slot schedule whenever the endpoint pair is that
incidence. -/
theorem concreteMatterSlotOfIndexPair_eq_generatedSlotOfIncidence
    (p : ConcreteCanonicalOffDiagonalIndexPair)
    (i : InformationSlot)
    (h :
      (blockOfSMBlockIndex p.1.1, blockOfSMBlockIndex p.1.2) =
        SU7BlockIncidence.endpoints i) :
    concreteMatterSlotOfIndexPair p = generatedSlotOfIncidence i := by
  cases hsrc : blockOfSMBlockIndex p.1.1 <;>
    cases htgt : blockOfSMBlockIndex p.1.2 <;>
    cases i <;>
    simp [concreteMatterSlotOfIndexPair, SU7BlockIncidence.endpoints,
      generatedSlotOfIncidence, hsrc, htgt] at h ⊢

/-- THEOREM 2: every existing matter/Higgs slot is realized by at least one
concrete canonical matrix position. -/
theorem concreteMatterSlotOfIndexPair_surjective :
    Function.Surjective concreteMatterSlotOfIndexPair := by
  intro s
  cases s <;> decide

/-! ## Fiber counts and component multiplicities -/

/-- The concrete fiber over a matter/Higgs slot. -/
abbrev ConcreteMatterSlotFiber (s : MatterSlot) :=
  {p : ConcreteCanonicalOffDiagonalIndexPair //
    concreteMatterSlotOfIndexPair p = s}

instance concreteMatterSlotFiberFintype (s : MatterSlot) :
    Fintype (ConcreteMatterSlotFiber s) := by
  infer_instance

/-- Component multiplicity of the generated matter/Higgs slot, as a natural
number.  This is the same data as P456/P457 for the five Weyl slots, plus the
two-component Higgs doublet. -/
def matterSlotComponentMultiplicity : MatterSlot -> ℕ
  | .quarkDoublet => 6
  | .upConjugate => 3
  | .downConjugate => 3
  | .leptonDoublet => 2
  | .electronConjugate => 1
  | .higgsDoublet => 2

/-- THEOREM 3: concrete support fibers are exactly the representation
component multiplicities. -/
theorem concreteMatterSlotFiber_card_eq_componentMultiplicity
    (s : MatterSlot) :
    Fintype.card (ConcreteMatterSlotFiber s) =
      matterSlotComponentMultiplicity s := by
  cases s <;> decide

/-- THEOREM 4: the concrete support fiber table is
`Q=6,uᶜ=3,dᶜ=3,L=2,eᶜ=1,H=2`. -/
theorem concreteMatterSlotFiber_card_table :
    Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) = 6 ∧
    Fintype.card (ConcreteMatterSlotFiber .upConjugate) = 3 ∧
    Fintype.card (ConcreteMatterSlotFiber .downConjugate) = 3 ∧
    Fintype.card (ConcreteMatterSlotFiber .leptonDoublet) = 2 ∧
    Fintype.card (ConcreteMatterSlotFiber .electronConjugate) = 1 ∧
    Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) = 2 := by
  decide

/-- THEOREM 5: summing the six typed fibers recovers the canonical concrete
support size `17`. -/
theorem concreteMatterSlotFiber_card_sum :
    Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) +
    Fintype.card (ConcreteMatterSlotFiber .upConjugate) +
    Fintype.card (ConcreteMatterSlotFiber .downConjugate) +
    Fintype.card (ConcreteMatterSlotFiber .leptonDoublet) +
    Fintype.card (ConcreteMatterSlotFiber .electronConjugate) +
    Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) = 17 := by
  decide

/-- Embed the five Weyl multiplets into the generated carrier. -/
def matterSlotOfWeyl : StandardModelWeylMultiplet -> MatterSlot
  | .quarkDoublet => .quarkDoublet
  | .upConjugate => .upConjugate
  | .downConjugate => .downConjugate
  | .leptonDoublet => .leptonDoublet
  | .electronConjugate => .electronConjugate

/-- THEOREM 6: the Weyl embedding is the inverse of `toWeyl?` on the five
fermion slots. -/
theorem matterSlotOfWeyl_toWeyl
    (m : StandardModelWeylMultiplet) :
    SU7GeneratedCarrierSlot.toWeyl? (matterSlotOfWeyl m) = some m := by
  cases m <;> rfl

/-- THEOREM 7: on the five Weyl slots, concrete support fiber counts equal
P457's Weyl component multiplicities. -/
theorem concreteMatterSlotFiber_card_eq_weylComponentMultiplicity
    (m : StandardModelWeylMultiplet) :
    (Fintype.card (ConcreteMatterSlotFiber (matterSlotOfWeyl m)) : ℚ) =
      StandardModelWeylMultiplet.componentMultiplicity m := by
  rw [concreteMatterSlotFiber_card_eq_componentMultiplicity]
  cases m <;>
    norm_num [matterSlotOfWeyl, matterSlotComponentMultiplicity,
      StandardModelWeylMultiplet.componentMultiplicity]

/-- THEOREM 8: the scalar slot is the two-component Higgs doublet. -/
theorem concreteMatterSlotFiber_card_higgsDoublet :
    Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) = 2 := by
  decide

/-- Bundled receipt: the concrete canonical matrix support realizes the
existing matter/Higgs representation typing and component counts. -/
structure ConcreteMatterRepresentationTypingCertificate : Prop where
  concrete_slot_surjective :
    Function.Surjective concreteMatterSlotOfIndexPair
  compatible_with_incidence_schedule :
    ∀ p : ConcreteCanonicalOffDiagonalIndexPair,
      ∀ i : InformationSlot,
        (blockOfSMBlockIndex p.1.1, blockOfSMBlockIndex p.1.2) =
          SU7BlockIncidence.endpoints i ->
        concreteMatterSlotOfIndexPair p = generatedSlotOfIncidence i
  fiber_card_component_multiplicity :
    ∀ s : MatterSlot,
      Fintype.card (ConcreteMatterSlotFiber s) =
        matterSlotComponentMultiplicity s
  fiber_card_table :
    Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) = 6 ∧
    Fintype.card (ConcreteMatterSlotFiber .upConjugate) = 3 ∧
    Fintype.card (ConcreteMatterSlotFiber .downConjugate) = 3 ∧
    Fintype.card (ConcreteMatterSlotFiber .leptonDoublet) = 2 ∧
    Fintype.card (ConcreteMatterSlotFiber .electronConjugate) = 1 ∧
    Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) = 2
  fiber_card_sum :
    Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) +
    Fintype.card (ConcreteMatterSlotFiber .upConjugate) +
    Fintype.card (ConcreteMatterSlotFiber .downConjugate) +
    Fintype.card (ConcreteMatterSlotFiber .leptonDoublet) +
    Fintype.card (ConcreteMatterSlotFiber .electronConjugate) +
    Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) = 17
  weyl_component_multiplicity :
    ∀ m : StandardModelWeylMultiplet,
      (Fintype.card (ConcreteMatterSlotFiber (matterSlotOfWeyl m)) : ℚ) =
        StandardModelWeylMultiplet.componentMultiplicity m
  higgs_doublet_card :
    Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) = 2
  full_off_block_support :
    ConcreteFullOffBlockSupportCertificate

/-- THEOREM 9: concrete block support realizes the representation component
counts used by the Standard-Model trace/anomaly layer. -/
theorem concreteMatterRepresentationTypingCertificate :
    ConcreteMatterRepresentationTypingCertificate where
  concrete_slot_surjective := concreteMatterSlotOfIndexPair_surjective
  compatible_with_incidence_schedule :=
    concreteMatterSlotOfIndexPair_eq_generatedSlotOfIncidence
  fiber_card_component_multiplicity :=
    concreteMatterSlotFiber_card_eq_componentMultiplicity
  fiber_card_table := concreteMatterSlotFiber_card_table
  fiber_card_sum := concreteMatterSlotFiber_card_sum
  weyl_component_multiplicity :=
    concreteMatterSlotFiber_card_eq_weylComponentMultiplicity
  higgs_doublet_card := concreteMatterSlotFiber_card_higgsDoublet
  full_off_block_support := concreteFullOffBlockSupportCertificate

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
