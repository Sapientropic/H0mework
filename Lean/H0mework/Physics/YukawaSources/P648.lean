import H0mework.Physics.AlphaSources.P647

/-!
# Proposition 648: finite Yukawa depth producer-debt closure

P645 proves the SU(7) primitive depth-producer surface is a singleton.  This
file exposes the theorem in the form needed by the producer-debt track:

given a primitive-card packet satisfying the finite source equations and a
Yukawa sector schedule preserving SU(7) endpoint signatures, the generated
depth table is forced to be the selected table.  Hence the nine integer depths
and the typed Jarlskog sum are outputs of the finite SU(7) source/ordering
surface, not a post-hoc table lookup.

Boundary: this is still finite source/ordering closure.  It does not derive
the primitive-card source equations from smooth SU(7)-breaking dynamics or a
continuous consolidation flow.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Direct producer theorem from primitive cards plus endpoint schedule -/

/-- THEOREM 1: primitive-card source equations plus endpoint-preserving SU(7)
sector schedule force the selected Yukawa depth table. -/
theorem yukawaDepthTable_forced_of_primitiveCards_and_endpointSchedule
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    T = selectedYukawaDepthTableCandidate := by
  exact
    eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T
      ⟨P, f, hP, hf, hT⟩

/-- THEOREM 2: under the same producer hypotheses, the mass-order depth list
is exactly the documented nine integer depths. -/
theorem yukawaDepthMassOrder_forced_of_primitiveCards_and_endpointSchedule
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rw [yukawaDepthTable_forced_of_primitiveCards_and_endpointSchedule
    P f T hP hf hT]
  exact selectedYukawaDepthTableCandidate_massOrder_eq

/-- THEOREM 3: under the same producer hypotheses, the individual named
depths are forced. -/
theorem yukawaNamedDepths_forced_of_primitiveCards_and_endpointSchedule
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    T.depth .top = 50 ∧
      T.depth .bottom = 346 ∧
      T.depth .tau = 372 ∧
      T.depth .charm = 489 ∧
      T.depth .muon = 583 ∧
      T.depth .strange = 682 ∧
      T.depth .down = 880 ∧
      T.depth .up = 908 ∧
      T.depth .electron = 982 := by
  exact
    su7PrimitiveYukawaDepthProducerSurface_namedDepths T
      ⟨P, f, hP, hf, hT⟩

/-- THEOREM 4: under the same producer hypotheses, the typed Jarlskog
four-product depth sum is `386`. -/
theorem yukawaTypedJarlskog_forced_of_primitiveCards_and_endpointSchedule
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int) := by
  exact
    su7PrimitiveYukawaDepthProducerSurface_jarlskog_eq_386 T
      ⟨P, f, hP, hf, hT⟩

/-! ## Bundled finite closure certificate -/

/-- Compact certificate: the current finite Yukawa-depth producer debt is
closed at the primitive-card / endpoint-ordering layer. -/
structure YukawaFiniteDepthProducerDebtClosureCertificate where
  primitive_card :
    YukawaPrimitiveCardProducerReceipt
  source_surface :
    YukawaPrimitiveCardSourceSurfaceReceipt
  endpoint_orientation :
    YukawaSectorEndpointOrientationUniquenessReceipt
  su7_surface :
    SU7PrimitiveYukawaDepthProducerCertificate
  table_forced :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              T = selectedYukawaDepthTableCandidate
  mass_order_forced :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  named_depths_forced :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              T.depth .top = 50 ∧
                T.depth .bottom = 346 ∧
                T.depth .tau = 372 ∧
                T.depth .charm = 489 ∧
                T.depth .muon = 583 ∧
                T.depth .strange = 682 ∧
                T.depth .down = 880 ∧
                T.depth .up = 908 ∧
                T.depth .electron = 982
  typed_jarlskog_forced :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int)

/-- THEOREM 5: finite Yukawa-depth producer-debt closure certificate. -/
theorem yukawaFiniteDepthProducerDebtClosureCertificate :
    YukawaFiniteDepthProducerDebtClosureCertificate where
  primitive_card := yukawaPrimitiveCardProducerReceipt
  source_surface := yukawaPrimitiveCardSourceSurfaceReceipt
  endpoint_orientation := yukawaSectorEndpointOrientationUniquenessReceipt
  su7_surface := su7PrimitiveYukawaDepthProducerCertificate
  table_forced :=
    yukawaDepthTable_forced_of_primitiveCards_and_endpointSchedule
  mass_order_forced :=
    yukawaDepthMassOrder_forced_of_primitiveCards_and_endpointSchedule
  named_depths_forced :=
    yukawaNamedDepths_forced_of_primitiveCards_and_endpointSchedule
  typed_jarlskog_forced :=
    yukawaTypedJarlskog_forced_of_primitiveCards_and_endpointSchedule

end StandardModelConstraint
end SaturationMonoid
