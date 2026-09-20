import H0mework.Physics.MixingSources.P644

/-!
# Proposition 645: SU(7) primitive depth producer for the Yukawa table

P606 proves that the primitive-card packet is a singleton source surface.
P591 proves that endpoint-signature preservation forces the SU(7) sector
schedule.  P644 proves that the selected depth table feeds the typed
Jarlskog four-product and produces `386`.

This file welds those pieces into the producer statement needed by the
Standard-Model track:

* a Yukawa table is accepted when it is generated from a primitive-card packet
  satisfying the finite SU(7) / information / Poincare source equations and
  an endpoint-signature preserving SU(7) sector schedule;
* that accepted surface is exactly the singleton selected table;
* therefore the nine displayed depths
  `[50, 346, 372, 489, 583, 682, 880, 908, 982]`
  and the typed Jarlskog depth sum `386` are forced outputs of this finite
  producer surface.

Boundary: this is the current finite producer closure.  It does not yet derive
the primitive-card source equations from smooth SU(7)-breaking dynamics,
three-loop RG, or a continuous consolidation-order flow.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## The SU(7) primitive depth-producer surface -/

/-- A Yukawa depth table is produced when it is generated from:

* a primitive-card packet satisfying the P606 source equations; and
* an endpoint-signature preserving SU(7) sector schedule.

The coefficient vector is read from the packet by P604's primitive-card law.
-/
def SU7PrimitiveYukawaDepthProducerSurface
    (T : YukawaDepthTableCandidate) : Prop :=
  ∃ P : YukawaCoefficientPrimitiveCardPacket,
    ∃ f : YukawaInteractionSector -> InformationSlot,
      YukawaPrimitiveCardSourceEquations P ∧
        YukawaSectorEndpointSignaturePreservingSchedule f ∧
          T =
            coefficientScheduleYukawaDepthTableCandidate
              (primitiveCardYukawaDepthStencilCoefficientVector P) f

/-- THEOREM 1: the selected table is accepted by the SU(7) primitive
depth-producer surface. -/
theorem selectedYukawaDepthTableCandidate_su7PrimitiveProducer :
    SU7PrimitiveYukawaDepthProducerSurface
      selectedYukawaDepthTableCandidate := by
  refine
    ⟨canonicalYukawaCoefficientPrimitiveCardPacket,
      yukawaSectorInformationIncidence,
      canonicalYukawaCoefficientPrimitiveCardPacket_sourceEquations,
      yukawaSectorInformationIncidence_endpointPreserving, ?_⟩
  ext y
  simp [coefficientScheduleYukawaDepthTableCandidate,
    selectedYukawaDepthTableCandidate]
  simpa [canonicalPrimitiveCardYukawaDepthStencilCoefficientVector] using
    (coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_sourceEquations
      yukawaSectorInformationIncidence
      yukawaSectorInformationIncidence_endpointPreserving y).symm

/-- THEOREM 2: every accepted SU(7) primitive producer table is the selected
nine-depth table. -/
theorem eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer
    (T : YukawaDepthTableCandidate)
    (hT : SU7PrimitiveYukawaDepthProducerSurface T) :
    T = selectedYukawaDepthTableCandidate := by
  rcases hT with ⟨P, f, hP, hf, hT⟩
  rw [hT]
  have hP' :
      P = canonicalYukawaCoefficientPrimitiveCardPacket :=
    eq_canonicalYukawaCoefficientPrimitiveCardPacket_of_sourceEquations P hP
  have hf' : f = yukawaSectorInformationIncidence :=
    yukawaSectorEndpointSignaturePreservingSchedule_unique f hf
  subst P
  rw [hf']
  ext y
  simp [coefficientScheduleYukawaDepthTableCandidate,
    selectedYukawaDepthTableCandidate]
  simpa [canonicalPrimitiveCardYukawaDepthStencilCoefficientVector] using
    coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_sourceEquations
      yukawaSectorInformationIncidence
      yukawaSectorInformationIncidence_endpointPreserving y

/-- THEOREM 3: the SU(7) primitive depth-producer surface is exactly the
selected table. -/
theorem su7PrimitiveYukawaDepthProducerSurface_iff_selected
    (T : YukawaDepthTableCandidate) :
    SU7PrimitiveYukawaDepthProducerSurface T ↔
      T = selectedYukawaDepthTableCandidate := by
  constructor
  · exact eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T
  · intro hT
    rw [hT]
    exact selectedYukawaDepthTableCandidate_su7PrimitiveProducer

/-- THEOREM 4: the SU(7) primitive producer surface has no table-level
freedom. -/
theorem su7PrimitiveYukawaDepthProducerSurface_noFree :
    NoContinuousFreeYukawaDepthTableParameters
      SU7PrimitiveYukawaDepthProducerSurface := by
  intro T U hT hU
  rw [eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T hT,
    eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer U hU]

/-! ## Forced nine-depth output -/

/-- THEOREM 5: any accepted SU(7) primitive producer table has the nine named
integer depths. -/
theorem su7PrimitiveYukawaDepthProducerSurface_namedDepths
    (T : YukawaDepthTableCandidate)
    (hT : SU7PrimitiveYukawaDepthProducerSurface T) :
    T.depth .top = 50 ∧
      T.depth .bottom = 346 ∧
      T.depth .tau = 372 ∧
      T.depth .charm = 489 ∧
      T.depth .muon = 583 ∧
      T.depth .strange = 682 ∧
      T.depth .down = 880 ∧
      T.depth .up = 908 ∧
      T.depth .electron = 982 := by
  rw [eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T hT]
  norm_num [selectedYukawaDepthTableCandidate,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth]

/-- THEOREM 6: any accepted SU(7) primitive producer table has the documented
mass-order depth list. -/
theorem su7PrimitiveYukawaDepthProducerSurface_massOrder_eq
    (T : YukawaDepthTableCandidate)
    (hT : SU7PrimitiveYukawaDepthProducerSurface T) :
    T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rw [eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T hT]
  exact selectedYukawaDepthTableCandidate_massOrder_eq

/-! ## CKM/Jarlskog consequence from the same producer -/

/-- THEOREM 7: any accepted SU(7) primitive producer table has typed
Jarlskog four-product depth sum `386`. -/
theorem su7PrimitiveYukawaDepthProducerSurface_jarlskog_eq_386
    (T : YukawaDepthTableCandidate)
    (hT : SU7PrimitiveYukawaDepthProducerSurface T) :
    ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int) := by
  rw [eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T hT]
  exact selectedCKMJarlskogFourProductDepthSum_eq_386

/-- THEOREM 8: the same accepted table also computes the table-level CKM depth
sum `386`. -/
theorem su7PrimitiveYukawaDepthProducerSurface_ckmTableSum_eq_386
    (T : YukawaDepthTableCandidate)
    (hT : SU7PrimitiveYukawaDepthProducerSurface T) :
    ckmDepthSum_fromYukawaDepthTable T = (ckmCPDepthSum : Int) := by
  rw [eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T hT]
  exact selectedYukawaDepthTableCandidate_ckmDepthSum_eq_386

/-! ## Receipt -/

/-- Compact receipt: the finite SU(7) primitive depth-producer surface is a
singleton and forces both the nine Yukawa depths and the typed Jarlskog sum. -/
structure SU7PrimitiveYukawaDepthProducerCertificate where
  selected_surface :
    SU7PrimitiveYukawaDepthProducerSurface
      selectedYukawaDepthTableCandidate
  surface_iff_selected :
    ∀ T : YukawaDepthTableCandidate,
      SU7PrimitiveYukawaDepthProducerSurface T ↔
        T = selectedYukawaDepthTableCandidate
  no_free :
    NoContinuousFreeYukawaDepthTableParameters
      SU7PrimitiveYukawaDepthProducerSurface
  named_depths :
    ∀ T : YukawaDepthTableCandidate,
      SU7PrimitiveYukawaDepthProducerSurface T ->
        T.depth .top = 50 ∧
          T.depth .bottom = 346 ∧
          T.depth .tau = 372 ∧
          T.depth .charm = 489 ∧
          T.depth .muon = 583 ∧
          T.depth .strange = 682 ∧
          T.depth .down = 880 ∧
          T.depth .up = 908 ∧
          T.depth .electron = 982
  mass_order :
    ∀ T : YukawaDepthTableCandidate,
      SU7PrimitiveYukawaDepthProducerSurface T ->
        T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  typed_jarlskog_sum :
    ∀ T : YukawaDepthTableCandidate,
      SU7PrimitiveYukawaDepthProducerSurface T ->
        ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int)
  table_ckm_sum :
    ∀ T : YukawaDepthTableCandidate,
      SU7PrimitiveYukawaDepthProducerSurface T ->
        ckmDepthSum_fromYukawaDepthTable T = (ckmCPDepthSum : Int)

/-- THEOREM 9: SU(7) primitive Yukawa-depth producer certificate. -/
theorem su7PrimitiveYukawaDepthProducerCertificate :
    SU7PrimitiveYukawaDepthProducerCertificate where
  selected_surface := selectedYukawaDepthTableCandidate_su7PrimitiveProducer
  surface_iff_selected := su7PrimitiveYukawaDepthProducerSurface_iff_selected
  no_free := su7PrimitiveYukawaDepthProducerSurface_noFree
  named_depths := su7PrimitiveYukawaDepthProducerSurface_namedDepths
  mass_order := su7PrimitiveYukawaDepthProducerSurface_massOrder_eq
  typed_jarlskog_sum :=
    su7PrimitiveYukawaDepthProducerSurface_jarlskog_eq_386
  table_ckm_sum :=
    su7PrimitiveYukawaDepthProducerSurface_ckmTableSum_eq_386

end StandardModelConstraint
end SaturationMonoid
