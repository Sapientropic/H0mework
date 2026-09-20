import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P590

/-!
# Proposition 591: endpoint-signature uniqueness of the Yukawa-sector axis

P590 identified the `YukawaInteractionSector` axis with a three-incidence
subcarrier of the SU(7) `3+2+1+1` block-incidence carrier.  This file proves
the next finite uniqueness statement:

* any sector-to-incidence schedule that preserves the endpoint signatures of
  the sector matter slots `u^c`, `d^c`, and `e^c` is exactly the P590 schedule;
* therefore the centered sector coordinate used by the Yukawa depth stencil is
  the unique coordinate induced by such an endpoint-signature preserving
  schedule.

Boundary: this is still finite endpoint-signature uniqueness.  It does not
claim that the endpoint-signature convention itself is derived from dynamics;
it proves that once the SU(7) endpoint signatures for the three sector matter
slots are fixed, the sector-axis orientation has no remaining freedom.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open InformationMatterProjection

/-! ## A total coordinate on information incidences -/

/-- Total centered coordinate on SU(7) information incidences.  It agrees with
the Yukawa-sector triad coordinate on the three sector incidences and sends the
other incidences to `0` because they are outside this coordinate axis. -/
def yukawaSectorInformationIncidenceTotalCoordinateZ :
    InformationSlot -> Int
  | .colorPositiveSinglet => -1
  | .colorNegativeSinglet => 0
  | .positiveNegativeSinglet => 1
  | .colorWeak => 0
  | .weakPositiveSinglet => 0
  | .weakNegativeSinglet => 0

/-- THEOREM 1: the subtype coordinate from P590 is the restriction of the
total information-incidence coordinate. -/
theorem yukawaSectorInformationIncidenceCoordinateZ_eq_total
    (i : { i : InformationSlot // IsYukawaSectorInformationIncidence i }) :
    yukawaSectorInformationIncidenceCoordinateZ i =
      yukawaSectorInformationIncidenceTotalCoordinateZ i.1 := by
  rcases i with ⟨i, hi⟩
  cases i <;>
    simp [IsYukawaSectorInformationIncidence,
      yukawaSectorInformationIncidenceCoordinateZ,
      yukawaSectorInformationIncidenceTotalCoordinateZ] at hi ⊢

/-- THEOREM 2: P584/P589's sector coordinate is the total coordinate of the
P590 SU(7) sector incidence. -/
theorem yukawaSectorDepthCoordinate_eq_totalIncidenceCoordinate
    (s : YukawaInteractionSector) :
    yukawaSectorDepthCoordinate s =
      yukawaSectorInformationIncidenceTotalCoordinateZ
        (yukawaSectorInformationIncidence s) := by
  cases s <;> rfl

/-! ## Endpoint-signature preserving schedules are unique -/

/-- A sector-to-incidence schedule preserves endpoint signatures when it sends
each sector to an incidence generating the same endpoint signature as that
sector's matter slot. -/
def YukawaSectorEndpointSignaturePreservingSchedule
    (f : YukawaInteractionSector -> InformationSlot) : Prop :=
  ∀ s : YukawaInteractionSector,
    generatedSlotEndpointSignature (generatedSlotOfIncidence (f s)) =
      generatedSlotEndpointSignature (yukawaSectorMatterSlot s)

/-! ## Incidence grammar forces endpoint preservation -/

/-- A stronger representation/encoding-facing grammar: the sector incidence
schedule must generate the actual Yukawa-sector matter slot, not merely match a
later depth table. -/
def YukawaSectorGeneratedMatterSlotSchedule
    (f : YukawaInteractionSector -> InformationSlot) : Prop :=
  ∀ s : YukawaInteractionSector,
    generatedSlotOfIncidence (f s) = yukawaSectorMatterSlot s

/-- Generated matter-slot incidence grammar implies endpoint-signature
preservation.  This is the lower schedule entrance for representation /
encoding routes: prove generated matter slots, then endpoint preservation is a
theorem. -/
theorem yukawaSectorEndpointPreserving_of_generatedMatterSlotSchedule
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorGeneratedMatterSlotSchedule f) :
    YukawaSectorEndpointSignaturePreservingSchedule f := by
  intro s
  rw [hf s]

/-- The P590 incidence schedule satisfies the stronger generated matter-slot
grammar. -/
theorem yukawaSectorInformationIncidence_generatedMatterSlot :
    YukawaSectorGeneratedMatterSlotSchedule
      yukawaSectorInformationIncidence :=
  yukawaSectorInformationIncidence_generatesMatterSlot

/-- THEOREM 3: the P590 schedule is endpoint-signature preserving. -/
theorem yukawaSectorInformationIncidence_endpointPreserving :
    YukawaSectorEndpointSignaturePreservingSchedule
      yukawaSectorInformationIncidence := by
  intro s
  cases s <;> rfl

/-- THEOREM 4: any endpoint-signature preserving sector schedule is exactly
P590's SU(7) incidence schedule. -/
theorem yukawaSectorEndpointSignaturePreservingSchedule_unique
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    f = yukawaSectorInformationIncidence := by
  funext s
  exact yukawaSectorInformationIncidence_unique_by_endpointSignature
    s (f s) (hf s)

/-- Any generated matter-slot sector schedule is exactly P590's SU(7)
incidence schedule. -/
theorem yukawaSectorGeneratedMatterSlotSchedule_unique
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorGeneratedMatterSlotSchedule f) :
    f = yukawaSectorInformationIncidence :=
  yukawaSectorEndpointSignaturePreservingSchedule_unique f
    (yukawaSectorEndpointPreserving_of_generatedMatterSlotSchedule f hf)

/-- THEOREM 5: every endpoint-signature preserving schedule lands inside the
P590 three-incidence triad. -/
theorem yukawaSectorEndpointSignaturePreservingSchedule_lands_in_triad
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (s : YukawaInteractionSector) :
    IsYukawaSectorInformationIncidence (f s) := by
  rw [yukawaSectorEndpointSignaturePreservingSchedule_unique f hf]
  cases s <;>
    simp [yukawaSectorInformationIncidence,
      IsYukawaSectorInformationIncidence]

/-! ## Coordinate orientation is forced by endpoint preservation -/

/-- THEOREM 6: reading the total incidence coordinate along any
endpoint-signature preserving schedule gives the same sector coordinate. -/
theorem yukawaSectorDepthCoordinate_eq_totalCoordinate_of_endpointPreserving
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (s : YukawaInteractionSector) :
    yukawaSectorDepthCoordinate s =
      yukawaSectorInformationIncidenceTotalCoordinateZ (f s) := by
  rw [yukawaSectorEndpointSignaturePreservingSchedule_unique f hf]
  exact yukawaSectorDepthCoordinate_eq_totalIncidenceCoordinate s

/-- THEOREM 7: a sector coordinate read from any endpoint-signature preserving
schedule is uniquely P584/P589's sector coordinate. -/
theorem yukawaSectorCoordinate_unique_of_endpointPreserving
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (c : YukawaInteractionSector -> Int)
    (hc : ∀ s : YukawaInteractionSector,
      c s = yukawaSectorInformationIncidenceTotalCoordinateZ (f s)) :
    c = yukawaSectorDepthCoordinate := by
  funext s
  rw [hc s]
  exact (yukawaSectorDepthCoordinate_eq_totalCoordinate_of_endpointPreserving
    f hf s).symm

/-- THEOREM 8: there is no alternative endpoint-preserving orientation for the
three sector coordinate values. -/
theorem yukawaSectorCoordinateValues_forced_by_endpointPreserving
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    yukawaSectorInformationIncidenceTotalCoordinateZ (f .upLike) = -1 ∧
      yukawaSectorInformationIncidenceTotalCoordinateZ (f .downLike) = 0 ∧
      yukawaSectorInformationIncidenceTotalCoordinateZ
        (f .chargedLepton) = 1 := by
  rw [yukawaSectorEndpointSignaturePreservingSchedule_unique f hf]
  constructor
  · rfl
  constructor <;> rfl

/-! ## Bundled receipt -/

/-- Compact receipt: once the endpoint signatures of the three Yukawa-sector
matter slots are fixed, the sector incidence schedule and centered coordinate
orientation are unique. -/
structure YukawaSectorEndpointOrientationUniquenessReceipt where
  total_coordinate_restricts_to_triad :
    ∀ i : { i : InformationSlot // IsYukawaSectorInformationIncidence i },
      yukawaSectorInformationIncidenceCoordinateZ i =
        yukawaSectorInformationIncidenceTotalCoordinateZ i.1
  selected_schedule_preserves_endpoint :
    YukawaSectorEndpointSignaturePreservingSchedule
      yukawaSectorInformationIncidence
  schedule_unique :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      YukawaSectorEndpointSignaturePreservingSchedule f ->
        f = yukawaSectorInformationIncidence
  schedule_lands_in_triad :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
        ∀ s : YukawaInteractionSector,
          IsYukawaSectorInformationIncidence (f s)
  coordinate_forced :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
        ∀ s : YukawaInteractionSector,
          yukawaSectorDepthCoordinate s =
            yukawaSectorInformationIncidenceTotalCoordinateZ (f s)
  coordinate_unique :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
        ∀ c : YukawaInteractionSector -> Int,
          (∀ s : YukawaInteractionSector,
            c s = yukawaSectorInformationIncidenceTotalCoordinateZ (f s)) ->
              c = yukawaSectorDepthCoordinate
  coordinate_values :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      YukawaSectorEndpointSignaturePreservingSchedule f ->
        yukawaSectorInformationIncidenceTotalCoordinateZ (f .upLike) = -1 ∧
          yukawaSectorInformationIncidenceTotalCoordinateZ (f .downLike) = 0 ∧
          yukawaSectorInformationIncidenceTotalCoordinateZ
            (f .chargedLepton) = 1

/-- THEOREM 9: endpoint-signature orientation uniqueness receipt. -/
theorem yukawaSectorEndpointOrientationUniquenessReceipt :
    YukawaSectorEndpointOrientationUniquenessReceipt where
  total_coordinate_restricts_to_triad :=
    yukawaSectorInformationIncidenceCoordinateZ_eq_total
  selected_schedule_preserves_endpoint :=
    yukawaSectorInformationIncidence_endpointPreserving
  schedule_unique :=
    yukawaSectorEndpointSignaturePreservingSchedule_unique
  schedule_lands_in_triad :=
    yukawaSectorEndpointSignaturePreservingSchedule_lands_in_triad
  coordinate_forced :=
    yukawaSectorDepthCoordinate_eq_totalCoordinate_of_endpointPreserving
  coordinate_unique :=
    yukawaSectorCoordinate_unique_of_endpointPreserving
  coordinate_values :=
    yukawaSectorCoordinateValues_forced_by_endpointPreserving

end StandardModelConstraint
end SaturationMonoid
