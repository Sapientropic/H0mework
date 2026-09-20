import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P589
import H0mework.Physics.RepresentationSources.P513

/-!
# Proposition 590: Yukawa interaction sectors as an SU(7) incidence triad

P589 sourced the Yukawa depth stencil axes from the 4D Poincare generation
coordinate and the `YukawaInteractionSector` coordinate.  This file lowers the
second axis one carrier layer:

* `upLike`, `downLike`, and `chargedLepton` are identified with the three
  SU(7) off-diagonal incidences
  `color-positive`, `color-negative`, and `positive-negative`;
* those incidences generate the right-side matter slots
  `u^c`, `d^c`, and `e^c`;
* the P589 centered sector coordinate is exactly the centered coordinate on
  this SU(7) incidence triad.

Boundary: this proves the finite incidence-triad source for the sector axis.
It does not yet prove that SU(7) dynamics uniquely selects this triad or this
orientation among all possible endpoint-signature conventions.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open InformationMatterProjection

/-! ## The SU(7) incidence triad behind Yukawa interaction sectors -/

/-- The SU(7) information-incidence source of each Yukawa interaction sector. -/
def yukawaSectorInformationIncidence :
    YukawaInteractionSector -> InformationSlot
  | .upLike => .colorPositiveSinglet
  | .downLike => .colorNegativeSinglet
  | .chargedLepton => .positiveNegativeSinglet

/-- The generated matter slot selected by each Yukawa interaction sector. -/
def yukawaSectorMatterSlot :
    YukawaInteractionSector -> MatterSlot
  | .upLike => .upConjugate
  | .downLike => .downConjugate
  | .chargedLepton => .electronConjugate

/-- THEOREM 1: the sector-incidence map generates exactly the sector matter
slot. -/
theorem yukawaSectorInformationIncidence_generatesMatterSlot
    (s : YukawaInteractionSector) :
    generatedSlotOfIncidence (yukawaSectorInformationIncidence s) =
      yukawaSectorMatterSlot s := by
  cases s <;> rfl

/-- THEOREM 2: the sector matter slot has the endpoint signature of its
sector incidence. -/
theorem yukawaSectorMatterSlot_endpointSignature_eq
    (s : YukawaInteractionSector) :
    generatedSlotEndpointSignature (yukawaSectorMatterSlot s) =
      SU7BlockIncidence.endpoints
        (yukawaSectorInformationIncidence s) := by
  cases s <;> rfl

/-- THEOREM 3: within the SU(7) generated-slot schedule, a sector incidence is
uniquely recovered from the endpoint signature of its matter slot. -/
theorem yukawaSectorInformationIncidence_unique_by_endpointSignature
    (s : YukawaInteractionSector) (i : InformationSlot)
    (h :
      generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
        generatedSlotEndpointSignature (yukawaSectorMatterSlot s)) :
    i = yukawaSectorInformationIncidence s := by
  cases s <;> cases i <;>
    simp [generatedSlotOfIncidence, generatedSlotEndpointSignature,
      yukawaSectorInformationIncidence, yukawaSectorMatterSlot] at h ⊢

/-! ## The triad as a finite subtype -/

/-- The three information incidences used by the Yukawa interaction sectors. -/
def IsYukawaSectorInformationIncidence (i : InformationSlot) : Prop :=
  i = .colorPositiveSinglet ∨
    i = .colorNegativeSinglet ∨
      i = .positiveNegativeSinglet

/-- Decidability for the finite Yukawa-sector incidence predicate. -/
instance instDecidablePredIsYukawaSectorInformationIncidence :
    DecidablePred IsYukawaSectorInformationIncidence := by
  intro i
  unfold IsYukawaSectorInformationIncidence
  infer_instance

/-- The sector incidence as an element of the three-incidence subtype. -/
def yukawaSectorInformationIncidenceSubtype
    (s : YukawaInteractionSector) :
    { i : InformationSlot // IsYukawaSectorInformationIncidence i } :=
  match s with
  | .upLike =>
      ⟨.colorPositiveSinglet, by
        simp [IsYukawaSectorInformationIncidence]⟩
  | .downLike =>
      ⟨.colorNegativeSinglet, by
        simp [IsYukawaSectorInformationIncidence]⟩
  | .chargedLepton =>
      ⟨.positiveNegativeSinglet, by
        simp [IsYukawaSectorInformationIncidence]⟩

/-- Read a Yukawa interaction sector back from a triad incidence. -/
def yukawaInteractionSectorOfInformationIncidence :
    { i : InformationSlot // IsYukawaSectorInformationIncidence i } ->
      YukawaInteractionSector
  | ⟨.colorWeak, h⟩ => by
      exfalso
      simp [IsYukawaSectorInformationIncidence] at h
  | ⟨.colorPositiveSinglet, _⟩ => .upLike
  | ⟨.colorNegativeSinglet, _⟩ => .downLike
  | ⟨.weakPositiveSinglet, h⟩ => by
      exfalso
      simp [IsYukawaSectorInformationIncidence] at h
  | ⟨.weakNegativeSinglet, h⟩ => by
      exfalso
      simp [IsYukawaSectorInformationIncidence] at h
  | ⟨.positiveNegativeSinglet, _⟩ => .chargedLepton

/-- THEOREM 4: the three Yukawa interaction sectors are exactly the three
selected SU(7) information incidences. -/
def yukawaInteractionSectorInformationIncidenceEquiv :
    YukawaInteractionSector ≃
      { i : InformationSlot // IsYukawaSectorInformationIncidence i } where
  toFun := yukawaSectorInformationIncidenceSubtype
  invFun := yukawaInteractionSectorOfInformationIncidence
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro i
    rcases i with ⟨i, hi⟩
    cases i <;>
      simp [yukawaInteractionSectorOfInformationIncidence,
        yukawaSectorInformationIncidenceSubtype,
        IsYukawaSectorInformationIncidence] at hi ⊢

/-- THEOREM 5: the incidence triad has exactly three elements because it is
equivalent to `YukawaInteractionSector`. -/
theorem yukawaSectorInformationIncidenceTriad_card :
    Fintype.card
      { i : InformationSlot // IsYukawaSectorInformationIncidence i } = 3 := by
  rw [← Fintype.card_congr
    yukawaInteractionSectorInformationIncidenceEquiv]
  exact YukawaInteractionSector.card

/-! ## Sector coordinate from the incidence triad -/

/-- Centered coordinate on the SU(7) Yukawa-sector incidence triad. -/
def yukawaSectorInformationIncidenceCoordinateZ
    (i : { i : InformationSlot // IsYukawaSectorInformationIncidence i }) :
    Int :=
  match i.1 with
  | .colorPositiveSinglet => -1
  | .colorNegativeSinglet => 0
  | .positiveNegativeSinglet => 1
  | .colorWeak => 0
  | .weakPositiveSinglet => 0
  | .weakNegativeSinglet => 0

/-- THEOREM 6: the P589/P584 sector coordinate is exactly the centered
coordinate on the SU(7) incidence triad. -/
theorem yukawaSectorDepthCoordinate_eq_informationIncidenceCoordinate
    (s : YukawaInteractionSector) :
    yukawaSectorDepthCoordinate s =
      yukawaSectorInformationIncidenceCoordinateZ
        (yukawaSectorInformationIncidenceSubtype s) := by
  cases s <;> rfl

/-- THEOREM 7: the sector matter slots have component multiplicities
`3, 3, 1`, read from the same generated matter carrier as P513. -/
theorem yukawaSectorMatterSlot_componentMultiplicity_table :
    matterSlotComponentMultiplicity
        (yukawaSectorMatterSlot .upLike) = 3 ∧
      matterSlotComponentMultiplicity
        (yukawaSectorMatterSlot .downLike) = 3 ∧
      matterSlotComponentMultiplicity
        (yukawaSectorMatterSlot .chargedLepton) = 1 := by
  norm_num [yukawaSectorMatterSlot, matterSlotComponentMultiplicity]

/-- THEOREM 8: the same multiplicities are endpoint block products in the
`3+2+1+1` SU(7) carrier. -/
theorem yukawaSectorMatterSlot_endpointBlockProduct_table :
    matterSlotEndpointBlockProduct
        (yukawaSectorMatterSlot .upLike) = 3 ∧
      matterSlotEndpointBlockProduct
        (yukawaSectorMatterSlot .downLike) = 3 ∧
      matterSlotEndpointBlockProduct
        (yukawaSectorMatterSlot .chargedLepton) = 1 := by
  norm_num [yukawaSectorMatterSlot, matterSlotEndpointBlockProduct,
    generatedSlotEndpointSignature, carrierBlockCard]

/-! ## Bundled receipt -/

/-- Compact receipt: the Yukawa sector axis is the centered coordinate of a
three-incidence SU(7) information/matter triad. -/
structure YukawaSectorIncidenceTriadReceipt where
  generates_matter_slot :
    ∀ s : YukawaInteractionSector,
      generatedSlotOfIncidence (yukawaSectorInformationIncidence s) =
        yukawaSectorMatterSlot s
  endpoint_signature :
    ∀ s : YukawaInteractionSector,
      generatedSlotEndpointSignature (yukawaSectorMatterSlot s) =
        SU7BlockIncidence.endpoints
          (yukawaSectorInformationIncidence s)
  unique_by_endpoint :
    ∀ s : YukawaInteractionSector, ∀ i : InformationSlot,
      generatedSlotEndpointSignature (generatedSlotOfIncidence i) =
        generatedSlotEndpointSignature (yukawaSectorMatterSlot s) ->
          i = yukawaSectorInformationIncidence s
  sector_incidence_equiv :
    Nonempty
      (YukawaInteractionSector ≃
        { i : InformationSlot // IsYukawaSectorInformationIncidence i })
  triad_card :
    Fintype.card
      { i : InformationSlot // IsYukawaSectorInformationIncidence i } = 3
  coordinate_source :
    ∀ s : YukawaInteractionSector,
      yukawaSectorDepthCoordinate s =
        yukawaSectorInformationIncidenceCoordinateZ
          (yukawaSectorInformationIncidenceSubtype s)
  component_multiplicity :
    matterSlotComponentMultiplicity
        (yukawaSectorMatterSlot .upLike) = 3 ∧
      matterSlotComponentMultiplicity
        (yukawaSectorMatterSlot .downLike) = 3 ∧
      matterSlotComponentMultiplicity
        (yukawaSectorMatterSlot .chargedLepton) = 1
  endpoint_block_product :
    matterSlotEndpointBlockProduct
        (yukawaSectorMatterSlot .upLike) = 3 ∧
      matterSlotEndpointBlockProduct
        (yukawaSectorMatterSlot .downLike) = 3 ∧
      matterSlotEndpointBlockProduct
        (yukawaSectorMatterSlot .chargedLepton) = 1

/-- THEOREM 9: SU(7) incidence-triad receipt for the Yukawa sector axis. -/
theorem yukawaSectorIncidenceTriadReceipt :
    YukawaSectorIncidenceTriadReceipt where
  generates_matter_slot :=
    yukawaSectorInformationIncidence_generatesMatterSlot
  endpoint_signature :=
    yukawaSectorMatterSlot_endpointSignature_eq
  unique_by_endpoint :=
    yukawaSectorInformationIncidence_unique_by_endpointSignature
  sector_incidence_equiv :=
    ⟨yukawaInteractionSectorInformationIncidenceEquiv⟩
  triad_card :=
    yukawaSectorInformationIncidenceTriad_card
  coordinate_source :=
    yukawaSectorDepthCoordinate_eq_informationIncidenceCoordinate
  component_multiplicity :=
    yukawaSectorMatterSlot_componentMultiplicity_table
  endpoint_block_product :=
    yukawaSectorMatterSlot_endpointBlockProduct_table

end StandardModelConstraint
end SaturationMonoid
