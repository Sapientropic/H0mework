/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import Mathlib.Data.List.Basic

/-!
# Fixed Citi Bike cross-season residual observation

This file records the smallest downstream readout shared by the April and
February reports.  It is deliberately not a space producer: the geographic
district, SVD embedding and k-means labels remain observer coordinates.

The machine claims here are only about the fixed reported rows: both seasonal
residual fibres are nonempty, their station bearers turn over completely, and
the common near-East-River crossing mechanism survives that turnover.  In
particular, the rejected claim that the four April stations persist into the
winter is made false explicitly.
-/

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace M11
namespace Empirical
namespace CitiBike

/-- The two independently observed snapshots. -/
inductive Season where
  | april2026
  | february2026
  deriving DecidableEq, Repr

/-- Station identity is kept at the reported normalized station-id gauge. -/
inductive Station where
  | grahamConselyea
  | queensPlazaCrescent
  | jayYork
  | roeblingSouthFourth
  | monroeBedford
  | clintonJoralemon
  | grahamGrand
  deriving DecidableEq, Repr

/-- Coarse geographic observer coordinate used by the reports. -/
inductive GeographicDistrict where
  | brooklynInland
  | brooklynWaterfront
  | queens
  deriving DecidableEq, Repr

/-- Dominant flow-community observer coordinate used by the reports. -/
inductive DominantFlowDistrict where
  | manhattanSouth
  | manhattanMidtown
  deriving DecidableEq, Repr

/-- The retained mechanism class; this is weaker than station persistence. -/
inductive CrossingMechanism where
  | nearEastRiverBridgeOrWaterfront
  deriving DecidableEq, Repr

/-- One fixed row read from a seasonal report.

`stableSeeds` is descriptive observer evidence, not source authority. -/
structure ResidualObservation where
  station : Station
  geographicDistrict : GeographicDistrict
  dominantFlowDistrict : DominantFlowDistrict
  monthlyEvents : Nat
  stableSeeds : Nat
  observedSeeds : Nat
  mechanism : CrossingMechanism
  deriving DecidableEq, Repr

/-- April 2026 reference-seed cross-river residual rows. -/
def aprilResiduals : List ResidualObservation :=
  [ { station := .grahamConselyea
      geographicDistrict := .brooklynInland
      dominantFlowDistrict := .manhattanSouth
      monthlyEvents := 9932
      stableSeeds := 6
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront },
    { station := .queensPlazaCrescent
      geographicDistrict := .queens
      dominantFlowDistrict := .manhattanMidtown
      monthlyEvents := 9070
      stableSeeds := 10
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront },
    { station := .jayYork
      geographicDistrict := .brooklynWaterfront
      dominantFlowDistrict := .manhattanSouth
      monthlyEvents := 8754
      stableSeeds := 10
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront },
    { station := .roeblingSouthFourth
      geographicDistrict := .brooklynInland
      dominantFlowDistrict := .manhattanSouth
      monthlyEvents := 8566
      stableSeeds := 6
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront } ]

/-- February 2026 reference-seed cross-river residual rows. -/
def februaryResiduals : List ResidualObservation :=
  [ { station := .monroeBedford
      geographicDistrict := .brooklynInland
      dominantFlowDistrict := .manhattanSouth
      monthlyEvents := 2922
      stableSeeds := 10
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront },
    { station := .clintonJoralemon
      geographicDistrict := .brooklynWaterfront
      dominantFlowDistrict := .manhattanSouth
      monthlyEvents := 2757
      stableSeeds := 10
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront },
    { station := .grahamGrand
      geographicDistrict := .brooklynInland
      dominantFlowDistrict := .manhattanSouth
      monthlyEvents := 2636
      stableSeeds := 10
      observedSeeds := 10
      mechanism := .nearEastRiverBridgeOrWaterfront } ]

/-- Seasonal observation selected by the fixed downstream observer. -/
def residualsAt : Season → List ResidualObservation
  | .april2026 => aprilResiduals
  | .february2026 => februaryResiduals

/-- Snapshot station bearers, forgetting all observer annotations. -/
def stationBearersAt (season : Season) : List Station :=
  (residualsAt season).map ResidualObservation.station

/-- April has exactly the four reference-seed residual rows recorded in the
corrected multi-seed report. -/
@[simp] theorem aprilResiduals_length : aprilResiduals.length = 4 := by
  rfl

/-- February has exactly the three winter residual rows. -/
@[simp] theorem februaryResiduals_length : februaryResiduals.length = 3 := by
  rfl

/-- The residual class is nonempty in April. -/
theorem april_residual_class_nonempty : aprilResiduals ≠ [] := by
  decide

/-- The residual class is nonempty in February. -/
theorem february_residual_class_nonempty : februaryResiduals ≠ [] := by
  decide

/-- Every reported residual row carries the same near-river crossing
mechanism, independently of the station bearer. -/
theorem mechanism_persists
    (season : Season)
    (observation : ResidualObservation)
    (observed : observation ∈ residualsAt season) :
    observation.mechanism = .nearEastRiverBridgeOrWaterfront := by
  cases season with
  | april2026 =>
      simp only [residualsAt, aprilResiduals, List.mem_cons,
        List.not_mem_nil, or_false] at observed
      rcases observed with equality | equality | equality | equality <;>
        subst observation <;> rfl
  | february2026 =>
      simp only [residualsAt, februaryResiduals, List.mem_cons,
        List.not_mem_nil, or_false] at observed
      rcases observed with equality | equality | equality <;>
        subst observation <;> rfl

/-- All winter residual rows are stable under all ten fixed observer seeds. -/
theorem february_all_seed_stable
    (observation : ResidualObservation)
    (observed : observation ∈ februaryResiduals) :
    observation.stableSeeds = observation.observedSeeds := by
  simp only [februaryResiduals, List.mem_cons, List.not_mem_nil, or_false]
    at observed
  rcases observed with equality | equality | equality <;>
    subst observation <;> rfl

/-- No station bearer in the April residual snapshot survives as a member of
the February residual snapshot. -/
theorem snapshot_bearers_completely_turn_over :
    List.Disjoint
      (stationBearersAt .april2026)
      (stationBearersAt .february2026) := by
  simp [List.Disjoint, stationBearersAt, residualsAt, aprilResiduals,
    februaryResiduals]

/-- Strong negative control: the two residual snapshots are not the same
station set. -/
theorem residual_snapshot_not_persistent :
    stationBearersAt .april2026 ≠ stationBearersAt .february2026 := by
  decide

/-- Cross-season consumer: the residual class survives, the mechanism
survives, and its station bearer does not. -/
theorem crossSeason_residual_class_survives_with_bearer_turnover :
    ∃ aprilObservation ∈ aprilResiduals,
      ∃ februaryObservation ∈ februaryResiduals,
        aprilObservation.station ≠ februaryObservation.station ∧
        aprilObservation.mechanism = februaryObservation.mechanism := by
  refine ⟨aprilResiduals.head april_residual_class_nonempty,
    List.head_mem april_residual_class_nonempty, ?_⟩
  refine ⟨februaryResiduals.head february_residual_class_nonempty,
    List.head_mem february_residual_class_nonempty, ?_⟩
  decide

end CitiBike
end Empirical
end M11
end Society
end Regression
end ProcessGame
end SaturationMonoid
