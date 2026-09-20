import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.Admission.StandingPullback

/-!
# Raw temporal standing for sourced claims

Freshness is metadata standing, not Lorentzian spacetime and not affine
relaxation time.  This raw record stores only a source timestamp, an
observation timestamp, and an allowed age.  Causal availability and the age
bound are computed as two independent native conditions; `StandingFresh` is
their conjunction.

The successful temporal operation advances observation time only while both
the source and result have valid standing.  Its generated standing identity
therefore preserves `StandingFresh`.  No seven-facet field, caller-provided
validity proposition, or final audit certificate is stored in the record.
-/

namespace SaturationMonoid
namespace PhysicsCore

structure RawTemporalStanding where
  sourcedAt : Nat
  observedAt : Nat
  maxAge : Nat
  deriving DecidableEq, Repr

namespace RawTemporalStanding

/-- A source cannot support a claim before it exists. -/
def CausallyAvailable (S : RawTemporalStanding) : Prop :=
  S.sourcedAt ≤ S.observedAt

/-- The computed source age remains inside the declared validity window. -/
def AgeWithinBound (S : RawTemporalStanding) : Prop :=
  S.observedAt - S.sourcedAt ≤ S.maxAge

/-- Temporal standing is the conjunction of causal availability and bounded
source age. -/
def StandingFresh (S : RawTemporalStanding) : Prop :=
  S.CausallyAvailable ∧ S.AgeWithinBound

instance standingFreshDecidable (S : RawTemporalStanding) :
    Decidable S.StandingFresh := by
  unfold StandingFresh CausallyAvailable AgeWithinBound
  infer_instance

inductive TemporalStandingCoordinate where
  | causalAvailability
  | ageBound
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    (S : RawTemporalStanding) : TemporalStandingCoordinate → Prop
  | .causalAvailability => S.CausallyAvailable
  | .ageBound => S.AgeWithinBound

theorem standingFresh_iff_all_coordinates (S : RawTemporalStanding) :
    S.StandingFresh ↔ ∀ coordinate, S.CoordinateHolds coordinate := by
  constructor
  · rintro ⟨hcausal, hage⟩ coordinate
    cases coordinate with
    | causalAvailability => exact hcausal
    | ageBound => exact hage
  · intro hall
    exact ⟨hall .causalAvailability, hall .ageBound⟩

theorem not_standingFresh_iff_exists_failed_coordinate
    (S : RawTemporalStanding) :
    ¬ S.StandingFresh ↔
      ∃ coordinate, ¬ S.CoordinateHolds coordinate := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot (S.standingFresh_iff_all_coordinates.mpr hnone)
  · rintro ⟨coordinate, hcoordinate⟩ hfresh
    exact hcoordinate
      (S.standingFresh_iff_all_coordinates.mp hfresh coordinate)

def OnlyFails
    (S : RawTemporalStanding) (failed : TemporalStandingCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ coordinate, coordinate ≠ failed → S.CoordinateHolds coordinate

namespace Toy

def fresh : RawTemporalStanding where
  sourcedAt := 2
  observedAt := 4
  maxAge := 3

def futureSource : RawTemporalStanding where
  sourcedAt := 2
  observedAt := 1
  maxAge := 1

def staleSource : RawTemporalStanding where
  sourcedAt := 0
  observedAt := 2
  maxAge := 1

theorem fresh_valid : fresh.StandingFresh := by
  norm_num [StandingFresh, CausallyAvailable, AgeWithinBound, fresh]

theorem futureSource_not_causal : ¬ futureSource.CausallyAvailable := by
  norm_num [CausallyAvailable, futureSource]

theorem futureSource_ageWithinBound : futureSource.AgeWithinBound := by
  norm_num [AgeWithinBound, futureSource]

theorem staleSource_causal : staleSource.CausallyAvailable := by
  norm_num [CausallyAvailable, staleSource]

theorem staleSource_not_ageWithinBound : ¬ staleSource.AgeWithinBound := by
  norm_num [AgeWithinBound, staleSource]

theorem futureSource_onlyFails :
    futureSource.OnlyFails .causalAvailability := by
  refine ⟨futureSource_not_causal, ?_⟩
  intro coordinate hcoordinate
  cases coordinate with
  | causalAvailability => exact (hcoordinate rfl).elim
  | ageBound => exact futureSource_ageWithinBound

theorem staleSource_onlyFails : staleSource.OnlyFails .ageBound := by
  refine ⟨staleSource_not_ageWithinBound, ?_⟩
  intro coordinate hcoordinate
  cases coordinate with
  | causalAvailability => exact staleSource_causal
  | ageBound => exact (hcoordinate rfl).elim

theorem every_coordinate_has_only_one_failure_model
    (coordinate : TemporalStandingCoordinate) :
    ∃ S : RawTemporalStanding, S.OnlyFails coordinate := by
  cases coordinate with
  | causalAvailability => exact ⟨futureSource, futureSource_onlyFails⟩
  | ageBound => exact ⟨staleSource, staleSource_onlyFails⟩

end Toy

/-- Advance the observation clock without changing source issuance or age
policy. -/
def advance (S : RawTemporalStanding) (elapsed : Nat) :
    RawTemporalStanding where
  sourcedAt := S.sourcedAt
  observedAt := S.observedAt + elapsed
  maxAge := S.maxAge

/-- A temporal move is defined only when both endpoints retain freshness
standing.  Expiration therefore stops identity-preserving transport. -/
def advanceWhileFresh
    (elapsed : Nat) (S : RawTemporalStanding) :
    Option RawTemporalStanding :=
  let result := S.advance elapsed
  if S.StandingFresh ∧ result.StandingFresh then some result else none

/-- Operations-only temporal presentation graph. -/
def standingOperations :
    NativeStandingOperations RawTemporalStanding Nat where
  apply := advanceWhileFresh

/-- The source issuance and age policy identify the temporal claim across
successful observation-time advances. -/
def claimAnchor (S : RawTemporalStanding) : Nat × Nat :=
  (S.sourcedAt, S.maxAge)

def anchoredStandingOperations :
    AnchoredStandingOperations RawTemporalStanding Nat (Nat × Nat) where
  toNativeStandingOperations := standingOperations
  anchor := claimAnchor
  anchor_preserved := by
    intro elapsed source result happlies
    simp only [standingOperations, advanceWhileFresh] at happlies
    split at happlies
    · simp only [Option.some.injEq] at happlies
      subst result
      rfl
    · simp at happlies

theorem nativeMoveInvariant_standingFresh :
    NativeMoveInvariant standingOperations StandingFresh := by
  intro elapsed source result happlies
  simp only [standingOperations, advanceWhileFresh] at happlies
  split at happlies
  · rename_i hfresh
    simp only [Option.some.injEq] at happlies
    subst result
    exact iff_of_true hfresh.1 hfresh.2
  · simp at happlies

/-- Freshness is genuinely standing-relevant for the native temporal graph. -/
theorem standingInvariant_standingFresh :
    StandingInvariant (generatedStandingIdentity standingOperations)
      StandingFresh :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    standingOperations StandingFresh).mpr nativeMoveInvariant_standingFresh

/-! ## One audit atom covering two native domain coordinates -/

/-- The selected temporal standing contract contains exactly predicates
extensionally equal to computed freshness.  It does not admit arbitrary
temporal-domain predicates merely because they are invariant. -/
def freshnessRelevance :
    StandingRelevance (generatedStandingIdentity standingOperations) where
  relevant := fun target => ∀ state, target state ↔ state.StandingFresh
  invariant := by
    intro target htarget source result hstanding
    calc
      target source ↔ source.StandingFresh := htarget source
      _ ↔ result.StandingFresh :=
        standingInvariant_standingFresh hstanding
      _ ↔ target result := (htarget result).symm

/-- A one-atom audit vocabulary for the selected freshness contract. -/
def freshnessAuditSemantics :
    ObligationSemantics RawTemporalStanding Unit where
  holds := fun _ => StandingFresh

theorem freshnessAudit_atomCoverage :
    AtomCoverageCertificate freshnessAuditSemantics
      freshnessRelevance.relevant where
  invariant := by
    intro target htarget source result hatoms
    have hfresh : source.StandingFresh ↔ result.StandingFresh :=
      hatoms ()
    calc
      target source ↔ source.StandingFresh := htarget source
      _ ↔ result.StandingFresh := hfresh
      _ ↔ target result := (htarget result).symm

/-- The one freshness atom is complete for the selected standing-relevance
family even though the raw freshness law has two independent coordinates. -/
theorem freshnessAudit_complete_for_relevance :
    FiniteFacetCompleteFor freshnessAuditSemantics
      freshnessRelevance.relevant := by
  classical
  exact
    (finiteFacetCompleteFor_standingRelevance_iff_atomCoverage
      (generatedStandingIdentity standingOperations)
      freshnessRelevance freshnessAuditSemantics).mpr
        freshnessAudit_atomCoverage

theorem temporalStandingCoordinate_cardinality :
    Fintype.card TemporalStandingCoordinate = 2 := by
  decide

theorem temporalStandingCoordinates_not_equivalent_to_freshnessAtom :
    ¬ Nonempty (TemporalStandingCoordinate ≃ Unit) := by
  rintro ⟨equiv⟩
  have hcard := Fintype.card_congr equiv
  norm_num [temporalStandingCoordinate_cardinality] at hcard

end RawTemporalStanding
end PhysicsCore
end SaturationMonoid
