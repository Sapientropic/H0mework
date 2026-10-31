import H0mework.Cognition.Selfhood.Narrative
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.NaturalReconstructionNoGoRegression

/-!
# M7 trace-constrained narrative fixture

The narrative carrier is only a normalized classical image paired with a list
of proposed source atoms.  Admissibility is checked against the existing M5
occurrence trace.  No archive, occurrence, or witness registry is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7TraceConstrainedNarrativeFixture

noncomputable section

open Classical.Source Classical.Source.FreeStrategicSyntax
open M5SourceFirstCrossOccurrenceFixture
open M5SourceFirstCrossOccurrenceResidual
open M6NormalizedAuthorityObserverFixture
open History

/-- A proposed narrative consists only of its visible normal form and source
claims.  Trace authority remains outside the narrative. -/
abbrev Narrative := NormalizedImage × List FreeClassicalAtom

def commonNarrative : Narrative :=
  (commonImage, [.origin])

def pathTrace (path : ActualPath) : List FreeClassicalAtom :=
  (actualOccurrence path).trace

def pathNarrative (_path : ActualPath) : Narrative :=
  commonNarrative

def narrativeClaims (story : Narrative) : List FreeClassicalAtom :=
  story.2

def narrativeReadout :
    TraceConstrainedNarrativeReadout
      ActualPath Narrative FreeClassicalAtom where
  trace := pathTrace
  narrative := pathNarrative
  claims := narrativeClaims
  emitted_claim_supported := by
    intro path atom claimed
    have atomEq : atom = FreeClassicalAtom.origin := by
      simpa [pathNarrative, commonNarrative, narrativeClaims] using claimed
    subst atom
    cases path with
    | left =>
        exact leftProgram.origin_mem_trace
    | right =>
        exact rightProgram.origin_mem_trace

theorem commonNarrative_has_witnessed_origin_claim :
    FreeClassicalAtom.origin ∈ narrativeReadout.claims commonNarrative := by
  simp [narrativeReadout, narrativeClaims, commonNarrative]

theorem same_classical_narrative :
    narrativeReadout.narrative leftPath =
      narrativeReadout.narrative rightPath :=
  rfl

theorem common_narrative_fibre_not_subsingleton :
    ¬ Subsingleton
      (narrativeReadout.NarrativeFibreAt
        (narrativeReadout.narrative leftPath)) :=
  narrativeReadout.narrativeFibre_not_subsingleton
    leftPath rightPath leftPath_ne_rightPath same_classical_narrative

theorem every_common_fibre_member_is_trace_constrained
    (member : narrativeReadout.NarrativeFibreAt commonNarrative) :
    narrativeReadout.SupportsAt member.1 commonNarrative :=
  narrativeReadout.fibre_member_supports member

/-- This proposed story adds the exact authority atom emitted only by the
left source occurrence. -/
def leftAuthorityNarrative : Narrative :=
  (commonImage, [leftAuthorityAtom])

theorem leftAuthorityNarrative_supported_left :
    narrativeReadout.SupportsAt leftPath leftAuthorityNarrative := by
  intro atom claimed
  have atomEq : atom = leftAuthorityAtom := by
    simpa [narrativeReadout, narrativeClaims, leftAuthorityNarrative] using
      claimed
  subst atom
  simpa [narrativeReadout, pathTrace, actualOccurrence, leftPath] using
    leftAuthorityAtom_mem_trace

theorem leftAuthorityNarrative_not_supported_right :
    ¬ narrativeReadout.SupportsAt rightPath leftAuthorityNarrative := by
  apply narrativeReadout.not_supports_of_claim_absent
    rightPath leftAuthorityNarrative leftAuthorityAtom
  · simp [narrativeReadout, narrativeClaims, leftAuthorityNarrative]
  · simpa [narrativeReadout, pathTrace, actualOccurrence, rightPath] using
      leftAuthorityAtom_not_mem_right_trace

end
end M7TraceConstrainedNarrativeFixture
end Society
end ProcessGame
end SaturationMonoid
