import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.Matching.VisibleBalanceFixture

/-!
# M7 matching identification boundary

Visible matching succeeds at the common normalized image.  Treating the same
visible computation as complete authority or actual source-path
identification is rejected by the existing M6 source-generated attachment
boundary.  No credit lineage or identification oracle is added.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7MatchingAuthorityIdentificationRegression

noncomputable section

open Classical.GeneratedTerminalExchange
open M5SourceFirstCrossOccurrenceFixture
open M5SourceFirstCrossOccurrenceResidual
open M6NormalizedAuthorityObserverFixture
open M6FaithfulReconstructionNoGoRegression
open M6NaturalReconstructionNoGoRegression
open M7VisibleBalanceFixture
open Matching Observer

abbrev MatchingOutput := Option ℚ × Option ℚ

def visibleMatchingOutput (visible : NormalizedImage) : MatchingOutput :=
  (visibleMatchingBalance.leftBalance visible,
    visibleMatchingBalance.rightBalance visible)

/-- The positive matching computation is induced directly from the visible
image and therefore factors definitionally through the observer. -/
def matchingReadout : OccurrenceReadout ActualPath MatchingOutput :=
  OccurrenceReadout.ofVisible societyObserver visibleMatchingOutput

def matchingFactorization :
    ReadoutFactorization societyObserver matchingReadout :=
  ReadoutFactorization.ofVisible societyObserver visibleMatchingOutput

theorem matching_visible_factorization_positive :
    Nonempty (ReadoutFactorization societyObserver matchingReadout) :=
  ReadoutFactorization.visibleComputation_nonempty
    societyObserver visibleMatchingOutput

theorem matching_output_exact :
    matchingReadout.read leftPath = (some 7, some 7) ∧
      matchingReadout.read rightPath = (some 7, some 7) := by
  have exactPair : visibleMatchingOutput commonImage = (some 7, some 7) := by
    apply Prod.ext
    · exact matched_value_is_nonzero_terminal_value.1
    · exact matched_value_is_nonzero_terminal_value.2
  exact ⟨exactPair, exactPair⟩

theorem matching_output_same_on_authority_fibre :
    matchingReadout.read leftPath = matchingReadout.read rightPath :=
  rfl

/-- The exact M6 attachment boundary rejects every decoder that advertises
the visible matching output as complete source authority. -/
theorem matching_no_complete_authority_identification :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt societyObserver matchingReadout) :=
  societySourceGeneratedAttachingDirection
    |>.boundary_noAuthorityCompleteReadout matchingFactorization

/-- The ordinary left surrogate remains a visible readout, but cannot identify
both actual source paths.  This is the lineage/occurrence completeness half of
the matching no-go. -/
def visibleSurrogatePathReadout :
    OccurrenceReadout ActualPath ActualPath :=
  OccurrenceReadout.ofVisible societyObserver leftSurrogateSection

def visibleSurrogatePathFactorization :
    ReadoutFactorization societyObserver visibleSurrogatePathReadout :=
  ReadoutFactorization.ofVisible societyObserver leftSurrogateSection

theorem matching_no_complete_actual_path_identification :
    ¬ Nonempty
      (ActualOccurrenceCompleteReadoutAt visibleSurrogatePathReadout) := by
  rintro ⟨complete⟩
  exact societySourceGeneratedAttachingDirection
    |>.boundary_rejectsActualCompleteReadout
      visibleSurrogatePathFactorization societySurrogateRightSection complete

structure MatchingAuthorityIdentificationCertificate : Prop where
  leftExactConsumer : TerminalAuthorityConsumerAt leftProgram leftTerminal
  rightExactConsumer : TerminalAuthorityConsumerAt rightProgram rightTerminal
  positiveVisibleBalance : Nonempty visibleMatchingBalance.BalancedImage
  positiveVisibleFactorization :
    Nonempty (ReadoutFactorization societyObserver matchingReadout)
  exactMatchedValue :
    matchingReadout.read leftPath = (some 7, some 7) ∧
      matchingReadout.read rightPath = (some 7, some 7)
  sameVisibleOutput :
    matchingReadout.read leftPath = matchingReadout.read rightPath
  actualPathsDifferent : leftPath ≠ rightPath
  authorityDifferent :
    societyObserver.authorityK leftPath ≠
      societyObserver.authorityK rightPath
  attachmentBoundaryExact :
    societySourceGeneratedAttachingDirection.boundaryKernelPair =
      societyRootedObserverObstruction.kernelPair
  noCompleteAuthorityIdentification :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt societyObserver matchingReadout)
  noCompleteActualPathIdentification :
    ¬ Nonempty
      (ActualOccurrenceCompleteReadoutAt visibleSurrogatePathReadout)

theorem matchingAuthorityIdentificationDirectConsumer :
    MatchingAuthorityIdentificationCertificate where
  leftExactConsumer := left_exact_authority_consumer
  rightExactConsumer := right_exact_authority_consumer
  positiveVisibleBalance := positive_visible_balance
  positiveVisibleFactorization := matching_visible_factorization_positive
  exactMatchedValue := matching_output_exact
  sameVisibleOutput := matching_output_same_on_authority_fibre
  actualPathsDifferent := leftPath_ne_rightPath
  authorityDifferent := pathAuthorityK_ne
  attachmentBoundaryExact := society_attaching_boundary_exact
  noCompleteAuthorityIdentification :=
    matching_no_complete_authority_identification
  noCompleteActualPathIdentification :=
    matching_no_complete_actual_path_identification

end
end M7MatchingAuthorityIdentificationRegression
end Society
end ProcessGame
end SaturationMonoid
