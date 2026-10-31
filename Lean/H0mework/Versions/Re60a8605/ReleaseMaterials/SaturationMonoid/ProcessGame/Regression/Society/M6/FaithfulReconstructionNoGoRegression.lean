import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.NormalizedAuthorityObserverFixture

/-!
# M6 Society faithful-reconstruction no-go

The generic observer interface is instantiated by the existing M5 source-path
fibre.  This consumer keeps the positive surrogate right section and rejects
both visible authority factorization and faithful actual-occurrence recovery.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M6FaithfulReconstructionNoGoRegression

noncomputable section

open Classical.GeneratedTerminalExchange
open M5SourceFirstCrossOccurrenceFixture
open M5SourceFirstCrossOccurrenceResidual
open M6NormalizedAuthorityObserverFixture
open Observer

def societyObserver :
    AuthorityObserver ActualPath NormalizedImage ℚ where
  forget := normalizedForget
  authorityK := pathAuthorityK

def societyKernelPair : AuthorityKernelPair societyObserver where
  left := leftPath
  right := rightPath
  occurrence_ne := leftPath_ne_rightPath
  visible_eq := normalizedForget_paths_equal
  authority_ne := pathAuthorityK_ne

def societySurrogateRightSection :
    SurrogateRightSection societyObserver where
  lift := leftSurrogateSection
  lift_forget := leftSurrogateSection_rightInverse

theorem society_no_authority_factorization :
    ¬ Nonempty (AuthorityFactorization societyObserver) :=
  societyKernelPair.noAuthorityFactorization

theorem society_no_occurrence_left_inverse :
    ¬ ∃ reconstruct : NormalizedImage → ActualPath,
      Function.LeftInverse reconstruct societyObserver.forget :=
  societyKernelPair.noOccurrenceLeftInverse

theorem society_no_faithful_authority_reconstruction :
    ¬ Nonempty (FaithfulAuthorityReconstruction societyObserver) :=
  societyKernelPair.noFaithfulAuthorityReconstruction

/-- Direct Society consumer: object-level normalization remains surjective,
while the exact M5 authority pair rules out every visible-only authority
factorization and every faithful occurrence reconstruction. -/
structure SocietyFaithfulReconstructionNoGoCertificate : Prop where
  leftConsumer : TerminalAuthorityConsumerAt leftProgram leftTerminal
  rightConsumer : TerminalAuthorityConsumerAt rightProgram rightTerminal
  leftOccurrenceExact :
    actualOccurrence leftPath = leftProgram.occurrence
  rightOccurrenceExact :
    actualOccurrence rightPath = rightProgram.occurrence
  occurrencesDifferent :
    actualOccurrence leftPath ≠ actualOccurrence rightPath
  authorityDifferent :
    societyObserver.authorityK leftPath ≠
      societyObserver.authorityK rightPath
  sameNormalizedImage :
    societyObserver.forget leftPath = societyObserver.forget rightPath
  surrogateExists : Nonempty (SurrogateRightSection societyObserver)
  noAuthorityFactorization :
    ¬ Nonempty (AuthorityFactorization societyObserver)
  noOccurrenceLeftInverse :
    ¬ ∃ reconstruct : NormalizedImage → ActualPath,
      Function.LeftInverse reconstruct societyObserver.forget
  noFaithfulReconstruction :
    ¬ Nonempty (FaithfulAuthorityReconstruction societyObserver)

theorem societyFaithfulReconstructionNoGoDirectConsumer :
    SocietyFaithfulReconstructionNoGoCertificate where
  leftConsumer := left_exact_authority_consumer
  rightConsumer := right_exact_authority_consumer
  leftOccurrenceExact := left_actualOccurrence
  rightOccurrenceExact := right_actualOccurrence
  occurrencesDifferent := actualOccurrences_ne
  authorityDifferent := pathAuthorityK_ne
  sameNormalizedImage := normalizedForget_paths_equal
  surrogateExists := ⟨societySurrogateRightSection⟩
  noAuthorityFactorization := society_no_authority_factorization
  noOccurrenceLeftInverse := society_no_occurrence_left_inverse
  noFaithfulReconstruction := society_no_faithful_authority_reconstruction

end
end M6FaithfulReconstructionNoGoRegression
end Society
end ProcessGame
end SaturationMonoid
