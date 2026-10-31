import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Fold.Source.SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold

/-!
# Proof-carrying accepted-legislation finite-fold universal property

Every finite presentation with the exact base and literal generated successor
is the existing physical `cycleAt` fold.  Independently presented audits agree
on overlaps, concatenation preserves the enacted readouts, and every prefix's
one compatible extension is already accepted, enacted and extendable.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
open M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep
open M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
open M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold

/-- The final node of every compatible `(fuel + 1)` presentation is the one
literal physical extension.  The same node carries acceptance, enactment and
another actual step. -/
structure CanonicalSocietyAcceptedLegislationUniqueExtensionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  literalGeneratedFinalNext :
    generatedFinalNextCycleAt initial fuel =
      generatedNextCycleAt (cycleAt initial fuel)
  everyCompatibleFinalNodeUnique :
    ∀ (candidate :
        FiniteEnactmentCycleCandidateAt initial (fuel + 1))
      (_base : HEq (candidate ⟨0, by omega⟩) initial)
      (_step : ∀ edge : Fin (fuel + 1),
        HEq (candidate (edgeTargetNode edge))
          (generatedNextCycleAt
            (candidate (edgeSourceNode edge)))),
      HEq (candidate ⟨fuel + 1, by omega⟩)
        (generatedFinalNextCycleAt initial fuel)
  generatedFinalNextAcceptance :
    Nonempty
      (SourceAcceptedExternalPaymentLegislationAt
        (generatedFinalNextCycleAt initial fuel).1
        (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + (fuel + 1)))
        (targetLegislation (generatedFinalNextCycleAt initial fuel).1))
  generatedFinalNextEnactment :
    CycleAcceptedLegislationEffectFactsAt initial (fuel + 1)
  generatedFinalNextStillExtends :
    CycleAcceptedLegislationStepFactsAt initial (fuel + 1)

theorem canonicalSocietyAcceptedLegislationUniqueExtension
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    CanonicalSocietyAcceptedLegislationUniqueExtensionAt initial fuel := by
  let cascade :=
    proofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
      initial fuel
  refine
    { literalGeneratedFinalNext := rfl
      everyCompatibleFinalNodeUnique := ?_
      generatedFinalNextAcceptance := cascade.finalGeneratedNextAcceptance
      generatedFinalNextEnactment := cascade.finalGeneratedNextEffect
      generatedFinalNextStillExtends :=
        cascade.finalGeneratedNextStillExtends }
  intro candidate base step
  have finalExact :=
    cycleAt_uniqueFiniteFold initial (fuel + 1) candidate base step
      ⟨fuel + 1, by omega⟩
  exact HEq.trans finalExact
    (heq_of_eq
      (generatedFinalNextCycle_eq_cycleAt_succ initial fuel).symm)

/-- A finite enactment presentation cannot obey the physical base and every
literal successor edge while ending at a different law cycle. -/
theorem compatibleAlternativeFinalNode_isFalse
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (candidate :
      FiniteEnactmentCycleCandidateAt initial (fuel + 1))
    (base : HEq (candidate ⟨0, by omega⟩) initial)
    (step : ∀ edge : Fin (fuel + 1),
      HEq (candidate (edgeTargetNode edge))
        (generatedNextCycleAt
          (candidate (edgeSourceNode edge))))
    (differentFinal :
      ¬ HEq (candidate ⟨fuel + 1, by omega⟩)
        (generatedFinalNextCycleAt initial fuel)) : False :=
  differentFinal
    ((canonicalSocietyAcceptedLegislationUniqueExtension initial fuel
      ).everyCompatibleFinalNodeUnique candidate base step)

/-- Maximum finite-fold consumer.  It rules out an alternative finite law
path without constructing a completed future or storing candidate authority. -/
structure CanonicalSocietyAcceptedLegislationFiniteFoldUniversalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) : Prop where
  priorPhysicalNoFiniteTerminal :
    CanonicalSocietyAcceptedLegislationNoFiniteTerminalAt initial
  zeroCoherence : cycleAt initial 0 = initial
  successorCoherence : ∀ depth,
    cycleAt initial (depth + 1) = (stepAt initial depth).nextCycle
  everyFiniteCandidateUnique :
    ∀ (fuel : Nat)
      (candidate : FiniteEnactmentCycleCandidateAt initial fuel)
      (_base : HEq (candidate ⟨0, by omega⟩) initial)
      (_step : ∀ edge : Fin fuel,
        HEq (candidate (edgeTargetNode edge))
          (generatedNextCycleAt
            (candidate (edgeSourceNode edge))))
      (node : Fin (fuel + 1)),
      HEq (candidate node) (cycleAt initial node.1)
  finiteRestrictionsCompatible :
    ∀ (leftFuel rightFuel : Nat)
      (leftCandidate :
        FiniteEnactmentCycleCandidateAt initial leftFuel)
      (rightCandidate :
        FiniteEnactmentCycleCandidateAt initial rightFuel)
      (_leftBase : HEq (leftCandidate ⟨0, by omega⟩) initial)
      (_rightBase : HEq (rightCandidate ⟨0, by omega⟩) initial)
      (_leftStep : ∀ edge : Fin leftFuel,
        HEq (leftCandidate (edgeTargetNode edge))
          (generatedNextCycleAt
            (leftCandidate (edgeSourceNode edge))))
      (_rightStep : ∀ edge : Fin rightFuel,
        HEq (rightCandidate (edgeTargetNode edge))
          (generatedNextCycleAt
            (rightCandidate (edgeSourceNode edge))))
      (leftNode : Fin (leftFuel + 1))
      (rightNode : Fin (rightFuel + 1))
      (_sameDepth : leftNode.1 = rightNode.1),
      HEq (leftCandidate leftNode) (rightCandidate rightNode)
  enactedConcatenationCoherence : ∀ firstDepth secondDepth,
    type_of% (enactedLaw_concat initial firstDepth secondDepth)
  everyPrefixUniqueEnactedExtension : ∀ fuel,
    CanonicalSocietyAcceptedLegislationUniqueExtensionAt initial fuel

theorem canonicalSocietyAcceptedLegislationFiniteFoldUniversal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    CanonicalSocietyAcceptedLegislationFiniteFoldUniversalAt initial where
  priorPhysicalNoFiniteTerminal :=
    canonicalSocietyAcceptedLegislationNoFiniteTerminal initial
  zeroCoherence := cycleAt_zero initial
  successorCoherence := fun depth => cycleAt_succ initial depth
  everyFiniteCandidateUnique := fun fuel candidate base step node =>
    cycleAt_uniqueFiniteFold initial fuel candidate base step node
  finiteRestrictionsCompatible :=
    fun leftFuel rightFuel leftCandidate rightCandidate leftBase rightBase
      leftStep rightStep leftNode rightNode sameDepth =>
        finiteEnactmentCandidates_agreeOnCommonDepth initial
          leftFuel rightFuel leftCandidate rightCandidate leftBase rightBase
          leftStep rightStep leftNode rightNode sameDepth
  enactedConcatenationCoherence := fun firstDepth secondDepth =>
    enactedLaw_concat initial firstDepth secondDepth
  everyPrefixUniqueEnactedExtension := fun fuel =>
    canonicalSocietyAcceptedLegislationUniqueExtension initial fuel

end
end M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal.canonicalSocietyAcceptedLegislationUniqueExtension
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal.compatibleAlternativeFinalNode_isFalse
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal.canonicalSocietyAcceptedLegislationFiniteFoldUniversal
