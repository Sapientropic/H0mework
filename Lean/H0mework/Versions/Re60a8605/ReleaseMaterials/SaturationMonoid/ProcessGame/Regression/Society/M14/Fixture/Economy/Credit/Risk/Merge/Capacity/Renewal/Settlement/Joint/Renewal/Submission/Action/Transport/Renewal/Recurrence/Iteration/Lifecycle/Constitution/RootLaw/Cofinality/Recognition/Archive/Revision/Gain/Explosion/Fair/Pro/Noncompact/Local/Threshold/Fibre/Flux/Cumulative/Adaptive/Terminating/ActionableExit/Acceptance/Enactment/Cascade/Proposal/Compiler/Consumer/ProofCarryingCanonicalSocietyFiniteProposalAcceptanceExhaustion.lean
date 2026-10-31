import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Proposal.Compiler.Source.SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler

/-!
# Proof-carrying finite proposal acceptance exhaustion

The source compiler's all-accepted branch is connected to the unique physical
enactment fold.  Its first-refusal branch retains all earlier enactments and
proves that refusal of an external proposal cannot stop or rewrite the
canonical law at the same physical node.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Legislation
open M14UBIPeriodicRootHistory
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
open M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal
open M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler

/-- An enactment attempt indexed by the refused external acceptance.  It is
empty whenever that acceptance fibre is empty, even though the canonical
source consumer at the same node remains real. -/
abbrev FiniteProposalAcceptedConsumerAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) :=
  Σ _acceptance : FiniteProposalAcceptedAt initial program node,
    ProofCarryingLegislationConsumerAt
      (targetLegislation (cycleLegislationSpanAt initial node.1))

structure EveryAcceptedFiniteProposalEnactmentAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel) : Prop where
  priorFiniteFoldUniversal :
    CanonicalSocietyAcceptedLegislationFiniteFoldUniversalAt initial
  everyProgramAcceptance :
    EveryFiniteProposalAcceptedAt initial program
  everyProgramProposalExact : ∀ node,
    program node =
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + node.1)
  physicalCascade :
    ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascadeAt
      initial fuel
  everyNodeEnacted : ∀ node : Fin (fuel + 1),
    CycleAcceptedLegislationEffectFactsAt initial node.1
  everyEdgeGeneratesActualNext : ∀ edge : Fin fuel,
    CycleAcceptedLegislationStepFactsAt initial edge.1
  finalUniqueAcceptedEnactedExtension :
    CanonicalSocietyAcceptedLegislationUniqueExtensionAt initial fuel

theorem everyAcceptedFiniteProposal_enactsUniquePhysicalFold
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (every : EveryFiniteProposalAcceptedAt initial program) :
    EveryAcceptedFiniteProposalEnactmentAt initial program := by
  let universal :=
    canonicalSocietyAcceptedLegislationFiniteFoldUniversal initial
  let cascade :=
    proofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
      initial fuel
  exact
    { priorFiniteFoldUniversal := universal
      everyProgramAcceptance := every
      everyProgramProposalExact := fun node =>
        (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
          node).mp (every node)
      physicalCascade := cascade
      everyNodeEnacted := cascade.everyNodeEffect
      everyEdgeGeneratesActualNext :=
        cascade.everyEdgeActualEnactmentRecurrence
      finalUniqueAcceptedEnactedExtension :=
        universal.everyPrefixUniqueEnactedExtension fuel }

structure FirstRefusedFiniteProposalContinuationAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) : Prop where
  priorFiniteFoldUniversal :
    CanonicalSocietyAcceptedLegislationFiniteFoldUniversalAt initial
  firstRefusal :
    FirstSourceAcceptanceRefusalAt initial program node
  earlierProgramProposalExact : ∀ earlier : Fin (fuel + 1),
    earlier.1 < node.1 →
      program earlier =
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + earlier.1)
  earlierPhysicalEnactments : ∀ earlier : Fin (fuel + 1),
    earlier.1 < node.1 →
      CycleAcceptedLegislationEffectFactsAt initial earlier.1
  refusedProgramAcceptanceEmpty :
    IsEmpty (FiniteProposalAcceptedAt initial program node)
  refusedProgramAcceptedConsumerEmpty :
    IsEmpty (FiniteProposalAcceptedConsumerAt initial program node)
  refusedProposalDifferent :
    program node ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + node.1)
  canonicalProposalStillAccepted :
    Nonempty
      (SourceAcceptedExternalPaymentLegislationAt
        (cycleLegislationSpanAt initial node.1)
        (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + node.1))
        (targetLegislation (cycleLegislationSpanAt initial node.1)))
  canonicalConsumerStillExact :
    type_of%
      (cyclePointwiseAcceptanceAt initial node.1
        ).independentConsumer_heq_targetConsumer
  canonicalLawStillEnacted :
    CycleAcceptedLegislationEffectFactsAt initial node.1
  canonicalLawStillGeneratesActualNext :
    CycleAcceptedLegislationStepFactsAt initial node.1

theorem firstRefusedFiniteProposal_preservesSourceEnactment
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1))
    (refusal : FirstSourceAcceptanceRefusalAt initial program node) :
    FirstRefusedFiniteProposalContinuationAt initial program node := by
  let universal :=
    canonicalSocietyAcceptedLegislationFiniteFoldUniversal initial
  exact
    { priorFiniteFoldUniversal := universal
      firstRefusal := refusal
      earlierProgramProposalExact := fun earlier earlierLt =>
        (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
          earlier).mp (refusal.earlierAccepted earlier earlierLt)
      earlierPhysicalEnactments := fun earlier _ =>
        cycleAcceptedLegislationEffect initial earlier.1
      refusedProgramAcceptanceEmpty := refusal.refused
      refusedProgramAcceptedConsumerEmpty :=
        ⟨fun attempted => refusal.refused.false attempted.1⟩
      refusedProposalDifferent := refusal.proposal_ne_source
      canonicalProposalStillAccepted :=
        ⟨cyclePointwiseAcceptanceAt initial node.1⟩
      canonicalConsumerStillExact :=
        (cyclePointwiseAcceptanceAt initial node.1
          ).independentConsumer_heq_targetConsumer
      canonicalLawStillEnacted :=
        cycleAcceptedLegislationEffect initial node.1
      canonicalLawStillGeneratesActualNext :=
        cycleAcceptedLegislationStep initial node.1 }

/-- Concrete negative control: one externally mismatched proposal is refused
at its requested first node, while the physical canonical enactment there
continues unchanged. -/
theorem oneNodeExternalProposalRefusal_preservesCanonicalEnactment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (refusalNode : Fin (fuel + 1))
    (alternative : AnySourceBackedPaymentOccurrence)
    (different : alternative ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + refusalNode.1)) :
    FirstRefusedFiniteProposalContinuationAt initial
      (finiteProposalProgramRefusingAt initial fuel refusalNode alternative)
      refusalNode :=
  firstRefusedFiniteProposal_preservesSourceEnactment initial
    (finiteProposalProgramRefusingAt initial fuel refusalNode alternative)
    refusalNode
    (finiteProposalProgramRefusingAt_first initial fuel refusalNode
      alternative different)

/-- Premise-free adjacent-Payment counterexample.  The external program is
refused at zero, while the zero-node canonical law remains enacted and
continues to its literal successor. -/
theorem adjacentActualPaymentProposalRefusal_preservesCanonicalEnactment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    FirstRefusedFiniteProposalContinuationAt initial
      (adjacentMismatchFiniteProposalProgramAt initial fuel)
      ⟨0, by omega⟩ :=
  firstRefusedFiniteProposal_preservesSourceEnactment initial
    (adjacentMismatchFiniteProposalProgramAt initial fuel) ⟨0, by omega⟩
    (adjacentMismatchFiniteProposalProgram_firstRefusal initial fuel)

abbrev FiniteProposalAcceptanceEnactmentResultAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel) :=
  Sum (PLift (EveryAcceptedFiniteProposalEnactmentAt initial program))
    (Σ node, PLift
      (FirstRefusedFiniteProposalContinuationAt initial program node))

/-- Exhaustive direct consumer of the source compiler. -/
def compileFiniteProposalAcceptanceEnactment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (program : FiniteProposalProgramAt initial fuel) :
    FiniteProposalAcceptanceEnactmentResultAt initial program :=
  match compileFiniteProposalProgram initial fuel program with
  | .inl every =>
      .inl ⟨everyAcceptedFiniteProposal_enactsUniquePhysicalFold initial
        program every.down⟩
  | .inr refusal =>
      .inr ⟨refusal.1,
        ⟨firstRefusedFiniteProposal_preservesSourceEnactment initial program
          refusal.1 refusal.2.down⟩⟩

theorem everyAcceptedEnactment_and_firstRefusalContinuation_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel} :
    IsEmpty
      (PLift (EveryAcceptedFiniteProposalEnactmentAt initial program) ×
        (Σ node, PLift
          (FirstRefusedFiniteProposalContinuationAt initial program node))) :=
  ⟨fun both =>
    everyAccepted_and_firstRefusal_isEmpty.false
      ⟨⟨both.1.down.everyProgramAcceptance⟩,
        ⟨both.2.1, ⟨both.2.2.down.firstRefusal⟩⟩⟩⟩

/-- Maximum finite external-proposal exhaustion.  Results are generated per
request; no sequence of programs or future verdicts is stored. -/
structure CanonicalSocietyFiniteProposalAcceptanceExhaustionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) : Prop where
  priorFiniteFoldUniversal :
    CanonicalSocietyAcceptedLegislationFiniteFoldUniversalAt initial
  everyFiniteProposalProgram : ∀ fuel
      (program : FiniteProposalProgramAt initial fuel),
    Nonempty (FiniteProposalAcceptanceEnactmentResultAt initial program)

theorem canonicalSocietyFiniteProposalAcceptanceExhaustion
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    CanonicalSocietyFiniteProposalAcceptanceExhaustionAt initial where
  priorFiniteFoldUniversal :=
    canonicalSocietyAcceptedLegislationFiniteFoldUniversal initial
  everyFiniteProposalProgram := fun fuel program =>
    ⟨compileFiniteProposalAcceptanceEnactment initial fuel program⟩

end
end M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.everyAcceptedFiniteProposal_enactsUniquePhysicalFold
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.firstRefusedFiniteProposal_preservesSourceEnactment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.oneNodeExternalProposalRefusal_preservesCanonicalEnactment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.adjacentActualPaymentProposalRefusal_preservesCanonicalEnactment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.compileFiniteProposalAcceptanceEnactment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.everyAcceptedEnactment_and_firstRefusalContinuation_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion.canonicalSocietyFiniteProposalAcceptanceExhaustion
