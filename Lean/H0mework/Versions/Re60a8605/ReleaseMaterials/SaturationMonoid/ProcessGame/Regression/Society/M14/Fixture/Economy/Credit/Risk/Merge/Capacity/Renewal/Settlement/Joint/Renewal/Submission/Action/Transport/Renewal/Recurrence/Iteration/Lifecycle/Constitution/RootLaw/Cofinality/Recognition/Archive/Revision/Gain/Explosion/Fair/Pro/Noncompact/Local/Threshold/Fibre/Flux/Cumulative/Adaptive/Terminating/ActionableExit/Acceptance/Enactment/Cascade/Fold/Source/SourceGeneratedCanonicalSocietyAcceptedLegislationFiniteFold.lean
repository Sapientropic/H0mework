import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Consumer.ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade

/-!
# Source-generated accepted-legislation finite fold

The existing physical `cycleAt` is characterized by its exact base and literal
generated-successor law on every finite candidate.  Prefix/suffix execution
commutes for cycles and enacted-law readouts without constructing an omega
path.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold

noncomputable section

universe u v

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade

/-- The candidate is only a theorem parameter over a finite node set.  It is
not stored authority or a future registry. -/
abbrev FiniteEnactmentCycleCandidateAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :=
  (node : Fin (fuel + 1)) →
    CycleAt oldVisit sourceIndex (boundary + node.1)

def edgeSourceNode {fuel : Nat} (edge : Fin fuel) : Fin (fuel + 1) :=
  ⟨edge.1, by omega⟩

def edgeTargetNode {fuel : Nat} (edge : Fin fuel) : Fin (fuel + 1) :=
  ⟨edge.1 + 1, by omega⟩

private abbrev PackedCycleAt (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Σ boundary, CycleAt oldVisit sourceIndex boundary

private def packCycleAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    PackedCycleAt oldVisit sourceIndex :=
  ⟨boundary, cycle⟩

private def packedGeneratedNextCycleAt
    {oldVisit : OldVisit} {sourceIndex : Nat} :
    PackedCycleAt oldVisit sourceIndex → PackedCycleAt oldVisit sourceIndex
  | ⟨boundary, cycle⟩ =>
      ⟨boundary + 1, generatedNextCycleAt cycle⟩

private theorem dependentCongrArgHEq
    {α : Sort u} {motive : α → Sort v}
    (f : (a : α) → motive a) {left right : α}
    (exact : left = right) : HEq (f left) (f right) := by
  cases exact
  exact HEq.rfl

/-- Any finite candidate with the exact base and literal generated-successor
law is the physical source fold at every node. -/
theorem cycleAt_uniqueFiniteFold
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (candidate : FiniteEnactmentCycleCandidateAt initial fuel)
    (base : HEq (candidate ⟨0, by omega⟩) initial)
    (step : ∀ edge : Fin fuel,
      HEq (candidate (edgeTargetNode edge))
        (generatedNextCycleAt (candidate (edgeSourceNode edge)))) :
    ∀ node : Fin (fuel + 1),
      HEq (candidate node) (cycleAt initial node.1) := by
  intro node
  have nodewise : ∀ depth (bound : depth < fuel + 1),
      HEq (candidate ⟨depth, bound⟩) (cycleAt initial depth) := by
    intro depth
    induction depth with
    | zero =>
        intro bound
        have nodeEq : (⟨0, bound⟩ : Fin (fuel + 1)) = ⟨0, by omega⟩ :=
          Fin.ext rfl
        rw [nodeEq]
        simpa only [cycleAt_zero] using base
    | succ depth inductionHypothesis =>
        intro bound
        let edge : Fin fuel := ⟨depth, by omega⟩
        have sourceExact :
            HEq (candidate (edgeSourceNode edge))
              (cycleAt initial depth) := by
          simpa only [edgeSourceNode, edge] using
            inductionHypothesis (by omega)
        have sourceEquality :
            candidate (edgeSourceNode edge) = cycleAt initial depth := by
          exact eq_of_heq sourceExact
        have generatedEquality :
            generatedNextCycleAt (candidate (edgeSourceNode edge)) =
              generatedNextCycleAt (cycleAt initial depth) :=
          congrArg generatedNextCycleAt sourceEquality
        have stepExact :
            HEq (candidate ⟨depth + 1, bound⟩)
              (generatedNextCycleAt (candidate (edgeSourceNode edge))) := by
          simpa only [edgeTargetNode, edge] using step edge
        exact HEq.trans stepExact
          (HEq.trans (heq_of_eq generatedEquality)
            (heq_of_eq (cycleAt_succ initial depth).symm))
  exact nodewise node.1 node.2

/-- Independently presented finite candidates agree on every shared depth;
each is a restriction of the same physical source fold. -/
theorem finiteEnactmentCandidates_agreeOnCommonDepth
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (leftFuel rightFuel : Nat)
    (leftCandidate :
      FiniteEnactmentCycleCandidateAt initial leftFuel)
    (rightCandidate :
      FiniteEnactmentCycleCandidateAt initial rightFuel)
    (leftBase : HEq (leftCandidate ⟨0, by omega⟩) initial)
    (rightBase : HEq (rightCandidate ⟨0, by omega⟩) initial)
    (leftStep : ∀ edge : Fin leftFuel,
      HEq (leftCandidate (edgeTargetNode edge))
        (generatedNextCycleAt
          (leftCandidate (edgeSourceNode edge))))
    (rightStep : ∀ edge : Fin rightFuel,
      HEq (rightCandidate (edgeTargetNode edge))
        (generatedNextCycleAt
          (rightCandidate (edgeSourceNode edge))))
    (leftNode : Fin (leftFuel + 1))
    (rightNode : Fin (rightFuel + 1))
    (sameDepth : leftNode.1 = rightNode.1) :
    HEq (leftCandidate leftNode) (rightCandidate rightNode) := by
  have leftExact :=
    cycleAt_uniqueFiniteFold initial leftFuel leftCandidate leftBase
      leftStep leftNode
  have rightExact :=
    cycleAt_uniqueFiniteFold initial rightFuel rightCandidate rightBase
      rightStep rightNode
  have physicalExact :
      HEq (cycleAt initial leftNode.1)
        (cycleAt initial rightNode.1) := by
    rw [sameDepth]
  exact HEq.trans leftExact
    (HEq.trans physicalExact (HEq.symm rightExact))

/-- Prefix/suffix execution is the same dependent physical cycle. -/
private theorem packedCycleAt_concat
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (firstDepth secondDepth : Nat) :
    packCycleAt (cycleAt initial (firstDepth + secondDepth)) =
      packCycleAt (cycleAt (cycleAt initial firstDepth) secondDepth) := by
  induction secondDepth with
  | zero =>
      rfl
  | succ secondDepth inductionHypothesis =>
      change packedGeneratedNextCycleAt
          (packCycleAt (cycleAt initial (firstDepth + secondDepth))) =
        packedGeneratedNextCycleAt
          (packCycleAt
            (cycleAt (cycleAt initial firstDepth) secondDepth))
      exact congrArg packedGeneratedNextCycleAt inductionHypothesis

/-- Prefix/suffix execution is the same dependent physical cycle. -/
theorem cycleAt_concat
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (firstDepth secondDepth : Nat) :
    HEq (cycleAt initial (firstDepth + secondDepth))
      (cycleAt (cycleAt initial firstDepth) secondDepth) := by
  have packedExact :=
    packedCycleAt_concat initial firstDepth secondDepth
  have secondExact :
      HEq
        (packCycleAt (cycleAt initial
          (firstDepth + secondDepth))).2
        (packCycleAt
          (cycleAt (cycleAt initial firstDepth) secondDepth)).2 := by
    exact (Sigma.ext_iff.mp packedExact).2
  exact secondExact

/-- Enacted-law source data commute with prefix/suffix decomposition. -/
theorem enactedLaw_concat
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (firstDepth secondDepth : Nat) :
    HEq
        (cycleLegislationSpanAt initial (firstDepth + secondDepth))
        (cycleLegislationSpanAt (cycleAt initial firstDepth) secondDepth) ∧
      HEq
        (cyclePointwiseAcceptanceAt initial (firstDepth + secondDepth))
        (cyclePointwiseAcceptanceAt
          (cycleAt initial firstDepth) secondDepth) ∧
      HEq
        (cyclePointwiseAcceptanceAt initial (firstDepth + secondDepth)
          ).independentConsumer
        (cyclePointwiseAcceptanceAt
          (cycleAt initial firstDepth) secondDepth
          ).independentConsumer ∧
      (cyclePointwiseAcceptanceAt initial (firstDepth + secondDepth)
          ).independentConsumer.generatedNext =
        (cyclePointwiseAcceptanceAt
          (cycleAt initial firstDepth) secondDepth
          ).independentConsumer.generatedNext := by
  have packedExact :=
    packedCycleAt_concat initial firstDepth secondDepth
  have spanExact := dependentCongrArgHEq
    (fun packed : PackedCycleAt oldVisit sourceIndex => packed.2.1)
    packedExact
  have acceptanceExact := dependentCongrArgHEq
    (fun packed : PackedCycleAt oldVisit sourceIndex =>
      cyclePointwiseAcceptanceAt packed.2 0)
    packedExact
  have consumerExact := dependentCongrArgHEq
    (fun packed : PackedCycleAt oldVisit sourceIndex =>
      (cyclePointwiseAcceptanceAt packed.2 0).independentConsumer)
    packedExact
  have nextExact := dependentCongrArgHEq
    (fun packed : PackedCycleAt oldVisit sourceIndex =>
      (cyclePointwiseAcceptanceAt packed.2 0
        ).independentConsumer.generatedNext)
    packedExact
  exact ⟨spanExact, acceptanceExact, consumerExact, eq_of_heq nextExact⟩

end
end M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold.cycleAt_uniqueFiniteFold
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold.finiteEnactmentCandidates_agreeOnCommonDepth
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold.cycleAt_concat
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAcceptedLegislationFiniteFold.enactedLaw_concat
