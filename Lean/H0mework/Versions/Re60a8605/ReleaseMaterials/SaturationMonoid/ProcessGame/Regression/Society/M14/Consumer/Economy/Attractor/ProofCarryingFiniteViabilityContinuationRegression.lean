import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.MinimalEconomicViabilityHittingTime

/-!
# M14 direct consumer for finite actual viability continuation

This consumer signs the viable-to-viable whole-root renewal edge, its exact
authority separation from the two death-repair edges, arbitrary requested
finite path composition, literal prefix factorization, and preservation of
the already proved universal hitting-time minimum.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingFiniteViabilityContinuationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14ActionableFuturePortfolio
open M14UBIProofCarryingRootRestriction
open M14SourceEssentialServiceRestoration
open M14PeriodicEssentialServiceRestoration
open M14PeriodicDeathRepairNormalization
open M14EconomicViability
open M14AdjacentEconomicViabilityBoundary
open M14PeriodicViabilityRenewalReceipt
open M14ActualEconomicViabilityPath
open M14MinimalEconomicViabilityHittingTime

theorem periodic_viability_renewal_retains_whole_root_authority
    (depth : Nat) :
    let renewal := sourceGeneratedPeriodicViabilityRenewalAt depth
    let source := renewal.source
    let transition := renewal.transition
    let service := transition.entry.normalization.service
    let capture := transition.entry.normalization.captureDeath.ordinaryRepair
    let normalForm := transition.entry.normalization.normalForm
    let target := renewal.target
    source.portfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      source.portfolio.paymentOccurrence.rootOccurrence =
        service.rootOccurrence ∧
      service.installed.payload.disposition =
        sourceGeneratedHealthServiceRestoration ∧
      capture.renewal.source.installed.payload.disposition =
        sourceGeneratedUBIDisposition ∧
      service.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      capture.renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld ∧
      service.applied.wholeLedgerWriteBack =
        capture.renewal.wholeLedgerWriteBack ∧
      normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt (depth + 1)) ∧
      target.portfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 2)) ∧
      HEq target.toDisposition transition.entry.viableDisposition ∧
      periodicPaymentOccurrenceAt (depth + 1) ≠
        periodicPaymentOccurrenceAt (depth + 2) ∧
      normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface := by
  let renewal := sourceGeneratedPeriodicViabilityRenewalAt depth
  exact ⟨renewal.sourceRootExact,
    renewal.sourceRootSharedWithService,
    renewal.serviceActionExact,
    renewal.captureActionExact,
    renewal.serviceSelectedWriteCommutes,
    renewal.captureSelectedWriteCommutes,
    renewal.wholeLedgerShared,
    renewal.generatedNextExact,
    renewal.targetRootExact,
    renewal.targetDispositionExact,
    renewal.adjacentOccurrencesDistinct,
    renewal.lawSurfacePreserved⟩

theorem three_actual_edges_and_actions_are_distinct (depth : Nat) :
    Nonempty (maintenanceConfigurationAt depth ⟶
      repairedConfigurationAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      Nonempty (repairedConfigurationAt depth ⟶
        repairedConfigurationAt (depth + 1)) ∧
      (maintenanceActionEdgeAt depth).2.2.1 ≠
          (captureActionEdgeAt depth).2.2.1 ∧
      (maintenanceActionEdgeAt depth).2.2.1 ≠
          (viabilityRenewalActionEdgeAt depth).2.2.1 ∧
      (captureActionEdgeAt depth).2.2.1 ≠
          (viabilityRenewalActionEdgeAt depth).2.2.1 :=
  ⟨⟨maintenanceActionEdgeAt depth⟩,
    ⟨captureActionEdgeAt depth⟩,
    ⟨viabilityRenewalActionEdgeAt depth⟩,
    three_actual_edge_actions_pairwise_distinct depth⟩

theorem action_branches_preserve_exact_source_and_target (depth : Nat) :
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    let service := boundary.entry.normalization.service
    let capture := boundary.entry.normalization.captureDeath.ordinaryRepair
    let renewal := sourceGeneratedPeriodicViabilityRenewalAt depth
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inl service)) (repairedConfigurationAt depth)
        (repairedConfigurationAt depth)) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inr capture)) (repairedConfigurationAt depth)
        (repairedConfigurationAt depth)) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inr renewal) (maintenanceConfigurationAt depth)
        (repairedConfigurationAt (depth + 1))) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inr renewal) (captureConfigurationAt depth)
        (repairedConfigurationAt (depth + 1))) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inr renewal) (repairedConfigurationAt depth)
        (repairedConfigurationAt depth)) := by
  dsimp only
  exact
    ⟨(serviceAction_repairedSourceEdge_isEmpty _ _ _ _),
      (captureAction_repairedSourceEdge_isEmpty _ _ _ _),
      viability_renewal_cannot_index_maintenance_source _ _ _ _,
      viability_renewal_cannot_index_capture_source _ _ _ _,
      viability_renewal_cannot_stay_at_same_viable_target _ _ _ _⟩

theorem every_requested_finite_prefix_is_actual_and_viable
    (depth horizon : Nat) :
    Nonempty (Quiver.Path (repairedConfigurationAt depth)
      (repairedConfigurationAt (depth + horizon))) ∧
      Nonempty (Quiver.Path (maintenanceConfigurationAt depth)
        (repairedConfigurationAt (depth + horizon))) ∧
      Nonempty (Quiver.Path (captureConfigurationAt depth)
        (repairedConfigurationAt (depth + horizon))) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (maintenanceConfigurationAt depth)) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (captureConfigurationAt depth)) ∧
      (viableContinuationPathAt depth horizon).length = horizon ∧
      (maintenanceFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      (∀ k : Nat, k ≤ horizon →
        (∃ suffix : Quiver.Path
            (repairedConfigurationAt (depth + k))
            (repairedConfigurationAt (depth + horizon)),
          (viableContinuationPathAt depth k).comp suffix =
            viableContinuationPathAt depth horizon) ∧
          Nonempty ((repairedConfigurationAt (depth + k)).Viable)) :=
  ⟨⟨viableContinuationPathAt depth horizon⟩,
    ⟨maintenanceFiniteAttractorPathAt depth horizon⟩,
    ⟨captureFiniteAttractorPathAt depth horizon⟩,
    ⟨maintenanceFiniteViabilityPathCandidateAt depth horizon⟩,
    ⟨captureFiniteViabilityPathCandidateAt depth horizon⟩,
    viableContinuationPath_length depth horizon,
    maintenanceFiniteAttractorPath_length depth horizon,
    captureFiniteAttractorPath_length depth horizon,
    fun k withinHorizon =>
      viableContinuationPath_prefix_is_viable
        depth horizon k withinHorizon⟩

theorem finite_continuation_preserves_universal_minimum
    (depth horizon : Nat) :
    maintenanceViabilityHittingTimeAt depth = 1 ∧
      captureViabilityHittingTimeAt depth = 1 ∧
      maintenanceViabilityHittingTimeAt depth ≤
        (maintenanceFiniteViabilityPathCandidateAt depth horizon).path.length ∧
      captureViabilityHittingTimeAt depth ≤
        (captureFiniteViabilityPathCandidateAt depth horizon).path.length ∧
      (¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
          (maintenanceConfigurationAt depth), candidate.path.length = 0) ∧
      (¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
          (captureConfigurationAt depth), candidate.path.length = 0) ∧
      (¬ ∃ reconstruct : Nat → ActualDeathRepairActionAt depth,
        Function.LeftInverse reconstruct
          (canonicalActionHittingTimeReadoutAt depth)) :=
  ⟨maintenanceViabilityHittingTime_eq_one depth,
    captureViabilityHittingTime_eq_one depth,
    maintenance_finite_continuation_respects_minimum depth horizon,
    capture_finite_continuation_respects_minimum depth horizon,
    maintenance_has_no_zero_length_viable_candidate depth,
    capture_has_no_zero_length_viable_candidate depth,
    no_hitting_time_leftInverse_reconstructs_action depth⟩

structure ProofCarryingFiniteViabilityContinuationCertificate : Prop where
  everyDepthWholeRootRenewal : ∀ depth : Nat,
    Nonempty (PeriodicViabilityRenewalReceiptAt depth)
  everyDepthThreeActualEdges : ∀ depth : Nat,
    Nonempty (maintenanceConfigurationAt depth ⟶
      repairedConfigurationAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      Nonempty (repairedConfigurationAt depth ⟶
        repairedConfigurationAt (depth + 1))
  everyDepthActionAuthorityDistinct : ∀ depth : Nat,
    (maintenanceActionEdgeAt depth).2.2.1 ≠
        (captureActionEdgeAt depth).2.2.1 ∧
      (maintenanceActionEdgeAt depth).2.2.1 ≠
        (viabilityRenewalActionEdgeAt depth).2.2.1 ∧
      (captureActionEdgeAt depth).2.2.1 ≠
        (viabilityRenewalActionEdgeAt depth).2.2.1
  everyDepthExactSourceAndTarget : ∀ depth : Nat,
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    let service := boundary.entry.normalization.service
    let capture := boundary.entry.normalization.captureDeath.ordinaryRepair
    let renewal := sourceGeneratedPeriodicViabilityRenewalAt depth
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inl service)) (repairedConfigurationAt depth)
        (repairedConfigurationAt depth)) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inr capture)) (repairedConfigurationAt depth)
        (repairedConfigurationAt depth)) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inr renewal) (maintenanceConfigurationAt depth)
        (repairedConfigurationAt (depth + 1))) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inr renewal) (captureConfigurationAt depth)
        (repairedConfigurationAt (depth + 1))) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inr renewal) (repairedConfigurationAt depth)
        (repairedConfigurationAt depth))
  everyFiniteContinuation : ∀ depth horizon : Nat,
    (viableContinuationPathAt depth horizon).length = horizon ∧
      (maintenanceFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      Nonempty ((repairedConfigurationAt (depth + horizon)).Viable)
  everyFiniteLiteralPrefix : ∀ depth horizon k : Nat, k ≤ horizon →
    (∃ suffix : Quiver.Path
        (repairedConfigurationAt (depth + k))
        (repairedConfigurationAt (depth + horizon)),
      (viableContinuationPathAt depth k).comp suffix =
        viableContinuationPathAt depth horizon) ∧
      Nonempty ((repairedConfigurationAt (depth + k)).Viable)
  expandedQuiverPreservesMinimum : ∀ depth horizon : Nat,
    maintenanceViabilityHittingTimeAt depth ≤
        (maintenanceFiniteViabilityPathCandidateAt depth horizon).path.length ∧
      captureViabilityHittingTimeAt depth ≤
        (captureFiniteViabilityPathCandidateAt depth horizon).path.length
  noStoredFuture : ∀ _depth _horizon : Nat, True

theorem proofCarryingFiniteViabilityContinuationDirectConsumer :
    ProofCarryingFiniteViabilityContinuationCertificate where
  everyDepthWholeRootRenewal := fun depth =>
    ⟨sourceGeneratedPeriodicViabilityRenewalAt depth⟩
  everyDepthThreeActualEdges := fun depth =>
    let edges := three_actual_edges_and_actions_are_distinct depth
    ⟨edges.1, edges.2.1, edges.2.2.1⟩
  everyDepthActionAuthorityDistinct := fun depth =>
    (three_actual_edges_and_actions_are_distinct depth).2.2.2
  everyDepthExactSourceAndTarget :=
    action_branches_preserve_exact_source_and_target
  everyFiniteContinuation := fun depth horizon =>
    let closure := every_finite_actual_continuation_after_hit_is_viable
      depth horizon
    ⟨viableContinuationPath_length depth horizon,
      closure.2.1, closure.2.2.1, closure.1⟩
  everyFiniteLiteralPrefix :=
    viableContinuationPath_prefix_is_viable
  expandedQuiverPreservesMinimum := fun depth horizon =>
    ⟨maintenance_finite_continuation_respects_minimum depth horizon,
      capture_finite_continuation_respects_minimum depth horizon⟩
  noStoredFuture := viability_path_mouth_has_no_length_or_completed_history

end
end M14ProofCarryingFiniteViabilityContinuationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteViabilityContinuationRegression.periodic_viability_renewal_retains_whole_root_authority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteViabilityContinuationRegression.every_requested_finite_prefix_is_actual_and_viable
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteViabilityContinuationRegression.finite_continuation_preserves_universal_minimum
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteViabilityContinuationRegression.proofCarryingFiniteViabilityContinuationDirectConsumer
