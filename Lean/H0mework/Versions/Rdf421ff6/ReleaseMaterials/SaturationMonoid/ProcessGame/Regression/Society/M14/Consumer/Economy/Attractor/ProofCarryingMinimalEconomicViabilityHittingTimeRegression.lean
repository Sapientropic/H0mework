import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.MinimalEconomicViabilityHittingTime

/-!
# M14 direct consumer for minimal viability hitting time

This consumer verifies the actual receipt arrows, their length-one paths, the
generic nil-path obstruction, universal minimality, and the strict observer
residual: two distinct repair authorities have the same minimal hitting-time
readout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIExitCapacityFixture
open M14ActionableFuturePortfolio
open M14EconomicViability
open M14AdjacentEconomicViabilityBoundary
open M14PeriodicNormalizedViableDisposition
open M14ActualEconomicViabilityPath
open M14MinimalEconomicViabilityHittingTime

theorem actual_receipts_generate_length_one_paths (depth : Nat) :
    Nonempty (maintenanceConfigurationAt depth ⟶
      repairedConfigurationAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (maintenanceConfigurationAt depth)) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (captureConfigurationAt depth)) ∧
      maintenanceViabilityHittingTimeAt depth = 1 ∧
      captureViabilityHittingTimeAt depth = 1 :=
  ⟨⟨maintenanceActionEdgeAt depth⟩,
    ⟨captureActionEdgeAt depth⟩,
    ⟨maintenanceViabilityPathCandidateAt depth⟩,
    ⟨captureViabilityPathCandidateAt depth⟩,
    maintenanceViabilityHittingTime_eq_one depth,
    captureViabilityHittingTime_eq_one depth⟩

theorem receipt_actions_cannot_cross_sources (depth : Nat) :
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inl boundary.entry.normalization.service))
        (captureConfigurationAt depth) (repairedConfigurationAt depth)) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inr
          boundary.entry.normalization.captureDeath.ordinaryRepair))
        (maintenanceConfigurationAt depth) (repairedConfigurationAt depth)) := by
  dsimp only
  exact
    ⟨service_receipt_cannot_index_capture_source _ _ _ _,
      capture_repair_cannot_index_maintenance_source _ _ _ _⟩

theorem both_minima_are_universal (depth : Nat) :
    (∀ other : SourceGeneratedViabilityPathCandidateAt
        (maintenanceConfigurationAt depth),
      maintenanceViabilityHittingTimeAt depth ≤ other.path.length) ∧
      (∀ other : SourceGeneratedViabilityPathCandidateAt
          (captureConfigurationAt depth),
        captureViabilityHittingTimeAt depth ≤ other.path.length) ∧
      (¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
          (maintenanceConfigurationAt depth), candidate.path.length = 0) ∧
      (¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
          (captureConfigurationAt depth), candidate.path.length = 0) :=
  ⟨maintenance_hitting_time_is_universally_minimal depth,
    capture_hitting_time_is_universally_minimal depth,
    maintenance_has_no_zero_length_viable_candidate depth,
    capture_has_no_zero_length_viable_candidate depth⟩

theorem equal_minimal_time_does_not_reconstruct_action (depth : Nat) :
    maintenanceActualActionAt depth ≠ captureActualActionAt depth ∧
      canonicalActionHittingTimeReadoutAt depth
          (maintenanceActualActionAt depth) =
        canonicalActionHittingTimeReadoutAt depth
          (captureActualActionAt depth) ∧
      (¬ ∃ reconstruct : Nat → ActualDeathRepairActionAt depth,
        Function.LeftInverse reconstruct
          (canonicalActionHittingTimeReadoutAt depth)) := by
  let same := distinct_actions_have_same_minimal_hitting_time depth
  exact ⟨same.1, same.2.1.trans same.2.2.symm,
    no_hitting_time_leftInverse_reconstructs_action depth⟩

theorem path_candidates_retain_adjacent_boundary (depth : Nat) :
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    Nonempty (AdjacentBoundaryAt depth) ∧
      boundary.maintenanceOffsetZeroEmpty =
        maintenanceEconomicViability_isEmpty depth ∧
      boundary.captureOffsetZeroEmpty =
        captureEconomicViability_isEmpty depth ∧
      Nonempty ((repairedConfigurationAt depth).Viable) ∧
      boundary.adjacentOccurrencesDistinct =
        SourceGeneratedPeriodicNormalizedViableDispositionAt.adjacentOccurrencesDistinct
          (sourceGeneratedPeriodicNormalizedViableDispositionAt depth) := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  exact ⟨⟨boundary⟩, Subsingleton.elim _ _, Subsingleton.elim _ _,
    ⟨sourceGeneratedPeriodicEconomicViabilityAt depth⟩,
    Subsingleton.elim _ _⟩

structure ProofCarryingMinimalEconomicViabilityHittingTimeCertificate : Prop where
  everyDepthActualPaths : ∀ depth : Nat,
    Nonempty (maintenanceConfigurationAt depth ⟶
      repairedConfigurationAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (maintenanceConfigurationAt depth)) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (captureConfigurationAt depth)) ∧
      maintenanceViabilityHittingTimeAt depth = 1 ∧
      captureViabilityHittingTimeAt depth = 1
  everyDepthExactSourceAuthority : ∀ depth : Nat,
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inl boundary.entry.normalization.service))
        (captureConfigurationAt depth) (repairedConfigurationAt depth)) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inr
          boundary.entry.normalization.captureDeath.ordinaryRepair))
        (maintenanceConfigurationAt depth) (repairedConfigurationAt depth))
  everyDepthUniversalMinimum : ∀ depth : Nat,
    (∀ other : SourceGeneratedViabilityPathCandidateAt
        (maintenanceConfigurationAt depth),
      maintenanceViabilityHittingTimeAt depth ≤ other.path.length) ∧
      (∀ other : SourceGeneratedViabilityPathCandidateAt
          (captureConfigurationAt depth),
        captureViabilityHittingTimeAt depth ≤ other.path.length) ∧
      (¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
          (maintenanceConfigurationAt depth), candidate.path.length = 0) ∧
      (¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
          (captureConfigurationAt depth), candidate.path.length = 0)
  everyDepthObserverResidual : ∀ depth : Nat,
    maintenanceActualActionAt depth ≠ captureActualActionAt depth ∧
      canonicalActionHittingTimeReadoutAt depth
          (maintenanceActualActionAt depth) =
        canonicalActionHittingTimeReadoutAt depth
          (captureActualActionAt depth) ∧
      (¬ ∃ reconstruct : Nat → ActualDeathRepairActionAt depth,
        Function.LeftInverse reconstruct
          (canonicalActionHittingTimeReadoutAt depth))
  everyDepthBoundaryRetained : ∀ depth : Nat,
    Nonempty (AdjacentBoundaryAt depth) ∧
      Nonempty ((repairedConfigurationAt depth).Viable)
  noOptimizerOrCompletedHistory : ∀ _depth : Nat, True

theorem proofCarryingMinimalEconomicViabilityHittingTimeDirectConsumer :
    ProofCarryingMinimalEconomicViabilityHittingTimeCertificate where
  everyDepthActualPaths := actual_receipts_generate_length_one_paths
  everyDepthExactSourceAuthority := receipt_actions_cannot_cross_sources
  everyDepthUniversalMinimum := both_minima_are_universal
  everyDepthObserverResidual := equal_minimal_time_does_not_reconstruct_action
  everyDepthBoundaryRetained := fun depth =>
    ⟨(path_candidates_retain_adjacent_boundary depth).1,
      (path_candidates_retain_adjacent_boundary depth).2.2.2.1⟩
  noOptimizerOrCompletedHistory :=
    minimal_hitting_mouth_has_no_optimizer_or_completed_history

end
end M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression.actual_receipts_generate_length_one_paths
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression.receipt_actions_cannot_cross_sources
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression.both_minima_are_universal
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression.equal_minimal_time_does_not_reconstruct_action
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMinimalEconomicViabilityHittingTimeRegression.proofCarryingMinimalEconomicViabilityHittingTimeDirectConsumer
