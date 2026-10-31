import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.FiniteViabilityContinuation

/-!
# M14 minimal economic-viability hitting time

The canonical service-restoration and remove-capture paths both have length
one by `Quiver.Hom.toPath`.  Every generated candidate from either nonviable
source has positive length because a nil path would identify its viable target
with the nonviable source.  Hence the actual length-one paths are universally
minimal.

The hitting time is only a path-length readout.  No caller supplies a number,
candidate set, coverage proof, optimizer, or completed history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14MinimalEconomicViabilityHittingTime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIExitCapacityFixture
open M14ActionableFuturePortfolio
open M14EconomicViability
open M14ActualEconomicViabilityPath

structure SourceGeneratedMinimalViabilityHittingAt
    (source : EconomicConfiguration)
    (canonical : SourceGeneratedViabilityPathCandidateAt source) : Prop where
  private mk ::
  sourceNonviable : IsEmpty source.Viable
  minimal : ∀ other : SourceGeneratedViabilityPathCandidateAt source,
    canonical.path.length ≤ other.path.length

theorem sourceGeneratedMaintenanceMinimalViabilityHittingAt (depth : Nat) :
    SourceGeneratedMinimalViabilityHittingAt
      (maintenanceConfigurationAt depth)
      (maintenanceViabilityPathCandidateAt depth) where
  sourceNonviable := by
    change IsEmpty (EconomicViabilityAt depth
      (stablePortfolioSourceAt depth) noCapture)
    exact maintenanceEconomicViability_isEmpty depth
  minimal := fun other => by
    rw [maintenanceViabilityPathCandidate_length]
    exact maintenance_candidate_path_length_pos depth other

theorem sourceGeneratedCaptureMinimalViabilityHittingAt (depth : Nat) :
    SourceGeneratedMinimalViabilityHittingAt
      (captureConfigurationAt depth)
      (captureViabilityPathCandidateAt depth) where
  sourceNonviable := by
    change IsEmpty (EconomicViabilityAt depth
      (fullPortfolioSourceAt depth) fullCapture)
    exact captureEconomicViability_isEmpty depth
  minimal := fun other => by
    rw [captureViabilityPathCandidate_length]
    exact capture_candidate_path_length_pos depth other

def maintenanceViabilityHittingTimeAt (depth : Nat) : Nat :=
  (maintenanceViabilityPathCandidateAt depth).path.length

def captureViabilityHittingTimeAt (depth : Nat) : Nat :=
  (captureViabilityPathCandidateAt depth).path.length

@[simp] theorem maintenanceViabilityHittingTime_eq_one (depth : Nat) :
    maintenanceViabilityHittingTimeAt depth = 1 :=
  maintenanceViabilityPathCandidate_length depth

@[simp] theorem captureViabilityHittingTime_eq_one (depth : Nat) :
    captureViabilityHittingTimeAt depth = 1 :=
  captureViabilityPathCandidate_length depth

theorem maintenance_hitting_time_is_universally_minimal (depth : Nat)
    (other : SourceGeneratedViabilityPathCandidateAt
      (maintenanceConfigurationAt depth)) :
    maintenanceViabilityHittingTimeAt depth ≤ other.path.length :=
  (sourceGeneratedMaintenanceMinimalViabilityHittingAt depth).minimal other

theorem capture_hitting_time_is_universally_minimal (depth : Nat)
    (other : SourceGeneratedViabilityPathCandidateAt
      (captureConfigurationAt depth)) :
    captureViabilityHittingTimeAt depth ≤ other.path.length :=
  (sourceGeneratedCaptureMinimalViabilityHittingAt depth).minimal other

theorem maintenance_finite_continuation_respects_minimum
    (depth horizon : Nat) :
    maintenanceViabilityHittingTimeAt depth ≤
      (maintenanceFiniteViabilityPathCandidateAt depth horizon).path.length :=
  maintenance_hitting_time_is_universally_minimal depth
    (maintenanceFiniteViabilityPathCandidateAt depth horizon)

theorem capture_finite_continuation_respects_minimum
    (depth horizon : Nat) :
    captureViabilityHittingTimeAt depth ≤
      (captureFiniteViabilityPathCandidateAt depth horizon).path.length :=
  capture_hitting_time_is_universally_minimal depth
    (captureFiniteViabilityPathCandidateAt depth horizon)

theorem maintenance_has_no_zero_length_viable_candidate (depth : Nat) :
    ¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
      (maintenanceConfigurationAt depth), candidate.path.length = 0 := by
  rintro ⟨candidate, lengthZero⟩
  have positive := maintenance_candidate_path_length_pos depth candidate
  omega

theorem capture_has_no_zero_length_viable_candidate (depth : Nat) :
    ¬ ∃ candidate : SourceGeneratedViabilityPathCandidateAt
      (captureConfigurationAt depth), candidate.path.length = 0 := by
  rintro ⟨candidate, lengthZero⟩
  have positive := capture_candidate_path_length_pos depth candidate
  omega

/-! ## Hitting-time observer loses action authority -/

def canonicalActionHittingTimeReadoutAt (depth : Nat) :
    ActualDeathRepairActionAt depth → Nat
  | .inl _ => maintenanceViabilityHittingTimeAt depth
  | .inr _ => captureViabilityHittingTimeAt depth

theorem distinct_actions_have_same_minimal_hitting_time (depth : Nat) :
    maintenanceActualActionAt depth ≠ captureActualActionAt depth ∧
      canonicalActionHittingTimeReadoutAt depth
          (maintenanceActualActionAt depth) = 1 ∧
      canonicalActionHittingTimeReadoutAt depth
          (captureActualActionAt depth) = 1 :=
  ⟨maintenance_capture_actions_distinct depth, rfl, rfl⟩

theorem no_hitting_time_leftInverse_reconstructs_action (depth : Nat) :
    ¬ ∃ reconstruct : Nat → ActualDeathRepairActionAt depth,
      Function.LeftInverse reconstruct
        (canonicalActionHittingTimeReadoutAt depth) := by
  rintro ⟨reconstruct, leftInverse⟩
  have maintenanceRecovered := leftInverse (maintenanceActualActionAt depth)
  have captureRecovered := leftInverse (captureActualActionAt depth)
  have readoutEqual :
      canonicalActionHittingTimeReadoutAt depth
          (maintenanceActualActionAt depth) =
        canonicalActionHittingTimeReadoutAt depth
          (captureActualActionAt depth) :=
    (distinct_actions_have_same_minimal_hitting_time depth).2.1.trans
      (distinct_actions_have_same_minimal_hitting_time depth).2.2.symm
  apply maintenance_capture_actions_distinct depth
  exact maintenanceRecovered.symm.trans
    ((congrArg reconstruct readoutEqual).trans captureRecovered)

theorem minimal_hitting_mouth_has_no_optimizer_or_completed_history
    (depth : Nat) : True := by
  let minimal := sourceGeneratedMaintenanceMinimalViabilityHittingAt depth
  fail_if_success exact minimal.optimizer
  fail_if_success exact minimal.coverage
  fail_if_success exact minimal.candidateList
  fail_if_success exact minimal.completedHistory
  fail_if_success exact minimal.u8Gate
  trivial

end
end M14MinimalEconomicViabilityHittingTime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14MinimalEconomicViabilityHittingTime.sourceGeneratedMaintenanceMinimalViabilityHittingAt
#print axioms SaturationMonoid.ProcessGame.Society.M14MinimalEconomicViabilityHittingTime.sourceGeneratedCaptureMinimalViabilityHittingAt
#print axioms SaturationMonoid.ProcessGame.Society.M14MinimalEconomicViabilityHittingTime.maintenance_finite_continuation_respects_minimum
#print axioms SaturationMonoid.ProcessGame.Society.M14MinimalEconomicViabilityHittingTime.capture_finite_continuation_respects_minimum
#print axioms SaturationMonoid.ProcessGame.Society.M14MinimalEconomicViabilityHittingTime.no_hitting_time_leftInverse_reconstructs_action
