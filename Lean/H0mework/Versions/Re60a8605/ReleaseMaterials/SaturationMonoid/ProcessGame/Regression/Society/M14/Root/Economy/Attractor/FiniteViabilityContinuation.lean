import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.ActualEconomicViabilityPath

/-!
# M14 finite actual viability continuation

The actual viable-renewal edge is composed only for the finite horizon
requested by the caller.  Both death-repair edges may then be prefixed to
the same continuation, producing genuine paths into every requested viable
future configuration.

There is no stored `Nat →` receipt, path, target, or completed future.  The
candidate constructor remains private in this file; public candidate
producers accept only `depth` and `horizon`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ActualEconomicViabilityPath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open M14UBIExitCapacityFixture
open M14ActionableFuturePortfolio
open M14EconomicViability
open M14PeriodicViabilityRenewalReceipt

/-! ## On-demand finite viable continuation -/

def viableContinuationPathAt (depth : Nat) :
    (horizon : Nat) → Quiver.Path
      (repairedConfigurationAt depth)
      (repairedConfigurationAt (depth + horizon))
  | 0 => .nil
  | horizon + 1 =>
      (viableContinuationPathAt depth horizon).cons
        (viabilityRenewalActionEdgeAt (depth + horizon))

@[simp] theorem viableContinuationPath_length
    (depth horizon : Nat) :
    (viableContinuationPathAt depth horizon).length = horizon := by
  induction horizon with
  | zero => rfl
  | succ horizon inductionHypothesis =>
      simp [viableContinuationPathAt, inductionHypothesis]

def maintenanceFiniteAttractorPathAt (depth horizon : Nat) :
    Quiver.Path (maintenanceConfigurationAt depth)
      (repairedConfigurationAt (depth + horizon)) :=
  (maintenanceActionEdgeAt depth).toPath.comp
    (viableContinuationPathAt depth horizon)

def captureFiniteAttractorPathAt (depth horizon : Nat) :
    Quiver.Path (captureConfigurationAt depth)
      (repairedConfigurationAt (depth + horizon)) :=
  (captureActionEdgeAt depth).toPath.comp
    (viableContinuationPathAt depth horizon)

@[simp] theorem maintenanceFiniteAttractorPath_length
    (depth horizon : Nat) :
    (maintenanceFiniteAttractorPathAt depth horizon).length = horizon + 1 := by
  simp [maintenanceFiniteAttractorPathAt, Nat.add_comm]

@[simp] theorem captureFiniteAttractorPath_length
    (depth horizon : Nat) :
    (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 := by
  simp [captureFiniteAttractorPathAt, Nat.add_comm]

def finiteContinuationTargetViabilityAt (depth horizon : Nat) :
    (repairedConfigurationAt (depth + horizon)).Viable :=
  sourceGeneratedPeriodicEconomicViabilityAt (depth + horizon)

/-- Every shorter requested continuation is a literal prefix of the longer
actual path, not merely another pointwise path with the same readout. -/
theorem viableContinuationPath_prefix_factorizes
    (depth horizon k : Nat) (withinHorizon : k ≤ horizon) :
    ∃ suffix : Quiver.Path
        (repairedConfigurationAt (depth + k))
        (repairedConfigurationAt (depth + horizon)),
      (viableContinuationPathAt depth k).comp suffix =
        viableContinuationPathAt depth horizon := by
  refine Nat.le_induction ?_ ?_ horizon withinHorizon
  · exact ⟨.nil, rfl⟩
  · intro current _currentWithin
    rintro ⟨suffix, factorization⟩
    refine ⟨suffix.cons
      (viabilityRenewalActionEdgeAt (depth + current)), ?_⟩
    rw [Quiver.Path.comp_cons, factorization]
    rfl

theorem viableContinuationPath_prefix_is_viable
    (depth horizon k : Nat) (withinHorizon : k ≤ horizon) :
    (∃ suffix : Quiver.Path
        (repairedConfigurationAt (depth + k))
        (repairedConfigurationAt (depth + horizon)),
      (viableContinuationPathAt depth k).comp suffix =
        viableContinuationPathAt depth horizon) ∧
      Nonempty ((repairedConfigurationAt (depth + k)).Viable) :=
  ⟨viableContinuationPath_prefix_factorizes
      depth horizon k withinHorizon,
    ⟨finiteContinuationTargetViabilityAt depth k⟩⟩

/-! ## Private candidate mouth, including every requested finite horizon -/

structure SourceGeneratedViabilityPathCandidateAt
    (source : EconomicConfiguration) : Type 18 where
  private mk ::
  target : EconomicConfiguration
  path : Quiver.Path source target
  targetViable : target.Viable

def maintenanceViabilityPathCandidateAt (depth : Nat) :
    SourceGeneratedViabilityPathCandidateAt
      (maintenanceConfigurationAt depth) where
  target := repairedConfigurationAt depth
  path := (maintenanceActionEdgeAt depth).toPath
  targetViable := sourceGeneratedPeriodicEconomicViabilityAt depth

def captureViabilityPathCandidateAt (depth : Nat) :
    SourceGeneratedViabilityPathCandidateAt
      (captureConfigurationAt depth) where
  target := repairedConfigurationAt depth
  path := (captureActionEdgeAt depth).toPath
  targetViable := sourceGeneratedPeriodicEconomicViabilityAt depth

def maintenanceFiniteViabilityPathCandidateAt (depth horizon : Nat) :
    SourceGeneratedViabilityPathCandidateAt
      (maintenanceConfigurationAt depth) where
  target := repairedConfigurationAt (depth + horizon)
  path := maintenanceFiniteAttractorPathAt depth horizon
  targetViable := finiteContinuationTargetViabilityAt depth horizon

def captureFiniteViabilityPathCandidateAt (depth horizon : Nat) :
    SourceGeneratedViabilityPathCandidateAt
      (captureConfigurationAt depth) where
  target := repairedConfigurationAt (depth + horizon)
  path := captureFiniteAttractorPathAt depth horizon
  targetViable := finiteContinuationTargetViabilityAt depth horizon

@[simp] theorem maintenanceViabilityPathCandidate_length (depth : Nat) :
    (maintenanceViabilityPathCandidateAt depth).path.length = 1 :=
  rfl

@[simp] theorem captureViabilityPathCandidate_length (depth : Nat) :
    (captureViabilityPathCandidateAt depth).path.length = 1 :=
  rfl

@[simp] theorem maintenanceFiniteViabilityPathCandidate_length
    (depth horizon : Nat) :
    (maintenanceFiniteViabilityPathCandidateAt depth horizon).path.length =
      horizon + 1 :=
  maintenanceFiniteAttractorPath_length depth horizon

@[simp] theorem captureFiniteViabilityPathCandidate_length
    (depth horizon : Nat) :
    (captureFiniteViabilityPathCandidateAt depth horizon).path.length =
      horizon + 1 :=
  captureFiniteAttractorPath_length depth horizon

/-- Any candidate from a source whose unified viability predicate is empty
has positive path length.  The nil case identifies target with source and
therefore contradicts target viability. -/
theorem viabilityCandidate_path_length_pos
    {source : EconomicConfiguration}
    (sourceEmpty : IsEmpty source.Viable)
    (candidate : SourceGeneratedViabilityPathCandidateAt source) :
    0 < candidate.path.length := by
  apply Nat.pos_of_ne_zero
  intro lengthZero
  have endpointsEqual : source = candidate.target :=
    Quiver.Path.eq_of_length_zero candidate.path lengthZero
  exact sourceEmpty.false (endpointsEqual.symm ▸ candidate.targetViable)

theorem maintenance_candidate_path_length_pos (depth : Nat)
    (candidate : SourceGeneratedViabilityPathCandidateAt
      (maintenanceConfigurationAt depth)) :
    0 < candidate.path.length :=
  viabilityCandidate_path_length_pos
    (source := maintenanceConfigurationAt depth)
    (by
      change IsEmpty (EconomicViabilityAt depth
        (stablePortfolioSourceAt depth) noCapture)
      exact maintenanceEconomicViability_isEmpty depth)
    candidate

theorem capture_candidate_path_length_pos (depth : Nat)
    (candidate : SourceGeneratedViabilityPathCandidateAt
      (captureConfigurationAt depth)) :
    0 < candidate.path.length :=
  viabilityCandidate_path_length_pos
    (source := captureConfigurationAt depth)
    (by
      change IsEmpty (EconomicViabilityAt depth
        (fullPortfolioSourceAt depth) fullCapture)
      exact captureEconomicViability_isEmpty depth)
    candidate

theorem every_finite_actual_continuation_after_hit_is_viable
    (depth horizon : Nat) :
    Nonempty ((repairedConfigurationAt (depth + horizon)).Viable) ∧
      (maintenanceFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      (∀ k : Nat, k ≤ horizon →
        (viableContinuationPathAt depth k).length = k ∧
          Nonempty ((repairedConfigurationAt (depth + k)).Viable)) := by
  refine ⟨⟨finiteContinuationTargetViabilityAt depth horizon⟩,
    maintenanceFiniteAttractorPath_length depth horizon,
    captureFiniteAttractorPath_length depth horizon, ?_⟩
  intro k _withinHorizon
  exact ⟨viableContinuationPath_length depth k,
    ⟨finiteContinuationTargetViabilityAt depth k⟩⟩

theorem viability_path_mouth_has_no_length_or_completed_history
    (depth horizon : Nat) : True := by
  let candidate := maintenanceFiniteViabilityPathCandidateAt depth horizon
  fail_if_success exact candidate.storedLength
  fail_if_success exact candidate.rank
  fail_if_success exact candidate.minimum
  fail_if_success exact candidate.coverage
  fail_if_success exact candidate.completedHistory
  fail_if_success exact candidate.futureTable
  trivial

end
end M14ActualEconomicViabilityPath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.viableContinuationPathAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.viableContinuationPath_prefix_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.viabilityCandidate_path_length_pos
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.every_finite_actual_continuation_after_hit_is_viable
