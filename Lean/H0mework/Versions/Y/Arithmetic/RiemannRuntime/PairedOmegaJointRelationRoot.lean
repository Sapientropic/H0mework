import H0mework.Foundation.Source.TraceAdvance
import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaJointRelationMaterial

/-!
# Same-root faithful realization of the full paired-Omega relation

The full joint history/evaluator is adjoined before emission to the existing
detector-faithful authority.  Its stage seed and continuation generate both
scale faces and the installed-balance relation family.  Coverage and
soundness of the whole generated closure are proved in the adjacent coverage
module so this root authority remains small.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalFaithfulSettlementFace
open CofinalFaithfulSettlementFace.RootGeneratedCofinalFaithfulSettlementStepAt

noncomputable section

def runtimeJointFaithfulAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeEffectFaithfulAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw

def runtimeJointFaithfulLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeJointFaithfulAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeJointFaithfulAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimeJointFaithfulRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeJointFaithfulLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeJointFaithfulRoot_reuses_lower_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeJointFaithfulRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeJointFaithfulRoot observation nontrivial).emitted = emitted := by
  exact ⟨rfl, rfl⟩

def runtimeJointFaithfulInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeJointFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeEffectFaithfulAuthoritySource observation nontrivial)
    (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw

def runtimeJointFaithfulInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectFaithfulAuthoritySource observation nontrivial).projectionLaw
      (runtimeJointFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeEffectFaithfulAuthoritySource observation nontrivial)
    (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw

abbrev runtimeJointFaithfulRecognition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalFaithfulRecognitionAt
      PairedOmegaJointRelationCarrier
      (runtimeJointFaithfulRoot observation nontrivial) :=
  SourceNativeCofinalFaithfulRecognitionAt.create
    (runtimeJointFaithfulMaterialLaw observation nontrivial)
    (runtimeJointFaithfulInstallation observation nontrivial)

def runtimeJointFaithfulVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeJointFaithfulRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

abbrev runtimeJointFaithfulStepAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    RootGeneratedCofinalFaithfulSettlementStepAt
      (runtimeJointFaithfulRecognition observation nontrivial)
      (runtimeJointFaithfulVisitAt observation nontrivial depth) :=
  (runtimeJointFaithfulRecognition observation nontrivial).generateStepAt
    (runtimeJointFaithfulVisitAt observation nontrivial depth)

/-- The later installed classifier reads exactly the raw classification
calculated from this original native occurrence. -/
theorem runtimeJointFaithfulStep_residual_eq_raw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth).residualDisposition =
      runtimeJointRawResidualAt observation nontrivial
        (CanonicalUnitArithmeticRoot.emitted
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current) :=
  rfl

@[simp] theorem runtimeJointFaithfulStepAt_seed_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).history.seed.root =
        runtimeJointIncidencePresentedEvent depth := by
  change runtimeJointIncidencePresentedEvent
      (currentEffectStage
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current) = _
  rw [currentEffectStage_finiteVisit]

@[simp] theorem runtimeJointFaithfulStepAt_seed_frontier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).history.seed.frontier =
        [runtimeJointBalancePresentedEvent depth] := by
  change (runtimeJointRelationSeedAt
    (currentEffectStage
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).frontier = _
  rw [currentEffectStage_finiteVisit,
    runtimeJointRelationSeedAt_frontier]

@[simp] theorem runtimeJointFaithfulStepAt_continuation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).history.actualContinuation event =
        runtimeJointShiftContinuationAt event :=
  rfl

theorem runtimeJointFaithfulObservation_frontier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    ((runtimeJointFaithfulStepAt observation nontrivial depth
      ).history.observation stage).frontier =
        [runtimeJointBalancePresentedEvent (depth + stage)] := by
  induction stage with
  | zero =>
      change
        (runtimeJointFaithfulStepAt observation nontrivial depth
          ).history.seed.frontier =
            [runtimeJointBalancePresentedEvent depth]
      exact runtimeJointFaithfulStepAt_seed_frontier
        observation nontrivial depth
  | succ stage inductionHypothesis =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ,
        RootedAccountedUnfolding.frontier_advance,
        inductionHypothesis]
      change
        (runtimeJointShiftContinuationAt
          (runtimeJointBalancePresentedEvent (depth + stage))).frontier =
            [runtimeJointBalancePresentedEvent (depth + (stage + 1))]
      simp [Nat.add_assoc]

end


end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
