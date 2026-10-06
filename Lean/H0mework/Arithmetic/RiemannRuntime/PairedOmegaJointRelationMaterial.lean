import H0mework.Arithmetic.RiemannRuntime.PairedOmegaEffectFaithfulRoot
import H0mework.Arithmetic.RiemannRuntime.PairedOmegaJointRelationOccurrence

/-!
# Source material for the full paired-Omega relation

The stage seed contains the root-scale and quarter-scale source-boundary and
joint-incidence relations together with the root-scale and quarter-scale
balance relations.  Its only open leaf is the root-scale balance relation;
the fixed continuation reconstructs all seven at the next stage and retains the
next root-scale balance relation as the new frontier.

The history and its full evaluator are installed as one faithful-material
face over the already fixed detector-faithful source.
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
open CofinalFaithfulSettlementFace
open CofinalHistorySettlement
open CofinalHistorySettlementFace

noncomputable section

def runtimeJointShiftGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, role) => (stage + 1, role)

def runtimeJointShiftRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointShiftGenerator

@[simp] theorem runtimeJointMapDomainShift_atom
    (stage : Nat) (role : RuntimeJointRelationRole) :
    Finsupp.mapDomain runtimeJointShiftGenerator
        (runtimeJointRelationAtom stage role) =
      runtimeJointRelationAtom (stage + 1) role := by
  simp [runtimeJointRelationAtom, runtimeJointShiftGenerator]

@[simp] theorem runtimeJointShiftRelation_atom
    (stage : Nat) (role : RuntimeJointRelationRole) :
    runtimeJointShiftRelation (runtimeJointRelationAtom stage role) =
      runtimeJointRelationAtom (stage + 1) role := by
  simp [runtimeJointShiftRelation, runtimeJointRelationAtom,
    runtimeJointShiftGenerator]

@[simp] theorem runtimeJointShiftRelation_incidence
    (stage : Nat) :
    runtimeJointShiftRelation (runtimeJointIncidenceStageRelation stage) =
      runtimeJointIncidenceStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation, runtimeJointIncidenceStageRelation,
    Finsupp.mapDomain_sub]

@[simp] theorem runtimeJointShiftRelation_sourceBoundary
    (stage : Nat) :
    runtimeJointShiftRelation (runtimeJointSourceBoundaryStageRelation stage) =
      runtimeJointSourceBoundaryStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation, runtimeJointSourceBoundaryStageRelation,
    Finsupp.mapDomain_sub]

@[simp] theorem runtimeJointShiftRelation_quarterIncidence
    (stage : Nat) :
    runtimeJointShiftRelation (runtimeJointQuarterIncidenceStageRelation stage) =
      runtimeJointQuarterIncidenceStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation, runtimeJointQuarterIncidenceStageRelation,
    Finsupp.mapDomain_sub]

@[simp] theorem runtimeJointShiftRelation_quarterSourceBoundary
    (stage : Nat) :
    runtimeJointShiftRelation
        (runtimeJointQuarterSourceBoundaryStageRelation stage) =
      runtimeJointQuarterSourceBoundaryStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation,
    runtimeJointQuarterSourceBoundaryStageRelation,
    Finsupp.mapDomain_sub]

@[simp] theorem runtimeJointShiftRelation_quarterBoundaryEnergy
    (stage : Nat) :
    runtimeJointShiftRelation
        (runtimeJointQuarterBoundaryEnergyStageRelation stage) =
      runtimeJointQuarterBoundaryEnergyStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation,
    runtimeJointQuarterBoundaryEnergyStageRelation,
    Finsupp.mapDomain_sub]

@[simp] theorem runtimeJointShiftRelation_quarterBalance
    (stage : Nat) :
    runtimeJointShiftRelation (runtimeJointQuarterBalanceStageRelation stage) =
      runtimeJointQuarterBalanceStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation, runtimeJointQuarterBalanceStageRelation,
    Finsupp.mapDomain_sub]

@[simp] theorem runtimeJointShiftRelation_balance
    (stage : Nat) :
    runtimeJointShiftRelation (runtimeJointBalanceStageRelation stage) =
      runtimeJointBalanceStageRelation (stage + 1) := by
  simp [runtimeJointShiftRelation, runtimeJointBalanceStageRelation,
    Finsupp.mapDomain_sub]

/-- On the actual frontier family, the companion map recovers the joint
incidence relation from the three balance roles.  Its values on joint roles
make the map total but are never used as a frontier assumption. -/
def runtimeJointBalanceToIncidenceGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .evolvedSeed)
  | (stage, .retained) => (stage, .sourceActionSeed)
  | (stage, .centeredTrace) => (stage, .incidence)
  | generator => generator

def runtimeJointBalanceToIncidenceRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointBalanceToIncidenceGenerator

@[simp] theorem runtimeJointBalanceToIncidenceRelation_balance
    (stage : Nat) :
    runtimeJointBalanceToIncidenceRelation
        (runtimeJointBalanceStageRelation stage) =
      runtimeJointIncidenceStageRelation stage := by
  simp [runtimeJointBalanceToIncidenceRelation,
    runtimeJointBalanceStageRelation, runtimeJointIncidenceStageRelation,
    runtimeJointRelationAtom, runtimeJointBalanceToIncidenceGenerator,
    Finsupp.mapDomain_sub]

/-- The same balance frontier also recovers the before/after source-boundary
relation at that stage. -/
def runtimeJointBalanceToSourceBoundaryGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .sourceSeed)
  | (stage, .retained) => (stage, .sourceActionSeed)
  | (stage, .centeredTrace) => (stage, .sourceBoundary)
  | generator => generator

def runtimeJointBalanceToSourceBoundaryRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointBalanceToSourceBoundaryGenerator

@[simp] theorem runtimeJointBalanceToSourceBoundaryRelation_balance
    (stage : Nat) :
    runtimeJointBalanceToSourceBoundaryRelation
        (runtimeJointBalanceStageRelation stage) =
      runtimeJointSourceBoundaryStageRelation stage := by
  simp [runtimeJointBalanceToSourceBoundaryRelation,
    runtimeJointBalanceStageRelation, runtimeJointSourceBoundaryStageRelation,
    runtimeJointRelationAtom, runtimeJointBalanceToSourceBoundaryGenerator,
    Finsupp.mapDomain_sub]

/-- The balance frontier recovers the quarter-scale joint-incidence relation
without introducing a second occurrence or an external comparator. -/
def runtimeJointBalanceToQuarterIncidenceGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .quarterEvolvedSeed)
  | (stage, .retained) => (stage, .quarterSourceActionSeed)
  | (stage, .centeredTrace) => (stage, .quarterIncidence)
  | generator => generator

def runtimeJointBalanceToQuarterIncidenceRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointBalanceToQuarterIncidenceGenerator

@[simp] theorem runtimeJointBalanceToQuarterIncidenceRelation_balance
    (stage : Nat) :
    runtimeJointBalanceToQuarterIncidenceRelation
        (runtimeJointBalanceStageRelation stage) =
      runtimeJointQuarterIncidenceStageRelation stage := by
  simp [runtimeJointBalanceToQuarterIncidenceRelation,
    runtimeJointBalanceStageRelation, runtimeJointQuarterIncidenceStageRelation,
    runtimeJointRelationAtom, runtimeJointBalanceToQuarterIncidenceGenerator,
    Finsupp.mapDomain_sub]

/-- The same balance frontier recovers the quarter-scale source boundary. -/
def runtimeJointBalanceToQuarterSourceBoundaryGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .quarterSourceSeed)
  | (stage, .retained) => (stage, .quarterSourceActionSeed)
  | (stage, .centeredTrace) => (stage, .quarterSourceBoundary)
  | generator => generator

def runtimeJointBalanceToQuarterSourceBoundaryRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointBalanceToQuarterSourceBoundaryGenerator

@[simp] theorem runtimeJointBalanceToQuarterSourceBoundaryRelation_balance
    (stage : Nat) :
    runtimeJointBalanceToQuarterSourceBoundaryRelation
        (runtimeJointBalanceStageRelation stage) =
      runtimeJointQuarterSourceBoundaryStageRelation stage := by
  simp [runtimeJointBalanceToQuarterSourceBoundaryRelation,
    runtimeJointBalanceStageRelation,
    runtimeJointQuarterSourceBoundaryStageRelation,
    runtimeJointRelationAtom,
    runtimeJointBalanceToQuarterSourceBoundaryGenerator,
    Finsupp.mapDomain_sub]

/-- The same root frontier writes the canonical energy/remainder split of the
actual quarter boundary.  No spectral value is introduced by this map. -/
def runtimeJointBalanceToQuarterBoundaryEnergyGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .quarterSourceBoundary)
  | (stage, .retained) => (stage, .quarterBoundaryEnergy)
  | (stage, .centeredTrace) => (stage, .quarterBoundaryRemainder)
  | generator => generator

def runtimeJointBalanceToQuarterBoundaryEnergyRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointBalanceToQuarterBoundaryEnergyGenerator

@[simp] theorem runtimeJointBalanceToQuarterBoundaryEnergyRelation_balance
    (stage : Nat) :
    runtimeJointBalanceToQuarterBoundaryEnergyRelation
        (runtimeJointBalanceStageRelation stage) =
      runtimeJointQuarterBoundaryEnergyStageRelation stage := by
  simp [runtimeJointBalanceToQuarterBoundaryEnergyRelation,
    runtimeJointBalanceStageRelation,
    runtimeJointQuarterBoundaryEnergyStageRelation,
    runtimeJointRelationAtom,
    runtimeJointBalanceToQuarterBoundaryEnergyGenerator,
    Finsupp.mapDomain_sub]

/-- The root frontier also emits the already generated quarter-scale effect
conservation row. -/
def runtimeJointBalanceToQuarterBalanceGenerator :
    RuntimeJointRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .quarterPhase)
  | (stage, .retained) => (stage, .quarterRetained)
  | (stage, .centeredTrace) => (stage, .quarterCenteredTrace)
  | generator => generator

def runtimeJointBalanceToQuarterBalanceRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  relation.mapDomain runtimeJointBalanceToQuarterBalanceGenerator

@[simp] theorem runtimeJointBalanceToQuarterBalanceRelation_balance
    (stage : Nat) :
    runtimeJointBalanceToQuarterBalanceRelation
        (runtimeJointBalanceStageRelation stage) =
      runtimeJointQuarterBalanceStageRelation stage := by
  simp [runtimeJointBalanceToQuarterBalanceRelation,
    runtimeJointBalanceStageRelation, runtimeJointQuarterBalanceStageRelation,
    runtimeJointRelationAtom, runtimeJointBalanceToQuarterBalanceGenerator,
    Finsupp.mapDomain_sub]

def runtimeJointIncidencePresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointIncidenceStageRelation stage)

def runtimeJointSourceBoundaryPresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointSourceBoundaryStageRelation stage)

def runtimeJointQuarterIncidencePresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointQuarterIncidenceStageRelation stage)

def runtimeJointQuarterSourceBoundaryPresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointQuarterSourceBoundaryStageRelation stage)

def runtimeJointQuarterBoundaryEnergyPresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointQuarterBoundaryEnergyStageRelation stage)

def runtimeJointQuarterBalancePresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointQuarterBalanceStageRelation stage)

def runtimeJointBalancePresentedEvent (stage : Nat) :
    PresentedRelationEventAt RuntimeJointRelationGenerator :=
  .relation (runtimeJointBalanceStageRelation stage)

/-- One rooted stage: both scale faces are closed dependent writes and balance
is the only open frontier. -/
def runtimeJointRelationSeedAt (stage : Nat) :
    RootedAccountedUnfolding
      (PresentedRelationEventAt RuntimeJointRelationGenerator) :=
  .occur (runtimeJointIncidencePresentedEvent stage) <|
    AccountedBranches.singleton <|
      .occur (runtimeJointSourceBoundaryPresentedEvent stage) <|
        AccountedBranches.singleton <|
          .occur (runtimeJointQuarterIncidencePresentedEvent stage) <|
            AccountedBranches.singleton <|
              .occur (runtimeJointQuarterSourceBoundaryPresentedEvent stage) <|
                AccountedBranches.singleton <|
                  .occur (runtimeJointQuarterBoundaryEnergyPresentedEvent stage) <|
                    AccountedBranches.singleton <|
                      .occur (runtimeJointQuarterBalancePresentedEvent stage) <|
                        AccountedBranches.singleton <|
                          RootedAccountedUnfolding.zero
                            (runtimeJointBalancePresentedEvent stage)

@[simp] theorem runtimeJointRelationSeedAt_root (stage : Nat) :
    (runtimeJointRelationSeedAt stage).root =
      runtimeJointIncidencePresentedEvent stage :=
  rfl

@[simp] theorem runtimeJointRelationSeedAt_frontier (stage : Nat) :
    (runtimeJointRelationSeedAt stage).frontier =
      [runtimeJointBalancePresentedEvent stage] :=
  rfl

@[simp] theorem runtimeJointRelationSeedAt_trace (stage : Nat) :
    (runtimeJointRelationSeedAt stage).trace =
      [runtimeJointIncidencePresentedEvent stage,
        runtimeJointSourceBoundaryPresentedEvent stage,
        runtimeJointQuarterIncidencePresentedEvent stage,
        runtimeJointQuarterSourceBoundaryPresentedEvent stage,
        runtimeJointQuarterBoundaryEnergyPresentedEvent stage,
        runtimeJointQuarterBalancePresentedEvent stage,
        runtimeJointBalancePresentedEvent stage] :=
  rfl

/-- The only actual frontier case produces all six dependent relation faces
at the next stage and leaves the next balance relation open. -/
def runtimeJointShiftContinuationAt :
    PresentedRelationEventAt RuntimeJointRelationGenerator →
      RootedAccountedUnfolding
        (PresentedRelationEventAt RuntimeJointRelationGenerator)
  | .generator generator =>
      RootedAccountedUnfolding.zero
        (.generator (runtimeJointShiftGenerator generator))
  | .relation relation =>
      let shifted := runtimeJointShiftRelation relation
      .occur (.relation
          (runtimeJointBalanceToIncidenceRelation shifted)) <|
        AccountedBranches.singleton <|
          .occur (.relation
              (runtimeJointBalanceToSourceBoundaryRelation shifted)) <|
            AccountedBranches.singleton <|
              .occur (.relation
                  (runtimeJointBalanceToQuarterIncidenceRelation shifted)) <|
                AccountedBranches.singleton <|
                  .occur (.relation
                      (runtimeJointBalanceToQuarterSourceBoundaryRelation shifted)) <|
                    AccountedBranches.singleton <|
                      .occur (.relation
                          (runtimeJointBalanceToQuarterBoundaryEnergyRelation shifted)) <|
                        AccountedBranches.singleton <|
                          .occur (.relation
                              (runtimeJointBalanceToQuarterBalanceRelation shifted)) <|
                            AccountedBranches.singleton <|
                              RootedAccountedUnfolding.zero (.relation shifted)

def runtimeJointRelationContinuation :
    RootedAccountedUnfolding
      (PresentedRelationEventAt RuntimeJointRelationGenerator →
        RootedAccountedUnfolding
          (PresentedRelationEventAt RuntimeJointRelationGenerator)) :=
  RootedAccountedUnfolding.zero runtimeJointShiftContinuationAt

@[simp] theorem runtimeJointShiftContinuationAt_balance
    (stage : Nat) :
    runtimeJointShiftContinuationAt
        (runtimeJointBalancePresentedEvent stage) =
      runtimeJointRelationSeedAt (stage + 1) := by
  simp [runtimeJointShiftContinuationAt, runtimeJointRelationSeedAt,
    runtimeJointBalancePresentedEvent,
    runtimeJointIncidencePresentedEvent,
    runtimeJointSourceBoundaryPresentedEvent,
    runtimeJointQuarterIncidencePresentedEvent,
    runtimeJointQuarterSourceBoundaryPresentedEvent,
    runtimeJointQuarterBoundaryEnergyPresentedEvent,
    runtimeJointQuarterBalancePresentedEvent]

@[simp] theorem runtimeJointShiftContinuationAt_balance_frontier
    (stage : Nat) :
    (runtimeJointShiftContinuationAt
      (runtimeJointBalancePresentedEvent stage)).frontier =
        [runtimeJointBalancePresentedEvent (stage + 1)] := by
  rw [runtimeJointShiftContinuationAt_balance,
    runtimeJointRelationSeedAt_frontier]

@[simp] theorem runtimeJointShiftContinuationAt_balance_trace
    (stage : Nat) :
    (runtimeJointShiftContinuationAt
      (runtimeJointBalancePresentedEvent stage)).trace =
        [runtimeJointIncidencePresentedEvent (stage + 1),
          runtimeJointSourceBoundaryPresentedEvent (stage + 1),
          runtimeJointQuarterIncidencePresentedEvent (stage + 1),
          runtimeJointQuarterSourceBoundaryPresentedEvent (stage + 1),
          runtimeJointQuarterBoundaryEnergyPresentedEvent (stage + 1),
          runtimeJointQuarterBalancePresentedEvent (stage + 1),
          runtimeJointBalancePresentedEvent (stage + 1)] := by
  rw [runtimeJointShiftContinuationAt_balance,
    runtimeJointRelationSeedAt_trace]

abbrev runtimeJointRelationMaterialLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalHistoryMaterialLaw
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource :=
  SourceNativeCofinalHistoryMaterialLaw.create
    RuntimeJointRelationGenerator
    (fun occurrence => RootedAccountedUnfolding.zero occurrence)
    (fun _occurrence => rfl)
    (fun {current} _occurrence =>
      runtimeJointRelationSeedAt (currentEffectStage current))
    (fun _occurrence => runtimeJointRelationContinuation)

@[simp] theorem runtimeJointRelationMaterialLaw_seed_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    ((runtimeJointRelationMaterialLaw observation nontrivial).seedAt
      occurrence).root =
        runtimeJointIncidencePresentedEvent (currentEffectStage current) :=
  rfl

def runtimeJointRelationEvaluatorOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding
      (RuntimeJointRelationGenerator → PairedOmegaJointRelationCarrier) :=
  RootedAccountedUnfolding.zero
    (runtimeJointRelationGeneratorValue observation nontrivial)

abbrev runtimeJointFaithfulMaterialLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalFaithfulMaterialLaw
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource
      PairedOmegaJointRelationCarrier :=
  SourceNativeCofinalFaithfulMaterialLaw.create
    (runtimeJointRelationMaterialLaw observation nontrivial)
    (fun _occurrence =>
      runtimeJointRelationEvaluatorOccurrence observation nontrivial)

@[simp] theorem runtimeJointFaithfulMaterialLaw_evaluator_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    ((runtimeJointFaithfulMaterialLaw observation nontrivial).evaluatorAt
      occurrence).root =
        runtimeJointRelationGeneratorValue observation nontrivial :=
  rfl

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
