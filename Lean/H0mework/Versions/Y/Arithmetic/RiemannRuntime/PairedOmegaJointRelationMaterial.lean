import H0mework.Versions.Y.Arithmetic.RiemannRuntime.ClozelPairedOmegaJointRelationRawAction
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaEffectFaithfulRoot

/-! Install the existing raw joint history and evaluator in the fixed joint root. -/

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
