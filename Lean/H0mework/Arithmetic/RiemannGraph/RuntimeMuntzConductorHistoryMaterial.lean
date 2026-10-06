import H0mework.Realization.Completion.FaithfulInstallation
import H0mework.Arithmetic.PrimeLeakage.AllPlaceWeilRuntimeRoot
import H0mework.Arithmetic.RiemannGraph.RuntimeMuntzConductorSuccessorRelation

/-!
# Source-installed conductor history material

The exact all-place runtime occurrence now generates both the rooted
conductor-successor history and its full function-valued evaluator.  This is
domain activation of the generic cofinal engine, not a new arithmetic root
or a submitted finite table.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open CofinalFaithfulSettlementFace
open CofinalHistorySettlementFace
open Material

noncomputable section

abbrev runtimeConductorHistoryMaterialLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalHistoryMaterialLaw
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource :=
  SourceNativeCofinalHistoryMaterialLaw.create
    ConductorHistoryGenerator
    (fun occurrence => RootedAccountedUnfolding.zero occurrence)
    (fun _occurrence => rfl)
    (fun _occurrence => conductorHistorySeedAt 0)
    (fun _occurrence => conductorHistoryContinuation)

@[simp] theorem runtimeConductorHistoryMaterialLaw_seed_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt
          current) :
    ((runtimeConductorHistoryMaterialLaw observation nontrivial).seedAt
      occurrence).root = conductorSuccessorPresentedEvent 0 :=
  rfl

def runtimeConductorHistoryEvaluatorOccurrenceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt
          current) :
    RootedAccountedUnfolding
      (ConductorHistoryGenerator → ConductorHistoryCarrier) :=
  RootedAccountedUnfolding.zero <|
    conductorHistoryGeneratorValue
      (generateRuntimeAllPlaceWeilFace observation nontrivial occurrence)

abbrev runtimeConductorFaithfulMaterialLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalFaithfulMaterialLaw
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource
      ConductorHistoryCarrier :=
  SourceNativeCofinalFaithfulMaterialLaw.create
    (runtimeConductorHistoryMaterialLaw observation nontrivial)
    (runtimeConductorHistoryEvaluatorOccurrenceAt observation nontrivial)

@[simp] theorem runtimeConductorFaithfulMaterialLaw_evaluator_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt
          current) :
    ((runtimeConductorFaithfulMaterialLaw observation nontrivial).evaluatorAt
      occurrence).root =
        conductorHistoryGeneratorValue
          (generateRuntimeAllPlaceWeilFace
            observation nontrivial occurrence) :=
  rfl

end
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
