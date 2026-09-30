import H0mework.Realization.Coherent.LivingLawRootGeneratedIntegralCoherentCovarianceCoimageKernel
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Topology.Action.LivingLawCanonicalRiemannPrimeExponentPoleEnergyCompletionAction

/-!
# Algebraic Mellin action on the generated energy coimage

The source-generated completion action has an algebraic sibling on the
faithful energy coimage.  The existing Mellin factor descends through that
same quotient and satisfies the actual prime-three character law.  The
coimage and completion actions commute strictly; no continuous Mellin
extension is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

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
namespace PrimePowerCurrent
namespace EnergyCompletion

open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentCovariance
open ReceiptRelation.Arithmetic.Character.CommonAction

noncomputable section

def selectedStageThreeEnergyCoimageAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SelectedPrimeExponentPoleEnergyCoimage observation nontrivial →ₗ[ℂ]
      SelectedPrimeExponentPoleEnergyCoimage observation nontrivial :=
  coherentCoimageAction
    (selectedStageThreeEnergyActionData observation nontrivial).toActionData
    (selectedStageThreeEnergyActionData_covariant observation nontrivial)

def reversalStageThreeEnergyCoimageAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReversalPrimeExponentPoleEnergyCoimage observation nontrivial →ₗ[ℂ]
      ReversalPrimeExponentPoleEnergyCoimage observation nontrivial :=
  coherentCoimageAction
    (reversalStageThreeEnergyActionData observation nontrivial).toActionData
    (reversalStageThreeEnergyActionData_covariant observation nontrivial)

@[simp] theorem selectedStageThreeEnergyCoimageAction_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedStageThreeEnergyCoimageAction observation nontrivial).comp
        (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial) =
      (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial).comp
        (complexifiedTransition
          (selectedStageThreeEnergyActionData observation nontrivial
            ).toActionData) :=
  coherentCoimageAction_canonicalMap
    (selectedStageThreeEnergyActionData observation nontrivial).toActionData
    (selectedStageThreeEnergyActionData_covariant observation nontrivial)

@[simp] theorem reversalStageThreeEnergyCoimageAction_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalStageThreeEnergyCoimageAction observation nontrivial).comp
        (reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial) =
      (reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial).comp
        (complexifiedTransition
          (reversalStageThreeEnergyActionData observation nontrivial
            ).toActionData) :=
  coherentCoimageAction_canonicalMap
    (reversalStageThreeEnergyActionData observation nontrivial).toActionData
    (reversalStageThreeEnergyActionData_covariant observation nontrivial)

def selectedStageThreeMellinCharacter
    (observation : GeneratedRiemannZeroObservation) : ℂ :=
  primeExponentMellinCharacter
    (selectedCoPoissonMuntzParameter observation) stageThreePrimeExponent

def reversalStageThreeMellinCharacter
    (observation : GeneratedRiemannZeroObservation) : ℂ :=
  primeExponentMellinCharacter
    (reversalCoPoissonMuntzParameter observation) stageThreePrimeExponent

theorem selectedStageThreeMellin_integral_eigenlaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : PrimeExponentFactorizationCarrier) :
    selectedPrimeExponentPoleMellinMap observation nontrivial
        (factorizationLeftTranslation stageThreePrimeExponent event) =
      selectedStageThreeMellinCharacter observation *
        selectedPrimeExponentPoleMellinMap observation nontrivial event := by
  rw [selectedPrimeExponentPoleMellinMap_eq_characterEvaluation]
  change characterEvaluation _
      (factorizationGroupEquiv
        (factorizationLeftTranslation stageThreePrimeExponent event)) = _
  rw [factorizationGroupEquiv_leftTranslation]
  exact characterEvaluation_left_covariance _ _ _

theorem reversalStageThreeMellin_integral_eigenlaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : PrimeExponentFactorizationCarrier) :
    reversalPrimeExponentPoleMellinMap observation nontrivial
        (factorizationLeftTranslation stageThreePrimeExponent event) =
      reversalStageThreeMellinCharacter observation *
        reversalPrimeExponentPoleMellinMap observation nontrivial event := by
  rw [reversalPrimeExponentPoleMellinMap_eq_characterEvaluation]
  change characterEvaluation _
      (factorizationGroupEquiv
        (factorizationLeftTranslation stageThreePrimeExponent event)) = _
  rw [factorizationGroupEquiv_leftTranslation]
  exact characterEvaluation_left_covariance _ _ _

/-- The installed algebraic Mellin factor is an eigenmeasurement of the
actual selected coimage action. -/
theorem selectedStageThreeEnergyMellinFactor_eigenlaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedPrimeExponentPoleEnergyMellinFactor observation nontrivial).comp
        (selectedStageThreeEnergyCoimageAction observation nontrivial) =
      selectedStageThreeMellinCharacter observation •
        selectedPrimeExponentPoleEnergyMellinFactor observation nontrivial :=
  coherentCoimageFactor_eigenlaw
    (selectedStageThreeEnergyActionData observation nontrivial).toActionData
    (selectedStageThreeEnergyActionData_covariant observation nontrivial)
    (selectedPrimeExponentPoleMellinMap observation nontrivial)
    (selectedStageThreeMellinCharacter observation)
    (selectedPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial)
    (selectedStageThreeMellin_integral_eigenlaw observation nontrivial)

theorem reversalStageThreeEnergyMellinFactor_eigenlaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalPrimeExponentPoleEnergyMellinFactor observation nontrivial).comp
        (reversalStageThreeEnergyCoimageAction observation nontrivial) =
      reversalStageThreeMellinCharacter observation •
        reversalPrimeExponentPoleEnergyMellinFactor observation nontrivial :=
  coherentCoimageFactor_eigenlaw
    (reversalStageThreeEnergyActionData observation nontrivial).toActionData
    (reversalStageThreeEnergyActionData_covariant observation nontrivial)
    (reversalPrimeExponentPoleMellinMap observation nontrivial)
    (reversalStageThreeMellinCharacter observation)
    (reversalPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial)
    (reversalStageThreeMellin_integral_eigenlaw observation nontrivial)

/-- Algebraic and completed selected actions are projections of the same
source transition. -/
theorem selectedStageThreeEnergyCoimage_completion_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedStageThreeCompletionAction observation nontrivial).toLinearMap.comp
        (selectedCoimageToCompletion observation nontrivial) =
      (selectedCoimageToCompletion observation nontrivial).comp
        (selectedStageThreeEnergyCoimageAction observation nontrivial) :=
  coherentCompletionAction_coimage
    (selectedStageThreeEnergyActionData observation nontrivial).toActionData
    (selectedStageThreeEnergyActionData_covariant observation nontrivial)

theorem reversalStageThreeEnergyCoimage_completion_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalStageThreeCompletionAction observation nontrivial).toLinearMap.comp
        (reversalCoimageToCompletion observation nontrivial) =
      (reversalCoimageToCompletion observation nontrivial).comp
        (reversalStageThreeEnergyCoimageAction observation nontrivial) :=
  coherentCompletionAction_coimage
    (reversalStageThreeEnergyActionData observation nontrivial).toActionData
    (reversalStageThreeEnergyActionData_covariant observation nontrivial)

end

end EnergyCompletion
end PrimePowerCurrent
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
