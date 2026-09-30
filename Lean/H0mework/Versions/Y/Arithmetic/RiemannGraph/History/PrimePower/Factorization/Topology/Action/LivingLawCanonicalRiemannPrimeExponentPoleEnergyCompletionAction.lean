import H0mework.Realization.Coherent.LivingLawRootGeneratedIntegralCoherentCovarianceEquivKernel
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleEnergyCoimage
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Coupling.Action.LivingLawCanonicalRiemannStageThreeArithmeticMellinCommonAction

/-!
# Source-generated prime-exponent energy completion action

The same factorization carrier that owns the arithmetic and Mellin reads now
generates the completion of its positive-energy face.  Every prime-exponent
translation acts by the actual logarithmic energy translation, and the
invertible source action generates an isometric equivalence on the completed
range.  No bounded Mellin extension, support, criticality, or neutrality is
assumed.
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

open AllPlaceOriginDefect.Orbit
open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedIntegralCoherentCovariance
open ReceiptRelation.Arithmetic.Character.CommonAction

noncomputable section

abbrev SelectedCompletion
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  CoherentCompletion
    (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial)

abbrev ReversalCompletion
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  CoherentCompletion
    (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial)

/-- The algebraic selected energy coimage embeds faithfully and densely into
its source-generated completion. -/
def selectedCoimageToCompletion
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SelectedPrimeExponentPoleEnergyCoimage observation nontrivial →ₗ[ℂ]
      SelectedCompletion observation nontrivial :=
  carrierToHilbertAmbient
    (complexifiedFeature
      (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial))

def reversalCoimageToCompletion
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReversalPrimeExponentPoleEnergyCoimage observation nontrivial →ₗ[ℂ]
      ReversalCompletion observation nontrivial :=
  carrierToHilbertAmbient
    (complexifiedFeature
      (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial))

theorem selectedCoimageToCompletion_injective
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Function.Injective
      (selectedCoimageToCompletion observation nontrivial) :=
  carrierToHilbertAmbient_injective _

theorem reversalCoimageToCompletion_injective
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Function.Injective
      (reversalCoimageToCompletion observation nontrivial) :=
  carrierToHilbertAmbient_injective _

theorem selectedCoimageToCompletion_denseRange
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    DenseRange (selectedCoimageToCompletion observation nontrivial) :=
  carrierToHilbertAmbient_denseRange _

theorem reversalCoimageToCompletion_denseRange
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    DenseRange (reversalCoimageToCompletion observation nontrivial) :=
  carrierToHilbertAmbient_denseRange _

theorem factorizationLeftTranslation_single_one
    (exponent : PrimeExponentGroup) (basis : PrimeExponentLattice) :
    factorizationLeftTranslation exponent
        (AddMonoidAlgebra.single basis 1) =
      AddMonoidAlgebra.single
        (Multiplicative.toAdd exponent + basis) 1 := by
  apply factorizationGroupEquiv.injective
  rw [factorizationGroupEquiv_leftTranslation]
  rw [show factorizationGroupEquiv
      (AddMonoidAlgebra.single basis 1) =
        delta (Multiplicative.ofAdd basis) by
      simp [factorizationGroupEquiv, delta]]
  rw [leftTranslation_delta]
  rw [show factorizationGroupEquiv
      (AddMonoidAlgebra.single
        (Multiplicative.toAdd exponent + basis) 1) =
        delta (exponent * Multiplicative.ofAdd basis) by
      simp [factorizationGroupEquiv, delta]]

/-- The actual source transition and its actual energy translation are both
equivalences; no inverse data is supplied separately. -/
def primeExponentEnergyActionData
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z)
    (exponent : PrimeExponentGroup) :
    EquivActionData (primeExponentPolePositiveEnergyMap z pole) where
  integralTransition := factorizationLeftTranslation exponent
  hilbertEvolution := positiveMellinQuarterEnergyTranslationIsometry
    (Real.log (scaleSquare
      (primeExponentScale (Multiplicative.toAdd exponent))))

theorem primeExponentEnergyActionData_covariant
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (pole : AllPlaceOriginOrbitJointCarrier z)
    (exponent : PrimeExponentGroup)
    (event : PrimeExponentFactorizationCarrier) :
    couplingResidual
        (primeExponentEnergyActionData z pole exponent).toActionData event = 0 := by
  rw [couplingResidual_eq_zero_iff]
  have square :
      ((((primeExponentEnergyActionData z pole exponent).hilbertEvolution
        ).toLinearEquiv.toLinearMap.restrictScalars ℤ).comp
          (primeExponentPolePositiveEnergyMap z pole)) =
        (primeExponentPolePositiveEnergyMap z pole).comp
          (factorizationLeftTranslation exponent).toLinearMap := by
    apply AddMonoidAlgebra.lhom_ext'
    intro basis
    apply LinearMap.ext
    intro coefficient
    simp only [LinearMap.comp_apply, AddMonoidAlgebra.lsingle_apply]
    rw [show AddMonoidAlgebra.single basis coefficient =
        coefficient • AddMonoidAlgebra.single basis 1 by simp]
    simp only [map_smul]
    apply congrArg
      (fun value : PositiveMellinQuarterEnergy => coefficient • value)
    change positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare
          (primeExponentScale (Multiplicative.toAdd exponent))))
        (primeExponentPolePositiveEnergyMap z pole
          (AddMonoidAlgebra.single basis 1)) =
      primeExponentPolePositiveEnergyMap z pole
        (factorizationLeftTranslation exponent
          (AddMonoidAlgebra.single basis 1))
    rw [primeExponentPolePositiveEnergyMap_single z positiveZ belowHalf,
      factorizationLeftTranslation_single_one,
      primeExponentPolePositiveEnergyMap_single z positiveZ belowHalf]
    have composition := LinearMap.congr_fun
      (positiveMellinQuarterEnergyTranslation_comp
        (Real.log (scaleSquare
          (primeExponentScale (Multiplicative.toAdd exponent))))
        (Real.log (scaleSquare (primeExponentScale basis))))
      (allPlaceOrbitPositiveEnergyMap z pole)
    change positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare
          (primeExponentScale (Multiplicative.toAdd exponent))))
        (positiveMellinQuarterEnergyTranslation
          (Real.log (scaleSquare (primeExponentScale basis)))
          (allPlaceOrbitPositiveEnergyMap z pole)) =
      positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare (primeExponentScale basis)) +
          Real.log (scaleSquare
            (primeExponentScale (Multiplicative.toAdd exponent))))
        (allPlaceOrbitPositiveEnergyMap z pole) at composition
    change positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare
          (primeExponentScale (Multiplicative.toAdd exponent))))
        (positiveMellinQuarterEnergyTranslation
          (Real.log (scaleSquare (primeExponentScale basis)))
          (allPlaceOrbitPositiveEnergyMap z pole)) =
      positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare
          (primeExponentScale
            (Multiplicative.toAdd exponent + basis))))
        (allPlaceOrbitPositiveEnergyMap z pole)
    rw [composition, primeExponentScale_add, log_scaleSquare_mul, add_comm]
  exact LinearMap.congr_fun square event

def selectedStageThreeEnergyActionData
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    EquivActionData
      (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial) :=
  primeExponentEnergyActionData
    (selectedCoPoissonMuntzParameter observation)
    (selectedAllPlacePoleOrbitJointValue observation nontrivial)
    stageThreePrimeExponent

def reversalStageThreeEnergyActionData
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    EquivActionData
      (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial) :=
  primeExponentEnergyActionData
    (reversalCoPoissonMuntzParameter observation)
    (reversalAllPlacePoleOrbitJointValue observation nontrivial)
    stageThreePrimeExponent

theorem selectedStageThreeEnergyActionData_covariant
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : PrimeExponentFactorizationCarrier) :
    couplingResidual
        (selectedStageThreeEnergyActionData observation nontrivial).toActionData
        event = 0 :=
  primeExponentEnergyActionData_covariant
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (selectedAllPlacePoleOrbitJointValue observation nontrivial)
    stageThreePrimeExponent event

theorem reversalStageThreeEnergyActionData_covariant
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : PrimeExponentFactorizationCarrier) :
    couplingResidual
        (reversalStageThreeEnergyActionData observation nontrivial).toActionData
        event = 0 :=
  primeExponentEnergyActionData_covariant
    (reversalCoPoissonMuntzParameter observation)
    (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
    (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (reversalAllPlacePoleOrbitJointValue observation nontrivial)
    stageThreePrimeExponent event

/-- Actual stage-three isometric equivalences on the two generated energy
completions. -/
def selectedStageThreeCompletionAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SelectedCompletion observation nontrivial ≃ₗᵢ[ℂ]
      SelectedCompletion observation nontrivial :=
  coherentCompletionActionEquiv
    (selectedStageThreeEnergyActionData observation nontrivial)
    (selectedStageThreeEnergyActionData_covariant observation nontrivial)

def reversalStageThreeCompletionAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReversalCompletion observation nontrivial ≃ₗᵢ[ℂ]
      ReversalCompletion observation nontrivial :=
  coherentCompletionActionEquiv
    (reversalStageThreeEnergyActionData observation nontrivial)
    (reversalStageThreeEnergyActionData_covariant observation nontrivial)

@[simp] theorem selectedStageThreeCompletionAction_discrete_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : PrimeExponentFactorizationCarrier) :
    selectedStageThreeCompletionAction observation nontrivial
        (discreteToCoherentCompletion
          (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial)
          event) =
      discreteToCoherentCompletion
        (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial)
        (factorizationLeftTranslation stageThreePrimeExponent event) := by
  exact coherentCompletionActionEquiv_discrete_source
    (selectedStageThreeEnergyActionData observation nontrivial)
    (selectedStageThreeEnergyActionData_covariant observation nontrivial)
    event

@[simp] theorem reversalStageThreeCompletionAction_discrete_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : PrimeExponentFactorizationCarrier) :
    reversalStageThreeCompletionAction observation nontrivial
        (discreteToCoherentCompletion
          (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial)
          event) =
      discreteToCoherentCompletion
        (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial)
        (factorizationLeftTranslation stageThreePrimeExponent event) := by
  exact coherentCompletionActionEquiv_discrete_source
    (reversalStageThreeEnergyActionData observation nontrivial)
    (reversalStageThreeEnergyActionData_covariant observation nontrivial)
    event

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
