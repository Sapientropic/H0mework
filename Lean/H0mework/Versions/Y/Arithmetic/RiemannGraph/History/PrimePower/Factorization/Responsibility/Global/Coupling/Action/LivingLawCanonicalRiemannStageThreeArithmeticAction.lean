import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Perfectification.Character.LivingLawCanonicalRiemannReceiptStageThreeArithmeticCharacter
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleOrbitCoupling
import H0mework.Versions.Y.Arithmetic.RiemannGraph.SourceCharacterJointAction

/-!
# Stage-three arithmetic action on the common factorization carrier

The actual stage-three Euler operator generates a coinvariant action on its
integral relation cokernel.  The source-owned rational-circle character is
invariant under that action and remains nonzero on the endpoint class.

The same `PrimeExponentFactorizationCarrier` already used by the all-place
pole source now generates this arithmetic orbit.  No finite complexification,
Mellin equality, separator, fixedness, or vanishing premise enters.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation
namespace Arithmetic.Character.CommonAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedFaithfulIntegralFace
open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open MuntzGraph.Conductor.History.PrimePowerCurrent
open ReceiptRelation.Arithmetic
open ReceiptRelation.Arithmetic.Character
open ReceiptRelation.Cofinal
open AllPlace.WeilQuadratic.Occurrence
open NoIslandNoMagic.CanonicalArithmeticState.BlockArithmeticSpecializationEndpoint
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead

noncomputable section

theorem stageThreeBoundaryPhase_relationEulerAction
    (value : WholeRelationModule seedOccurrence.root 3) :
    stageThreeBoundaryPhase
        (relationEulerAction seedOccurrence.root 3 value) =
      stageThreeBoundaryPhase value := by
  have killed := stageThreeBoundaryPhase_operator_zero value
  unfold integralRelationEulerOperator at killed
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_eq_zero] at killed
  exact killed.symm

theorem integralRelationOperatorRange_euler_stable (stage : Nat) :
    LinearMap.range (integralRelationEulerOperator stage) ≤
      (LinearMap.range (integralRelationEulerOperator stage)).comap
        (relationEulerAction seedOccurrence.root stage) := by
  rintro _ ⟨value, rfl⟩
  refine ⟨relationEulerAction seedOccurrence.root stage value, ?_⟩
  unfold integralRelationEulerOperator
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]

def integralRelationEulerCokernelAction (stage : Nat) :
    IntegralRelationOperatorCokernel stage →ₗ[ℤ]
      IntegralRelationOperatorCokernel stage :=
  Submodule.mapQ
    (LinearMap.range (integralRelationEulerOperator stage))
    (LinearMap.range (integralRelationEulerOperator stage))
    (relationEulerAction seedOccurrence.root stage)
    (integralRelationOperatorRange_euler_stable stage)

theorem integralRelationEulerCokernelAction_eq_id (stage : Nat) :
    integralRelationEulerCokernelAction stage = LinearMap.id := by
  apply LinearMap.ext
  intro quotient
  refine Submodule.Quotient.induction_on _ quotient ?_
  intro value
  apply (Submodule.Quotient.eq _).2
  change relationEulerAction seedOccurrence.root stage value - value ∈
    LinearMap.range (integralRelationEulerOperator stage)
  refine ⟨-value, ?_⟩
  unfold integralRelationEulerOperator
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_neg]
  module

theorem stageThreeEndpointCharacter_action_invariant
    (value : IntegralRelationOperatorCokernel 3) :
    stageThreeEndpointCharacter
        (integralRelationEulerCokernelAction 3 value) =
      stageThreeEndpointCharacter value := by
  rw [integralRelationEulerCokernelAction_eq_id]
  rfl

abbrev PrimeExponentGroup := Multiplicative PrimeExponentLattice

def factorizationGroupEquiv :
    PrimeExponentFactorizationCarrier ≃ₗ[ℤ] Carrier PrimeExponentGroup :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv
    ℤ ℤ PrimeExponentLattice).toLinearEquiv

def factorizationLeftTranslation (exponent : PrimeExponentGroup) :
    PrimeExponentFactorizationCarrier ≃ₗ[ℤ]
      PrimeExponentFactorizationCarrier :=
  (factorizationGroupEquiv.trans (leftTranslation exponent)).trans
    factorizationGroupEquiv.symm

@[simp] theorem factorizationGroupEquiv_leftTranslation
    (exponent : PrimeExponentGroup)
    (value : PrimeExponentFactorizationCarrier) :
    factorizationGroupEquiv (factorizationLeftTranslation exponent value) =
      leftTranslation exponent (factorizationGroupEquiv value) := by
  simp [factorizationLeftTranslation]

def stageThreeArithmeticRepresentation :
    PrimeExponentGroup →* Module.End ℤ (IntegralRelationOperatorCokernel 3) where
  toFun := fun _ => integralRelationEulerCokernelAction 3
  map_one' := integralRelationEulerCokernelAction_eq_id 3
  map_mul' := by
    intro left right
    rw [integralRelationEulerCokernelAction_eq_id]
    rfl

def stageThreeArithmeticOrbit :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      IntegralRelationOperatorCokernel 3 :=
  (orbitRealization stageThreeArithmeticRepresentation
    (specializedIntegralEndpointBoundaryClass 3)).comp
      factorizationGroupEquiv.toLinearMap

def stageThreeArithmeticMeasurement :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] AddCircle (1 : ℚ) :=
  stageThreeEndpointCharacter.toIntLinearMap.comp stageThreeArithmeticOrbit

theorem stageThreeArithmeticMeasurement_base_ne_zero :
    stageThreeArithmeticMeasurement
        (AddMonoidAlgebra.single 0 1) ≠ 0 := by
  change stageThreeEndpointCharacter
      (orbitRealization stageThreeArithmeticRepresentation
        (specializedIntegralEndpointBoundaryClass 3)
        (factorizationGroupEquiv (AddMonoidAlgebra.single 0 1))) ≠ 0
  rw [show factorizationGroupEquiv (AddMonoidAlgebra.single 0 1) =
      delta (1 : PrimeExponentGroup) by
    simp [factorizationGroupEquiv, delta]]
  rw [orbitRealization_delta]
  change stageThreeEndpointCharacter
      (integralRelationEulerCokernelAction 3
        (specializedIntegralEndpointBoundaryClass 3)) ≠ 0
  rw [integralRelationEulerCokernelAction_eq_id, LinearMap.id_apply]
  exact stageThreeEndpointCharacter_endpoint_ne_zero

theorem stageThreeArithmeticMeasurement_left_covariance
    (exponent : PrimeExponentGroup)
    (value : PrimeExponentFactorizationCarrier) :
    stageThreeArithmeticMeasurement
        (factorizationLeftTranslation exponent value) =
      stageThreeArithmeticMeasurement value := by
  have covariance := LinearMap.congr_fun
    (orbitRealization_left_covariance stageThreeArithmeticRepresentation
      (specializedIntegralEndpointBoundaryClass 3) exponent)
      (factorizationGroupEquiv value)
  simp only [LinearMap.comp_apply] at covariance
  change stageThreeEndpointCharacter
      (orbitRealization stageThreeArithmeticRepresentation
        (specializedIntegralEndpointBoundaryClass 3)
          (factorizationGroupEquiv
            (factorizationLeftTranslation exponent value))) = _
  rw [factorizationGroupEquiv_leftTranslation]
  exact (congrArg stageThreeEndpointCharacter covariance).trans
    (stageThreeEndpointCharacter_action_invariant _)

end
end Arithmetic.Character.CommonAction
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
