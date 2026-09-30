import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Coupling.Action.LivingLawCanonicalRiemannStageThreeArithmeticAction

/-!
# Common arithmetic--Mellin action at the actual prime-three generator

One left translation of the existing prime-exponent factorization carrier
now has three sibling measurements: the source-owned stage-three AddCircle
phase and the selected/reversal all-place Mellin characters.  Their product
measurement commutes with the same action, and the installed character
occurrence projects back to the existing zero-owned joint state.

The authoritative public square is the generator supplied by the actual
stage-three prime row.  The all-exponent square is an algebraic mechanism;
it does not claim that unrelated prime Euler actions live in the stage-three
coordinate.  No cross-coordinate equality or neutrality is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation
namespace Arithmetic.Character.CommonAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
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
open AllPlace.ActionCofiber.RawEffect
open NoIslandNoMagic.CanonicalArithmeticState.BlockArithmeticSpecializationEndpoint
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence

noncomputable section

def primeExponentMellinCharacter (z : ℂ) : PrimeExponentGroup →* ℂ where
  toFun := fun exponent =>
    quarterDilationCharacter z
      (scaleSquare (primeExponentScale (Multiplicative.toAdd exponent)))
  map_one' := by
    simp [quarterDilationCharacter, scaleSquare, scaleValue]
  map_mul' := by
    intro left right
    change quarterDilationCharacter z
        (scaleSquare (primeExponentScale
          (Multiplicative.toAdd left + Multiplicative.toAdd right))) = _
    rw [primeExponentScale_add,
      quarterDilationCharacter_scaleSquare_mul]

def primeExponentCharacterEvaluation (character : PrimeExponentGroup →* ℂ) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  (characterEvaluation character).comp factorizationGroupEquiv.toLinearMap

@[simp] theorem primeExponentCharacterEvaluation_single
    (z : ℂ) (exponent : PrimeExponentLattice) :
    primeExponentCharacterEvaluation (primeExponentMellinCharacter z)
        (AddMonoidAlgebra.single exponent 1) =
      quarterDilationCharacter z
        (scaleSquare (primeExponentScale exponent)) := by
  change characterEvaluation (primeExponentMellinCharacter z)
      (factorizationGroupEquiv
        (AddMonoidAlgebra.single exponent 1)) = _
  rw [show factorizationGroupEquiv
      (AddMonoidAlgebra.single exponent 1) =
        delta (Multiplicative.ofAdd exponent) by
      simp [factorizationGroupEquiv, delta]]
  rw [characterEvaluation_delta]
  rfl

theorem selectedPrimeExponentPoleMellinMap_eq_characterEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleMellinMap observation nontrivial =
      primeExponentCharacterEvaluation
        (primeExponentMellinCharacter
          (selectedCoPoissonMuntzParameter observation)) := by
  apply AddMonoidAlgebra.lhom_ext'
  intro exponent
  apply LinearMap.ext
  intro coefficient
  change selectedPrimeExponentPoleMellinMap observation nontrivial
      (AddMonoidAlgebra.single exponent coefficient) =
    primeExponentCharacterEvaluation
      (primeExponentMellinCharacter
        (selectedCoPoissonMuntzParameter observation))
      (AddMonoidAlgebra.single exponent coefficient)
  rw [show AddMonoidAlgebra.single exponent coefficient =
      coefficient • AddMonoidAlgebra.single exponent 1 by simp,
    map_smul, map_smul]
  apply congrArg (fun scalar : ℂ => coefficient • scalar)
  calc
    selectedPrimeExponentPoleMellinMap observation nontrivial
        (AddMonoidAlgebra.single exponent 1) =
      quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare (primeExponentScale exponent)) := by
          simpa [selectedPrimeExponentPoleMellinMap] using
            selectedPrimeExponentPoleMellinMap_single
              observation nontrivial exponent
    _ = _ := (primeExponentCharacterEvaluation_single
      (selectedCoPoissonMuntzParameter observation) exponent).symm

theorem reversalPrimeExponentPoleMellinMap_eq_characterEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPoleMellinMap observation nontrivial =
      primeExponentCharacterEvaluation
        (primeExponentMellinCharacter
          (reversalCoPoissonMuntzParameter observation)) := by
  apply AddMonoidAlgebra.lhom_ext'
  intro exponent
  apply LinearMap.ext
  intro coefficient
  change reversalPrimeExponentPoleMellinMap observation nontrivial
      (AddMonoidAlgebra.single exponent coefficient) =
    primeExponentCharacterEvaluation
      (primeExponentMellinCharacter
        (reversalCoPoissonMuntzParameter observation))
      (AddMonoidAlgebra.single exponent coefficient)
  rw [show AddMonoidAlgebra.single exponent coefficient =
      coefficient • AddMonoidAlgebra.single exponent 1 by simp,
    map_smul, map_smul]
  apply congrArg (fun scalar : ℂ => coefficient • scalar)
  calc
    reversalPrimeExponentPoleMellinMap observation nontrivial
        (AddMonoidAlgebra.single exponent 1) =
      quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare (primeExponentScale exponent)) := by
          simpa [reversalPrimeExponentPoleMellinMap] using
            reversalPrimeExponentPoleMellinMap_single
              observation nontrivial exponent
    _ = _ := (primeExponentCharacterEvaluation_single
      (reversalCoPoissonMuntzParameter observation) exponent).symm

def pairedPrimeExponentMellinMeasurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] QRich.ClozelJPair :=
  (selectedPrimeExponentPoleMellinMap observation nontrivial).prod
    (reversalPrimeExponentPoleMellinMap observation nontrivial)

def pairedPrimeExponentMellinAction
    (observation : GeneratedRiemannZeroObservation)
    (_nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (exponent : PrimeExponentGroup) :
    QRich.ClozelJPair →ₗ[ℤ] QRich.ClozelJPair :=
  (complexScalarAction
      (primeExponentMellinCharacter
        (selectedCoPoissonMuntzParameter observation) exponent)).prodMap
    (complexScalarAction
      (primeExponentMellinCharacter
        (reversalCoPoissonMuntzParameter observation) exponent))

theorem pairedPrimeExponentMellinMeasurement_left_covariance
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (exponent : PrimeExponentGroup)
    (value : PrimeExponentFactorizationCarrier) :
    pairedPrimeExponentMellinMeasurement observation nontrivial
        (factorizationLeftTranslation exponent value) =
      pairedPrimeExponentMellinAction observation nontrivial exponent
        (pairedPrimeExponentMellinMeasurement observation nontrivial value) := by
  apply Prod.ext
  · have covariance :
        selectedPrimeExponentPoleMellinMap observation nontrivial
            (factorizationLeftTranslation exponent value) =
          primeExponentMellinCharacter
              (selectedCoPoissonMuntzParameter observation) exponent *
            selectedPrimeExponentPoleMellinMap observation nontrivial value := by
      rw [selectedPrimeExponentPoleMellinMap_eq_characterEvaluation]
      change characterEvaluation _
          (factorizationGroupEquiv
            (factorizationLeftTranslation exponent value)) = _
      rw [factorizationGroupEquiv_leftTranslation]
      exact characterEvaluation_left_covariance _ _ _
    simpa [pairedPrimeExponentMellinMeasurement,
      pairedPrimeExponentMellinAction, complexScalarAction_apply] using covariance
  · have covariance :
        reversalPrimeExponentPoleMellinMap observation nontrivial
            (factorizationLeftTranslation exponent value) =
          primeExponentMellinCharacter
              (reversalCoPoissonMuntzParameter observation) exponent *
            reversalPrimeExponentPoleMellinMap observation nontrivial value := by
      rw [reversalPrimeExponentPoleMellinMap_eq_characterEvaluation]
      change characterEvaluation _
          (factorizationGroupEquiv
            (factorizationLeftTranslation exponent value)) = _
      rw [factorizationGroupEquiv_leftTranslation]
      exact characterEvaluation_left_covariance _ _ _
    simpa [pairedPrimeExponentMellinMeasurement,
      pairedPrimeExponentMellinAction, complexScalarAction_apply] using covariance

def arithmeticMellinJointMeasurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      AddCircle (1 : ℚ) × QRich.ClozelJPair :=
  stageThreeArithmeticMeasurement.prod
    (pairedPrimeExponentMellinMeasurement observation nontrivial)

def arithmeticMellinJointMeasurementAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (exponent : PrimeExponentGroup) :
    (AddCircle (1 : ℚ) × QRich.ClozelJPair) →ₗ[ℤ]
      AddCircle (1 : ℚ) × QRich.ClozelJPair :=
  LinearMap.id.prodMap
    (pairedPrimeExponentMellinAction observation nontrivial exponent)

/-- Algebraic common-action mechanism.  Public authority below is restricted
to the actual prime-three generator. -/
theorem arithmeticMellinJointMeasurement_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (exponent : PrimeExponentGroup) :
    (arithmeticMellinJointMeasurementAction
        observation nontrivial exponent).comp
          (arithmeticMellinJointMeasurement observation nontrivial) =
      (arithmeticMellinJointMeasurement observation nontrivial).comp
        (factorizationLeftTranslation exponent).toLinearMap := by
  apply LinearMap.ext
  intro value
  apply Prod.ext
  · change stageThreeArithmeticMeasurement value =
      stageThreeArithmeticMeasurement
        (factorizationLeftTranslation exponent value)
    exact (stageThreeArithmeticMeasurement_left_covariance exponent value).symm
  · change pairedPrimeExponentMellinAction observation nontrivial exponent
        (pairedPrimeExponentMellinMeasurement observation nontrivial value) =
      pairedPrimeExponentMellinMeasurement observation nontrivial
        (factorizationLeftTranslation exponent value)
    exact (pairedPrimeExponentMellinMeasurement_left_covariance
      observation nontrivial exponent value).symm

theorem zeroOwnedReceiptStageThreeCharacterOccurrence_projects_jointState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (((((zeroOwnedReceiptStageThreeCharacterOccurrence
        observation nontrivial).map Prod.fst).map Prod.fst).map Prod.fst).map
        Sigma.fst).map Sigma.fst =
      zeroOwnedJointStateModuleOccurrence observation nontrivial := by
  rw [zeroOwnedReceiptStageThreeCharacterOccurrence_projects,
    zeroOwnedReceiptArithmeticCharacterOccurrence_projects,
    zeroOwnedReceiptArithmeticResidualOccurrence_projects,
    receiptCofinalFace_projects_allPrime,
    zeroOwnedAllPrimeWeilQuadraticOccurrence_projects]

theorem pairedPrimeExponentMellinMeasurement_eq_generatedFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    pairedPrimeExponentMellinMeasurement observation nontrivial =
      (generatedPrimeExponentPoleCouplingFace observation nontrivial
        ).selectedMellin.prod
        (generatedPrimeExponentPoleCouplingFace observation nontrivial
          ).reversalMellin := by
  rfl

/-- The unique public generator comes from the actual stage-three prime row. -/
def stageThreePrimeExponent : PrimeExponentGroup :=
  Multiplicative.ofAdd
    (Finsupp.single (rowPrime actualStageThreePrimeRow) 1)

theorem stageThreePrimeExponent_actualPrime :
    ((rowPrime actualStageThreePrimeRow : Nat)) = 3 :=
  actualStageThreePrimeRow_prime

theorem stageThreePrimeExponent_scale :
    primeExponentScale (Multiplicative.toAdd stageThreePrimeExponent) =
      blockPrimeScaleUnit (rowPrime actualStageThreePrimeRow) := by
  simp [stageThreePrimeExponent, primeExponentScale_single]

/-- Authoritative source-generated common action square. -/
theorem stageThreeArithmeticMellinGenerator_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (arithmeticMellinJointMeasurementAction observation nontrivial
        stageThreePrimeExponent).comp
          (arithmeticMellinJointMeasurement observation nontrivial) =
      (arithmeticMellinJointMeasurement observation nontrivial).comp
        (factorizationLeftTranslation
          stageThreePrimeExponent).toLinearMap :=
  arithmeticMellinJointMeasurement_square observation nontrivial
    stageThreePrimeExponent

structure ZeroOwnedStageThreeArithmeticMellinCommonActionCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : Type where
  occurrence_projects : type_of%
    (zeroOwnedReceiptStageThreeCharacterOccurrence_projects_jointState
      observation nontrivial)
  arithmetic_base_ne_zero : type_of%
    stageThreeArithmeticMeasurement_base_ne_zero
  mellin_measurement_generated : type_of%
    (pairedPrimeExponentMellinMeasurement_eq_generatedFace
      observation nontrivial)
  actual_prime : type_of% stageThreePrimeExponent_actualPrime
  actual_scale : type_of% stageThreePrimeExponent_scale
  generator_square : type_of%
    (stageThreeArithmeticMellinGenerator_square observation nontrivial)

def generateZeroOwnedStageThreeArithmeticMellinCommonActionCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ZeroOwnedStageThreeArithmeticMellinCommonActionCertificate
      observation nontrivial where
  occurrence_projects :=
    zeroOwnedReceiptStageThreeCharacterOccurrence_projects_jointState
      observation nontrivial
  arithmetic_base_ne_zero := stageThreeArithmeticMeasurement_base_ne_zero
  mellin_measurement_generated :=
    pairedPrimeExponentMellinMeasurement_eq_generatedFace
      observation nontrivial
  actual_prime := stageThreePrimeExponent_actualPrime
  actual_scale := stageThreePrimeExponent_scale
  generator_square :=
    stageThreeArithmeticMellinGenerator_square observation nontrivial

end
end Arithmetic.Character.CommonAction
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
