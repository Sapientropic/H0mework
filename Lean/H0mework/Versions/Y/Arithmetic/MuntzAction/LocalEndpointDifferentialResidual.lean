import H0mework.Foundation.Relations.ScalarDifferentialResidual
import H0mework.Versions.Y.Arithmetic.MellinBoundary.ProperMellinLowHighRelativeOccurrence
import H0mework.Versions.Y.Arithmetic.EulerDualBlock.DeterminantLineEndpointSection

/-!
# Same-zero local endpoint differential residual

At a fixed actual factorization stage, the generated analytic point
specializes the existing pair endpoint section.  Its actual cochain
differential is retained in the generic differential coimage.  A faithful
row coordinate shows that this residual vanishes exactly when the selected
and reversal coordinates agree.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace LocalEndpointDifferentialResidual

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralRelationEmbedding
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineEndpointSection
open SourceGeneratedScalarDifferentialResidual
open scoped TensorProduct

noncomputable section

abbrev PairComplexLocalWholeVertex (stage : Nat) :=
  TensorProduct ℤ ℂ (WholeVertexModule seedOccurrence.root stage)

abbrev PairComplexLocalWholeRelation (stage : Nat) :=
  TensorProduct ℤ ℂ (WholeRelationModule seedOccurrence.root stage)

def complexLocalFactorizationDifferential (stage : Nat) :
    PairComplexLocalWholeVertex stage →ₗ[ℤ]
      PairComplexLocalWholeRelation stage :=
  TensorProduct.map LinearMap.id
    (factorizationDifferential seedOccurrence.root stage)

def pairPointLocalVertexSpecialization (stage : Nat)
    (point : PairPoint) :
    PairLocalWholeVertex stage →ₗ[ℤ]
      PairComplexLocalWholeVertex stage :=
  TensorProduct.map (pairPointCoefficientMap point) LinearMap.id

def pairPointLocalRelationSpecialization (stage : Nat)
    (point : PairPoint) :
    PairLocalWholeRelation stage →ₗ[ℤ]
      PairComplexLocalWholeRelation stage :=
  TensorProduct.map (pairPointCoefficientMap point) LinearMap.id

theorem pairPointLocalSpecialization_differential_square
    (stage : Nat) (point : PairPoint) :
    (complexLocalFactorizationDifferential stage).comp
        (pairPointLocalVertexSpecialization stage point) =
      (pairPointLocalRelationSpecialization stage point).comp
        (localPairFactorizationDifferential stage) := by
  rw [complexLocalFactorizationDifferential,
    pairPointLocalVertexSpecialization,
    pairPointLocalRelationSpecialization,
    localPairFactorizationDifferential,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · apply LinearMap.ext
    intro value
    rfl

def pairPointLocalEndpointValue (stage : Nat) (point : PairPoint) :
    PairComplexLocalWholeVertex stage :=
  pairPointLocalVertexSpecialization stage point
    (localUniversalPairEndpointSection stage)

theorem pairPointLocalEndpointValue_differential
    (stage : Nat) (point : PairPoint) :
    complexLocalFactorizationDifferential stage
        (pairPointLocalEndpointValue stage point) =
      (point.pair.1 - point.pair.2) ⊗ₜ[ℤ]
        localEndpointBoundaryRelation stage := by
  have square := LinearMap.congr_fun
    (pairPointLocalSpecialization_differential_square stage point)
    (localUniversalPairEndpointSection stage)
  change complexLocalFactorizationDifferential stage
      (pairPointLocalEndpointValue stage point) =
    pairPointLocalRelationSpecialization stage point
      (localPairFactorizationDifferential stage
        (localUniversalPairEndpointSection stage)) at square
  rw [localPairEndpoint_differential] at square
  simpa [pairPointLocalRelationSpecialization,
    pairPointCoefficientMap] using square

def localEndpointBoundaryCoordinate (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    WholeRelationModule seedOccurrence.root stage →ₗ[ℤ] ℤ :=
  (LinearMap.proj (row.1, (0 : Fin 2))).comp
    ((baseRead seedOccurrence.root stage).comp (LinearMap.proj row))

@[simp] theorem localEndpointBoundaryCoordinate_boundary
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    localEndpointBoundaryCoordinate stage row
        (localEndpointBoundaryRelation stage) = 1 := by
  simp [localEndpointBoundaryCoordinate,
    localEndpointBoundaryRelation, localInnerEmbedding,
    endpointAntiInvariantBase, leftEndpointBase, rightEndpointBase,
    LinearMap.comp_apply, baseRead_solutionOfBase, constantEulerBase]

def complexLocalEndpointBoundaryCoordinate (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    PairComplexLocalWholeRelation stage →ₗ[ℤ] ℂ :=
  (TensorProduct.rid ℤ ℂ).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      (localEndpointBoundaryCoordinate stage row))

@[simp] theorem complexLocalEndpointBoundaryCoordinate_tmul
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (coefficient : ℂ) :
    complexLocalEndpointBoundaryCoordinate stage row
        (coefficient ⊗ₜ[ℤ] localEndpointBoundaryRelation stage) =
      coefficient := by
  simp [complexLocalEndpointBoundaryCoordinate]

theorem pairPointLocalEndpointValue_differential_eq_zero_iff
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (point : PairPoint) :
    complexLocalFactorizationDifferential stage
        (pairPointLocalEndpointValue stage point) = 0 ↔
      point.pair.1 = point.pair.2 := by
  constructor
  · intro differentialZero
    have coordinateZero := congrArg
      (complexLocalEndpointBoundaryCoordinate stage row)
      differentialZero
    rw [pairPointLocalEndpointValue_differential,
      complexLocalEndpointBoundaryCoordinate_tmul, map_zero]
      at coordinateZero
    exact sub_eq_zero.mp coordinateZero
  · intro equality
    rw [pairPointLocalEndpointValue_differential, equality, sub_self]
    simp

def zeroPayloadPairPoint
    (zero : GeneratedZeroObservationPayload) : PairPoint :=
  pointOfMathlibZero zero.2.coordinate zero.2.mathlibZero

def zeroPayloadLocalEndpointValue (stage : Nat)
    (zero : GeneratedZeroObservationPayload) :
    PairComplexLocalWholeVertex stage :=
  pairPointLocalEndpointValue stage (zeroPayloadPairPoint zero)

theorem zeroPayloadLocalEndpointValue_differential
    (stage : Nat) (zero : GeneratedZeroObservationPayload) :
    complexLocalFactorizationDifferential stage
        (zeroPayloadLocalEndpointValue stage zero) =
      (zero.2.coordinate - coordinateReversal zero.2.coordinate) ⊗ₜ[ℤ]
        localEndpointBoundaryRelation stage := by
  exact pairPointLocalEndpointValue_differential stage
    (zeroPayloadPairPoint zero)

theorem zeroPayloadLocalEndpointValue_differential_eq_zero_iff
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (zero : GeneratedZeroObservationPayload) :
    complexLocalFactorizationDifferential stage
        (zeroPayloadLocalEndpointValue stage zero) = 0 ↔
      zero.2.coordinate = coordinateReversal zero.2.coordinate :=
  pairPointLocalEndpointValue_differential_eq_zero_iff
    stage row (zeroPayloadPairPoint zero)

abbrev ResidualPayload (stage : Nat) :=
  RootResidualPayload
    (fun _ : ProperMellinLowHighRelativePayload =>
      complexLocalFactorizationDifferential stage)

def occurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    RootedAccountedUnfolding (ResidualPayload stage) :=
  residualOccurrence
    (zeroOwnedProperMellinLowHighRelativeOccurrence observation nontrivial)
    (fun _ => complexLocalFactorizationDifferential stage)
    (fun payload => zeroPayloadLocalEndpointValue stage payload.1)

theorem occurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (occurrence observation nontrivial stage).map Sigma.fst =
      zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial :=
  residualOccurrence_projects _ _ _

theorem occurrence_root_differential_normalForm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    complexLocalFactorizationDifferential stage
        (zeroPayloadLocalEndpointValue stage
          (zeroOwnedProperMellinLowHighRelativeOccurrence
            observation nontrivial).root.1) =
      (observation.coordinate - coordinateReversal observation.coordinate) ⊗ₜ[ℤ]
        localEndpointBoundaryRelation stage := by
  exact zeroPayloadLocalEndpointValue_differential stage _

theorem occurrence_root_zero_iff_fixed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    (occurrence observation nontrivial stage).root.2 = 0 ↔
      observation.coordinate = coordinateReversal observation.coordinate := by
  rw [occurrence, residualOccurrence_root_zero_iff]
  exact zeroPayloadLocalEndpointValue_differential_eq_zero_iff
    stage row
    (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.1

end
end LocalEndpointDifferentialResidual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
