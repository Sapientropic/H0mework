import H0mework.Versions.Y.Arithmetic.EulerDerived.EndpointCokernelState
import H0mework.Versions.Y.Arithmetic.EulerAnalytic.EndpointBoundaryEigenAction

/-!
# The common local relation-action cokernel

The symbolic all-place endpoint relation and the analytic action cofiber do
not share a raw degree-one coordinate: the cofiber endpoint is a shifted
degree-zero section.  This file restores the missing source differential.

Scalar extension by the actual pair coefficient map carries the complete
symbolic `1 - M` relation operator to the analytic local operator.  It
therefore descends to the two action cokernels, and the symbolic endpoint
class becomes the quotient class of the actual analytic endpoint boundary.
No vanishing, inverse, point specialization, or spectral premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalRiemannPairLocalRelationActionCokernel

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open scoped ChangeOfRings

noncomputable section

abbrev PairLocalRelationActionCokernel (stage : Nat) :=
  (PairBlockLocalState stage).X 1 ⧸
    LinearMap.range ((pairBlockLocalEulerOperator stage).f 1).hom

def pairLocalRelationActionCokernelProjection (stage : Nat) :
    (PairBlockLocalState stage).X 1 →ₗ[PairCoefficientRing]
      PairLocalRelationActionCokernel stage :=
  Submodule.mkQ _

/-- The actual endpoint-difference coefficient tensored with an entire
symbolic relation.  It is semilinear for the installed block-to-pair map. -/
def blockRelationToPairLocal (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage →ₛₗ[
      blockCoordinateToPairZeroFiber] (PairBlockLocalState stage).X 1 where
  toFun := fun relation =>
    (universalLeftCoordinate installedOwner -
        universalRightCoordinate installedOwner) ⊗ₜ[
      BlockCoordinateRing, blockCoordinateToPairZeroFiber] relation
  map_add' := by
    intro left right
    rw [TensorProduct.tmul_add]
  map_smul' := by
    intro coefficient relation
    rw [TensorProduct.tmul_smul]
    rfl

/-- The full operator square, before quotienting. -/
theorem blockRelationToPairLocal_operator_square (stage : Nat) :
    (blockRelationToPairLocal stage).comp
        (blockWholeRelationEulerOperator seedOccurrence.root stage) =
      ((pairBlockLocalEulerOperator stage).f 1).hom.comp
        (blockRelationToPairLocal stage) := by
  letI : Module BlockCoordinateRing PairCoefficientRing :=
    Module.compHom PairCoefficientRing blockCoordinateToPairZeroFiber
  apply LinearMap.ext
  intro relation
  change
    (universalLeftCoordinate installedOwner -
        universalRightCoordinate installedOwner) ⊗ₜ[
      BlockCoordinateRing, blockCoordinateToPairZeroFiber]
        (blockWholeRelationEulerOperator seedOccurrence.root stage relation) =
      ((pairBlockLocalEulerOperator stage).f 1).hom
        ((universalLeftCoordinate installedOwner -
            universalRightCoordinate installedOwner) ⊗ₜ[
          BlockCoordinateRing, blockCoordinateToPairZeroFiber] relation)
  rw [show blockWholeRelationEulerOperator seedOccurrence.root stage relation =
      relation - blockWholeRelationAction seedOccurrence.root stage relation by
    rfl,
    TensorProduct.tmul_sub]
  change _ = _ -
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
      ((blockDirectEulerAction seedOccurrence.root stage).f 1)
      ((universalLeftCoordinate installedOwner -
          universalRightCoordinate installedOwner) ⊗ₜ[
        BlockCoordinateRing, blockCoordinateToPairZeroFiber] relation)
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

theorem blockOperatorRange_maps_to_pairOperatorRange (stage : Nat) :
    LinearMap.range
        (blockWholeRelationEulerOperator seedOccurrence.root stage) ≤
      (LinearMap.range ((pairBlockLocalEulerOperator stage).f 1).hom).comap
        (blockRelationToPairLocal stage) := by
  rintro value ⟨preimage, rfl⟩
  refine ⟨blockRelationToPairLocal stage preimage, ?_⟩
  exact (LinearMap.congr_fun
    (blockRelationToPairLocal_operator_square stage) preimage).symm

/-- The canonical dependent-face map on relation-action cokernels. -/
def formalClassToPairLocal (stage : Nat) :
    LocalRelationActionCokernel stage →ₛₗ[blockCoordinateToPairZeroFiber]
      PairLocalRelationActionCokernel stage :=
  Submodule.mapQ
    (LinearMap.range
      (blockWholeRelationEulerOperator seedOccurrence.root stage))
    (LinearMap.range ((pairBlockLocalEulerOperator stage).f 1).hom)
    (blockRelationToPairLocal stage)
    (blockOperatorRange_maps_to_pairOperatorRange stage)

@[simp] theorem formalClassToPairLocal_mk
    (stage : Nat) (relation : BlockWholeRelation seedOccurrence.root stage) :
    formalClassToPairLocal stage
        (localRelationActionCokernelProjection stage relation) =
      pairLocalRelationActionCokernelProjection stage
        (blockRelationToPairLocal stage relation) := by
  rfl

/-- The symbolic endpoint class reads as the actual analytic endpoint
boundary class, not as a freely supplied target value. -/
theorem formalClassToPairLocal_endpointClass (stage : Nat) :
    formalClassToPairLocal stage (localEndpointBoundaryCokernelClass stage) =
      pairLocalRelationActionCokernelProjection stage
        (localPairEndpointBoundary stage) := by
  rw [show localEndpointBoundaryCokernelClass stage =
      localRelationActionCokernelProjection stage
        (localBlockEndpointBoundaryRelation stage) by rfl,
    formalClassToPairLocal_mk]
  apply congrArg (pairLocalRelationActionCokernelProjection stage)
  change localPairEndpointBoundaryActual stage =
    localPairEndpointBoundary stage
  exact (localPairEndpointBoundary_eq_actual stage).symm

end
end CanonicalRiemannPairLocalRelationActionCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
