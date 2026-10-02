import H0mework.Versions.R2.Arithmetic.EulerDerived.EndpointDeterminantSupport

/-!
# Global relation-action cokernel class of the endpoint boundary

The actual relation restriction commutes with `1-M`, hence descends to the
local action cokernels.  Those descended restrictions preserve the literal
endpoint-boundary class.  The categorical limit therefore generates one
global same-component class, while the whole determinant continues to
annihilate every local restriction.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

theorem blockWholeRelationEulerOperator_restriction_square (stage : Nat) :
    (blockWholeRelationRestriction seedOccurrence.root stage).comp
        (blockWholeRelationEulerOperator seedOccurrence.root (stage + 1)) =
      (blockWholeRelationEulerOperator seedOccurrence.root stage).comp
        (blockWholeRelationRestriction seedOccurrence.root stage) := by
  unfold blockWholeRelationEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    blockWholeRelationRestriction_action_square]

theorem localBlockEndpointBoundaryRelation_restriction (stage : Nat) :
    blockWholeRelationRestriction seedOccurrence.root stage
        (localBlockEndpointBoundaryRelation (stage + 1)) =
      localBlockEndpointBoundaryRelation stage := by
  funext row index
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockWholeRelationRestriction,
      localBlockEndpointBoundaryRelation,
      localBlockEndpointAntiInvariant,
      blockWholeAntiInvariantProjection,
      blockInnerAntiInvariant, blockInnerReversal,
      blockInnerRestriction, localBlockEndpointVertexMap,
      blockLeftEndpointBase]

theorem relationOperatorRange_restriction (stage : Nat) :
    LinearMap.range
        (blockWholeRelationEulerOperator seedOccurrence.root (stage + 1)) ≤
      (LinearMap.range
        (blockWholeRelationEulerOperator seedOccurrence.root stage)).comap
          (blockWholeRelationRestriction seedOccurrence.root stage) := by
  intro value membership
  rcases membership with ⟨preimage, rfl⟩
  refine ⟨blockWholeRelationRestriction seedOccurrence.root stage preimage, ?_⟩
  have square := LinearMap.congr_fun
    (blockWholeRelationEulerOperator_restriction_square stage) preimage
  exact square.symm

def localRelationActionCokernelRestriction (stage : Nat) :
    LocalRelationActionCokernel (stage + 1) →ₗ[BlockCoordinateRing]
      LocalRelationActionCokernel stage :=
  Submodule.mapQ
    (LinearMap.range
      (blockWholeRelationEulerOperator seedOccurrence.root (stage + 1)))
    (LinearMap.range
      (blockWholeRelationEulerOperator seedOccurrence.root stage))
    (blockWholeRelationRestriction seedOccurrence.root stage)
    (relationOperatorRange_restriction stage)

def localEndpointBoundaryCokernelClass (stage : Nat) :
    LocalRelationActionCokernel stage :=
  localRelationActionCokernelProjection stage
    (localBlockEndpointBoundaryRelation stage)

theorem localRelationActionCokernelRestriction_boundaryClass (stage : Nat) :
    localRelationActionCokernelRestriction stage
        (localEndpointBoundaryCokernelClass (stage + 1)) =
      localEndpointBoundaryCokernelClass stage := by
  unfold localRelationActionCokernelRestriction
    localEndpointBoundaryCokernelClass
    localRelationActionCokernelProjection
  simp only [Submodule.mkQ_apply, Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk
    (localBlockEndpointBoundaryRelation_restriction stage)

theorem localEndpointBoundaryCokernelClass_determinant_zero (stage : Nat) :
    blockDeterminantSection seedOccurrence.root stage •
        localEndpointBoundaryCokernelClass stage = 0 := by
  change localRelationActionCokernelProjection stage
      (blockDeterminantSection seedOccurrence.root stage •
        localBlockEndpointBoundaryRelation stage) = 0
  exact determinant_smul_endpointBoundary_zero_in_cokernel stage

abbrev LocalRelationActionCokernelObject (stage : Nat) :
    ModuleCat BlockCoordinateRing :=
  ModuleCat.of BlockCoordinateRing (LocalRelationActionCokernel stage)

noncomputable def localRelationActionCokernelDiagram :
    ℕᵒᵖ ⥤ ModuleCat BlockCoordinateRing :=
  Functor.ofOpSequence
    (X := LocalRelationActionCokernelObject)
    (fun stage => ModuleCat.ofHom
      (localRelationActionCokernelRestriction stage))

abbrev BlockCoordinateUnitObject : ModuleCat BlockCoordinateRing :=
  ModuleCat.of BlockCoordinateRing BlockCoordinateRing

def localEndpointBoundaryCokernelClassMap (stage : Nat) :
    BlockCoordinateUnitObject ⟶ LocalRelationActionCokernelObject stage :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton BlockCoordinateRing
      (LocalRelationActionCokernel stage)
      (localEndpointBoundaryCokernelClass stage))

theorem localEndpointBoundaryCokernelClassMap_successor (stage : Nat) :
    localEndpointBoundaryCokernelClassMap (stage + 1) ≫
        ModuleCat.ofHom (localRelationActionCokernelRestriction stage) =
      localEndpointBoundaryCokernelClassMap stage := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change localRelationActionCokernelRestriction stage
      (coefficient • localEndpointBoundaryCokernelClass (stage + 1)) =
    coefficient • localEndpointBoundaryCokernelClass stage
  rw [map_smul,
    localRelationActionCokernelRestriction_boundaryClass]

noncomputable def endpointBoundaryCokernelCone :
    Cone localRelationActionCokernelDiagram where
  pt := BlockCoordinateUnitObject
  π := NatTrans.ofOpSequence
    localEndpointBoundaryCokernelClassMap
    (fun stage => by
      simp only [Functor.const_obj_map,
        localRelationActionCokernelDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (localEndpointBoundaryCokernelClassMap_successor stage).symm)

abbrev GlobalRelationActionCokernel : ModuleCat BlockCoordinateRing :=
  limit localRelationActionCokernelDiagram

noncomputable def globalEndpointBoundaryCokernelMap :
    BlockCoordinateUnitObject ⟶ GlobalRelationActionCokernel :=
  limit.lift _ endpointBoundaryCokernelCone

def globalEndpointBoundaryCokernelClass : GlobalRelationActionCokernel :=
  globalEndpointBoundaryCokernelMap.hom 1

theorem globalEndpointBoundaryCokernelClass_restriction (stage : Nat) :
    (limit.π localRelationActionCokernelDiagram
        (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass =
      localEndpointBoundaryCokernelClass stage := by
  unfold globalEndpointBoundaryCokernelClass
    globalEndpointBoundaryCokernelMap
  have restriction := ConcreteCategory.congr_hom
    (limit.lift_π endpointBoundaryCokernelCone (Opposite.op stage))
    (1 : BlockCoordinateRing)
  change
    (limit.π localRelationActionCokernelDiagram
        (Opposite.op stage)).hom
        ((limit.lift localRelationActionCokernelDiagram
          endpointBoundaryCokernelCone).hom (1 : BlockCoordinateRing)) =
      (localEndpointBoundaryCokernelClassMap stage).hom
        (1 : BlockCoordinateRing) at restriction
  calc
    _ = (localEndpointBoundaryCokernelClassMap stage).hom
        (1 : BlockCoordinateRing) := restriction
    _ = _ := by
      simp [localEndpointBoundaryCokernelClassMap,
        LinearMap.toSpanSingleton_apply]

theorem globalEndpointBoundaryCokernelClass_local_determinant_zero
    (stage : Nat) :
    blockDeterminantSection seedOccurrence.root stage •
        (limit.π localRelationActionCokernelDiagram
          (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass = 0 := by
  rw [globalEndpointBoundaryCokernelClass_restriction,
    localEndpointBoundaryCokernelClass_determinant_zero]

def globalEndpointBoundaryCokernelOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × GlobalRelationActionCokernel) :=
  seedOccurrence.map fun owner =>
    (owner, globalEndpointBoundaryCokernelClass)

theorem globalEndpointBoundaryCokernelOccurrence_projects :
    globalEndpointBoundaryCokernelOccurrence.map Prod.fst =
      seedOccurrence := by
  unfold globalEndpointBoundaryCokernelOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_actual_cokernel_successor_global_class_and_local_support :
    globalEndpointBoundaryCokernelOccurrence.map Prod.fst = seedOccurrence ∧
      (∀ stage,
        localRelationActionCokernelRestriction stage
            (localEndpointBoundaryCokernelClass (stage + 1)) =
          localEndpointBoundaryCokernelClass stage) ∧
      (∀ stage,
        (limit.π localRelationActionCokernelDiagram
            (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass =
          localEndpointBoundaryCokernelClass stage) ∧
      (∀ stage,
        blockDeterminantSection seedOccurrence.root stage •
            (limit.π localRelationActionCokernelDiagram
              (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass = 0) := by
  exact ⟨globalEndpointBoundaryCokernelOccurrence_projects,
    localRelationActionCokernelRestriction_boundaryClass,
    globalEndpointBoundaryCokernelClass_restriction,
    globalEndpointBoundaryCokernelClass_local_determinant_zero⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
