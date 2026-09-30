import H0mework.Versions.Y.Arithmetic.EulerDualBlock.GlobalZeroFiber
import H0mework.Versions.Y.Arithmetic.EulerDerived.EndpointCokernelState

/-!
# Formal-zero-fibre global endpoint-boundary cokernel class

The generated polynomial-section zero-fibre maps and the actual
relation-cokernel restrictions are tensored over the common block coordinate
ring.  They preserve `1 ⊗ [boundary]` strictly, so the limit generates one
formal-zero-fibre global class on the same root occurrence.  This retains the
uncancelled boundary class; it does not identify it with the unscaled endpoint
or with an analytic point.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryZeroFiberCokernelGlobalState

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open CofinalPolynomialSectionZeroFiber
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

abbrev LocalGeneratedBlockZeroFiberRing (stage : Nat) :=
  AdjoinRoot
    (GlobalBlockDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial

def blockSectionSuccessorArrow (stage : Nat) :
    (Opposite.op (stage + 1) : ℕᵒᵖ) ⟶ Opposite.op stage :=
  (homOfLE (Nat.le_succ stage)).op

def localGeneratedBlockZeroFiberRestrictionHom (stage : Nat) :
    LocalGeneratedBlockZeroFiberRing (stage + 1) →+*
      LocalGeneratedBlockZeroFiberRing stage :=
  zeroFiberMap
    (GlobalBlockDeterminantSectionDiagram.map
      (blockSectionSuccessorArrow stage))

def localGeneratedBlockZeroFiberRestrictionLinear (stage : Nat) :
    LocalGeneratedBlockZeroFiberRing (stage + 1) →ₗ[BlockCoordinateRing]
      LocalGeneratedBlockZeroFiberRing stage where
  toFun := localGeneratedBlockZeroFiberRestrictionHom stage
  map_add' left right :=
    (localGeneratedBlockZeroFiberRestrictionHom stage).map_add left right
  map_smul' coefficient value := by
    simp only [RingHom.id_apply, Algebra.smul_def,
      AdjoinRoot.algebraMap_eq]
    rw [map_mul]
    apply congrArg (fun coefficientImage => coefficientImage *
      localGeneratedBlockZeroFiberRestrictionHom stage value)
    unfold localGeneratedBlockZeroFiberRestrictionHom
    exact zeroFiberMap_base
      (GlobalBlockDeterminantSectionDiagram.map
        (blockSectionSuccessorArrow stage)) coefficient

abbrev LocalZeroFiberRelationCokernel (stage : Nat) :=
  TensorProduct BlockCoordinateRing
    (LocalGeneratedBlockZeroFiberRing stage)
    (LocalRelationActionCokernel stage)

def localZeroFiberEndpointBoundaryClass (stage : Nat) :
    LocalZeroFiberRelationCokernel stage :=
  (1 : LocalGeneratedBlockZeroFiberRing stage) ⊗ₜ[BlockCoordinateRing]
    localEndpointBoundaryCokernelClass stage

def localZeroFiberRelationCokernelRestriction (stage : Nat) :
    LocalZeroFiberRelationCokernel (stage + 1) →ₗ[BlockCoordinateRing]
      LocalZeroFiberRelationCokernel stage :=
  TensorProduct.map
    (localGeneratedBlockZeroFiberRestrictionLinear stage)
    (localRelationActionCokernelRestriction stage)

theorem localZeroFiberRelationCokernelRestriction_boundaryClass
    (stage : Nat) :
    localZeroFiberRelationCokernelRestriction stage
        (localZeroFiberEndpointBoundaryClass (stage + 1)) =
      localZeroFiberEndpointBoundaryClass stage := by
  simp [localZeroFiberRelationCokernelRestriction,
    localZeroFiberEndpointBoundaryClass,
    localGeneratedBlockZeroFiberRestrictionLinear,
    localGeneratedBlockZeroFiberRestrictionHom,
    localRelationActionCokernelRestriction_boundaryClass]

abbrev LocalZeroFiberRelationCokernelObject (stage : Nat) :
    ModuleCat BlockCoordinateRing :=
  ModuleCat.of BlockCoordinateRing (LocalZeroFiberRelationCokernel stage)

noncomputable def localZeroFiberRelationCokernelDiagram :
    ℕᵒᵖ ⥤ ModuleCat BlockCoordinateRing :=
  Functor.ofOpSequence
    (X := LocalZeroFiberRelationCokernelObject)
    (fun stage => ModuleCat.ofHom
      (localZeroFiberRelationCokernelRestriction stage))

abbrev BlockCoordinateUnitObject : ModuleCat BlockCoordinateRing :=
  ModuleCat.of BlockCoordinateRing BlockCoordinateRing

def localZeroFiberEndpointBoundaryClassMap (stage : Nat) :
    BlockCoordinateUnitObject ⟶
      LocalZeroFiberRelationCokernelObject stage :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton BlockCoordinateRing
      (LocalZeroFiberRelationCokernel stage)
      (localZeroFiberEndpointBoundaryClass stage))

theorem localZeroFiberEndpointBoundaryClassMap_successor (stage : Nat) :
    localZeroFiberEndpointBoundaryClassMap (stage + 1) ≫
        ModuleCat.ofHom
          (localZeroFiberRelationCokernelRestriction stage) =
      localZeroFiberEndpointBoundaryClassMap stage := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change localZeroFiberRelationCokernelRestriction stage
      (coefficient • localZeroFiberEndpointBoundaryClass (stage + 1)) =
    coefficient • localZeroFiberEndpointBoundaryClass stage
  rw [map_smul,
    localZeroFiberRelationCokernelRestriction_boundaryClass]

noncomputable def localZeroFiberEndpointBoundaryCone :
    Cone localZeroFiberRelationCokernelDiagram where
  pt := BlockCoordinateUnitObject
  π := NatTrans.ofOpSequence
    localZeroFiberEndpointBoundaryClassMap
    (fun stage => by
      simp only [Functor.const_obj_map,
        localZeroFiberRelationCokernelDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (localZeroFiberEndpointBoundaryClassMap_successor stage).symm)

abbrev GlobalZeroFiberRelationCokernel : ModuleCat BlockCoordinateRing :=
  limit localZeroFiberRelationCokernelDiagram

noncomputable def globalZeroFiberEndpointBoundaryMap :
    BlockCoordinateUnitObject ⟶ GlobalZeroFiberRelationCokernel :=
  limit.lift _ localZeroFiberEndpointBoundaryCone

def globalZeroFiberEndpointBoundaryClass :
    GlobalZeroFiberRelationCokernel :=
  globalZeroFiberEndpointBoundaryMap.hom 1

theorem globalZeroFiberEndpointBoundaryClass_restriction (stage : Nat) :
    (limit.π localZeroFiberRelationCokernelDiagram
        (Opposite.op stage)).hom globalZeroFiberEndpointBoundaryClass =
      localZeroFiberEndpointBoundaryClass stage := by
  unfold globalZeroFiberEndpointBoundaryClass
    globalZeroFiberEndpointBoundaryMap
  have restriction := ConcreteCategory.congr_hom
    (limit.lift_π localZeroFiberEndpointBoundaryCone
      (Opposite.op stage)) (1 : BlockCoordinateRing)
  change
    (limit.π localZeroFiberRelationCokernelDiagram
        (Opposite.op stage)).hom
        ((limit.lift localZeroFiberRelationCokernelDiagram
          localZeroFiberEndpointBoundaryCone).hom
            (1 : BlockCoordinateRing)) =
      (localZeroFiberEndpointBoundaryClassMap stage).hom
        (1 : BlockCoordinateRing) at restriction
  calc
    _ = (localZeroFiberEndpointBoundaryClassMap stage).hom
        (1 : BlockCoordinateRing) := restriction
    _ = _ := by
      simp [localZeroFiberEndpointBoundaryClassMap,
        LinearMap.toSpanSingleton_apply]

def globalZeroFiberEndpointBoundaryOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × GlobalZeroFiberRelationCokernel) :=
  seedOccurrence.map fun owner =>
    (owner, globalZeroFiberEndpointBoundaryClass)

theorem globalZeroFiberEndpointBoundaryOccurrence_projects :
    globalZeroFiberEndpointBoundaryOccurrence.map Prod.fst =
      seedOccurrence := by
  unfold globalZeroFiberEndpointBoundaryOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_generated_zero_fibre_actual_cokernel_successor_and_global_class :
    globalZeroFiberEndpointBoundaryOccurrence.map Prod.fst = seedOccurrence ∧
      (∀ stage,
        localZeroFiberRelationCokernelRestriction stage
            (localZeroFiberEndpointBoundaryClass (stage + 1)) =
          localZeroFiberEndpointBoundaryClass stage) ∧
      (∀ stage,
        (limit.π localZeroFiberRelationCokernelDiagram
            (Opposite.op stage)).hom globalZeroFiberEndpointBoundaryClass =
          localZeroFiberEndpointBoundaryClass stage) := by
  exact ⟨globalZeroFiberEndpointBoundaryOccurrence_projects,
    localZeroFiberRelationCokernelRestriction_boundaryClass,
    globalZeroFiberEndpointBoundaryClass_restriction⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryZeroFiberCokernelGlobalState
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
