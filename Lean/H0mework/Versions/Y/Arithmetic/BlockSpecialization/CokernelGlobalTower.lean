import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import H0mework.Versions.Y.Arithmetic.BlockSpecialization.CokernelNaturality

/-!
# Global arithmetic read of the universal block cokernel tower

The arithmetic action-cokernels form their own `ModuleCat ℤ` inverse tower.
Restriction of scalars along the actual block specialization views that tower
in `ModuleCat BlockCoordinateRing`.  The finite semilinear quotient reads then
assemble into one block-linear natural transformation from the existing
symbolic cokernel diagram.

Applying `limMap` to the existing global endpoint class produces its global
arithmetic image.  Every local projection is the already installed arithmetic
endpoint class.  No claim that restriction or extension of scalars preserves
this limit is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace BlockCokernelGlobalTower

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open BlockArithmeticSpecializationStage
open BlockActionCokernelRead
open BlockActionCokernelNaturality
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

abbrev ArithmeticCokernelObject (stage : Nat) : ModuleCat ℤ :=
  ModuleCat.of ℤ (IntegralRelationOperatorCokernel stage)

noncomputable def arithmeticCokernelDiagram : ℕᵒᵖ ⥤ ModuleCat ℤ :=
  Functor.ofOpSequence
    (X := ArithmeticCokernelObject)
    (fun stage => ModuleCat.ofHom
      (integralRelationOperatorCokernelRestriction stage))

abbrev ArithmeticToBlock :=
  ModuleCat.restrictScalars actualBlockSpecialization

noncomputable abbrev restrictedArithmeticCokernelDiagram :
    ℕᵒᵖ ⥤ ModuleCat BlockCoordinateRing :=
  arithmeticCokernelDiagram ⋙ ArithmeticToBlock

/-- The finite semilinear quotient read, presented as an ordinary
block-linear map into the restricted arithmetic object. -/
def restrictedArithmeticCokernelRead (stage : Nat) :
    LocalRelationActionCokernel stage →ₗ[BlockCoordinateRing]
      (ArithmeticToBlock.obj (ArithmeticCokernelObject stage) : Type) where
  toFun := blockRelationActionCokernelArithmeticRead stage
  map_add' := (blockRelationActionCokernelArithmeticRead stage).map_add
  map_smul' := by
    intro coefficient value
    change blockRelationActionCokernelArithmeticRead stage
        (coefficient • value) =
      actualBlockSpecialization coefficient •
        blockRelationActionCokernelArithmeticRead stage value
    exact (blockRelationActionCokernelArithmeticRead stage).map_smulₛₗ
      coefficient value

@[simp] theorem restrictedArithmeticCokernelRead_endpoint (stage : Nat) :
    restrictedArithmeticCokernelRead stage
        (localEndpointBoundaryCokernelClass stage) =
      specializedIntegralEndpointBoundaryClass stage :=
  blockRelationActionCokernelArithmeticRead_endpointClass stage

/-- Stage naturality promoted to a natural transformation of the two actual
inverse diagrams. -/
noncomputable def blockToRestrictedArithmeticCokernelNatTrans :
    localRelationActionCokernelDiagram ⟶
      restrictedArithmeticCokernelDiagram :=
  NatTrans.ofOpSequence
    (fun stage => by
      change LocalRelationActionCokernelObject stage ⟶
        ArithmeticToBlock.obj (ArithmeticCokernelObject stage)
      exact ModuleCat.ofHom
        (Y := ArithmeticToBlock.obj (ArithmeticCokernelObject stage))
        (restrictedArithmeticCokernelRead stage))
    (fun stage => by
      simp only [localRelationActionCokernelDiagram,
        restrictedArithmeticCokernelDiagram, arithmeticCokernelDiagram,
        Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro value
      change blockRelationActionCokernelArithmeticRead stage
          (localRelationActionCokernelRestriction stage value) =
        integralRelationOperatorCokernelRestriction stage
          (blockRelationActionCokernelArithmeticRead (stage + 1) value)
      exact LinearMap.congr_fun
        (blockRelationActionCokernelArithmeticRead_restriction_square stage)
        value)

abbrev RestrictedArithmeticGlobalCokernel : ModuleCat BlockCoordinateRing :=
  limit restrictedArithmeticCokernelDiagram

/-- The limit map is induced directly by the finite natural transformation. -/
noncomputable def globalBlockCokernelArithmeticRead :
    GlobalRelationActionCokernel ⟶ RestrictedArithmeticGlobalCokernel :=
  limMap blockToRestrictedArithmeticCokernelNatTrans

/-- Apply the global map to the existing global symbolic endpoint class. -/
def globalSpecializedIntegralEndpointBoundaryClass :
    RestrictedArithmeticGlobalCokernel :=
  globalBlockCokernelArithmeticRead.hom
    globalEndpointBoundaryCokernelClass

/-- Every finite projection is the existing arithmetic endpoint class. -/
theorem globalSpecializedIntegralEndpointBoundaryClass_restriction
    (stage : Nat) :
    (limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op stage)).hom
        globalSpecializedIntegralEndpointBoundaryClass =
      specializedIntegralEndpointBoundaryClass stage := by
  have projection := ConcreteCategory.congr_hom
    (limMap_π blockToRestrictedArithmeticCokernelNatTrans
      (Opposite.op stage))
    globalEndpointBoundaryCokernelClass
  change
    (limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op stage)).hom
        (globalBlockCokernelArithmeticRead.hom
          globalEndpointBoundaryCokernelClass) =
      (restrictedArithmeticCokernelRead stage)
        ((limit.π localRelationActionCokernelDiagram
          (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass)
      at projection
  rw [globalEndpointBoundaryCokernelClass_restriction,
    restrictedArithmeticCokernelRead_endpoint] at projection
  exact projection

end
end BlockCokernelGlobalTower
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
