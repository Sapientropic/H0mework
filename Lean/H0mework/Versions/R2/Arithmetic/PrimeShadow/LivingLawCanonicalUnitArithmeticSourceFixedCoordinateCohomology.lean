import H0mework.Versions.R2.Arithmetic.EulerGlobal.CofiberCofinalRigidity

/-!
# Source-fixed coordinate cohomology

Local factorization homotopies are precomposed with the one generated global
whole-relation source.  The target continues to follow the actual local
inner restriction, so the resulting cohomology classes form a genuine
high-to-low family and the canonical whole component is preserved exactly.

This file does not assert that a finite-stage coordinate class is zero and
does not supply finite generation for the full scalar cohomology ambient.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticSourceFixedCoordinateCohomology

open CanonicalUnitArithmeticIntegralActionCofiberFamily
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex

abbrev Q := HomotopyCategory.quotient (ModuleCat ℤ) (ComplexShape.up ℤ)

abbrev GlobalLocalCoordinateClass (stage : Nat) :=
  CochainComplex.HomComplex.CohomologyClass
    ScalarWholeRelationComplex (localScalarInnerSingle stage) 0

noncomputable def localToGlobalCoordinateClass (stage : Nat) :
    LocalCoordinateClass stage →+ GlobalLocalCoordinateClass stage where
  toFun value :=
    (CohomologyClass.homAddEquiv).symm
      (Q.map (globalToLocalWholeRelationMap stage) ≫
        CohomologyClass.homAddEquiv value)
  map_zero' := by simp
  map_add' left right := by simp

@[simp] theorem localToGlobalCoordinateClass_apply
    (stage : Nat) (value : LocalCoordinateClass stage) :
    localToGlobalCoordinateClass stage value =
      (CohomologyClass.homAddEquiv).symm
        (Q.map (globalToLocalWholeRelationMap stage) ≫
          CohomologyClass.homAddEquiv value) :=
  rfl

theorem localToGlobalCoordinateClass_mk (stage : Nat)
    (value : Cocycle (LocalScalarWholeRelationComplex stage)
      (localScalarInnerSingle stage) 0) :
    localToGlobalCoordinateClass stage (CohomologyClass.mk value) =
      CohomologyClass.mk
        (value.precomp (globalToLocalWholeRelationMap stage)) := by
  apply CohomologyClass.homAddEquiv.injective
  rw [localToGlobalCoordinateClass_apply, AddEquiv.apply_symm_apply]
  simp only [CohomologyClass.homAddEquiv_apply,
    CohomologyClass.toHom_mk]
  rw [Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

theorem cocycleOfHom_precomp
    {A B C : CochainComplex (ModuleCat ℤ) ℤ}
    (first : A ⟶ B) (second : B ⟶ C) :
    (Cocycle.ofHom second).precomp first =
      Cocycle.ofHom (first ≫ second) := by
  apply Cocycle.ext
  exact (Cochain.ofHom_comp first second).symm

theorem cocycleOfHom_postcomp
    {A B C : CochainComplex (ModuleCat ℤ) ℤ}
    (first : A ⟶ B) (second : B ⟶ C) :
    (Cocycle.ofHom first).postcomp second =
      Cocycle.ofHom (first ≫ second) := by
  apply Cocycle.ext
  exact (Cochain.ofHom_comp first second).symm

noncomputable def globalWholeAntiInvariantClass (stage : Nat) :
    GlobalLocalCoordinateClass stage :=
  localToGlobalCoordinateClass stage (localWholeAntiInvariantClass stage)

noncomputable def globalQuotientAntiInvariantClass (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    GlobalLocalCoordinateClass stage :=
  localToGlobalCoordinateClass stage
    (localQuotientAntiInvariantClass stage row)

theorem globalWholeAntiInvariantClass_landing_nat
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    globalWholeAntiInvariantClass stage =
      (rowPrime row : Nat) ^ rowExponent row •
        globalQuotientAntiInvariantClass stage row := by
  unfold globalWholeAntiInvariantClass globalQuotientAntiInvariantClass
  rw [← map_nsmul, localWholeAntiInvariantClass_landing_nat]

theorem coefficientRestriction_successor (stage : Nat) :
    (localCoefficientSuccessor stage).comp
        (coefficientRestriction (stage + 1)) =
      coefficientRestriction stage := by
  exact congrArg (fun arrow => arrow.hom.toAddMonoidHom.toIntLinearMap)
    (limit.w
      CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber.GlobalZeroFiberDiagram
      (localSuccessorArrow stage))

theorem vertexRestriction_successor (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
        seedOccurrence.root stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding.vertexRestriction
          (stage + 1)) =
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding.vertexRestriction
        stage := by
  have coneSquare :=
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalFace.restriction_naturality
      (CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity.runtimeSuccessorArrow
        stage)
  rw [CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity.actualDiagram_map_runtimeSuccessor]
    at coneSquare
  exact congrArg (fun arrow => (arrow.f 0).hom) coneSquare

theorem relationRestriction_successor (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
        seedOccurrence.root stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding.relationRestriction
          (stage + 1)) =
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding.relationRestriction
        stage := by
  have coneSquare :=
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalFace.restriction_naturality
      (CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity.runtimeSuccessorArrow
        stage)
  rw [CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity.actualDiagram_map_runtimeSuccessor]
    at coneSquare
  exact congrArg (fun arrow => (arrow.f 1).hom) coneSquare

theorem localTensorRestriction_successor (stage : Nat) :
    (localScalarVertexSuccessor stage).comp
        (localTensorRestriction (stage + 1)) =
      localTensorRestriction stage := by
  unfold localScalarVertexSuccessor localTensorRestriction
  rw [← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · exact coefficientRestriction_successor stage
  · exact vertexRestriction_successor stage

theorem localRelationTensorRestriction_successor (stage : Nat) :
    (localScalarRelationSuccessor stage).comp
        (localRelationTensorRestriction (stage + 1)) =
      localRelationTensorRestriction stage := by
  unfold localScalarRelationSuccessor localRelationTensorRestriction
  rw [← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · exact coefficientRestriction_successor stage
  · exact relationRestriction_successor stage

theorem globalToLocalMap_successor (stage : Nat) :
    globalToLocalMap (stage + 1) ≫ localVertexSuccessorMap stage =
      globalToLocalMap stage := by
  unfold globalToLocalMap localVertexSuccessorMap
  rw [← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact localTensorRestriction_successor stage

theorem globalToLocalRelationMap_successor (stage : Nat) :
    globalToLocalRelationMap (stage + 1) ≫
        localRelationSuccessorMap stage =
      globalToLocalRelationMap stage := by
  unfold globalToLocalRelationMap localRelationSuccessorMap
  rw [← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact localRelationTensorRestriction_successor stage

theorem globalToLocalWholeRelationMap_successor (stage : Nat) :
    globalToLocalWholeRelationMap (stage + 1) ≫
        localWholeRelationSuccessorMap stage =
      globalToLocalWholeRelationMap stage := by
  unfold globalToLocalWholeRelationMap localWholeRelationSuccessorMap
  rw [← CochainMappingCoconeFunctoriality.mappingCoconeMap_comp]
  apply CochainMappingCoconeFunctoriality.mappingCoconeMap_congr
  · exact globalToLocalMap_successor stage
  · exact globalToLocalRelationMap_successor stage

noncomputable def globalCoordinateRestriction (stage : Nat) :
    GlobalLocalCoordinateClass (stage + 1) →+
      GlobalLocalCoordinateClass stage where
  toFun value :=
    (CohomologyClass.homAddEquiv).symm
      (CohomologyClass.homAddEquiv value ≫
        Q.map
          ((shiftFunctor
            (HomologicalComplex (ModuleCat ℤ) (ComplexShape.up ℤ))
              (0 : ℤ)).map
            (localScalarInnerSuccessorMap stage)))
  map_zero' := by simp
  map_add' left right := by simp

@[simp] theorem globalCoordinateRestriction_apply
    (stage : Nat) (value : GlobalLocalCoordinateClass (stage + 1)) :
    globalCoordinateRestriction stage value =
      (CohomologyClass.homAddEquiv).symm
        (CohomologyClass.homAddEquiv value ≫
          Q.map
            ((shiftFunctor
              (HomologicalComplex (ModuleCat ℤ) (ComplexShape.up ℤ))
                (0 : ℤ)).map
              (localScalarInnerSuccessorMap stage))) :=
  rfl

theorem globalCoordinateRestriction_mk (stage : Nat)
    (value : Cocycle ScalarWholeRelationComplex
      (localScalarInnerSingle (stage + 1)) 0) :
    globalCoordinateRestriction stage (CohomologyClass.mk value) =
      CohomologyClass.mk
        (value.postcomp (localScalarInnerSuccessorMap stage)) := by
  apply CohomologyClass.homAddEquiv.injective
  rw [globalCoordinateRestriction_apply, AddEquiv.apply_symm_apply]
  simp only [CohomologyClass.homAddEquiv_apply,
    CohomologyClass.toHom_mk]
  rw [Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

theorem globalCoordinateRestriction_whole (stage : Nat) :
    globalCoordinateRestriction stage
        (globalWholeAntiInvariantClass (stage + 1)) =
      globalWholeAntiInvariantClass stage := by
  unfold globalWholeAntiInvariantClass localWholeAntiInvariantClass
  rw [localToGlobalCoordinateClass_mk,
    globalCoordinateRestriction_mk,
    localToGlobalCoordinateClass_mk]
  rw [cocycleOfHom_precomp, cocycleOfHom_postcomp,
    cocycleOfHom_precomp]
  apply congrArg CohomologyClass.mk
  apply congrArg Cocycle.ofHom
  rw [Category.assoc,
    ← localWholeAntiInvariantCoordinateMap_successor_square,
    ← Category.assoc,
    globalToLocalWholeRelationMap_successor]

end CanonicalUnitArithmeticSourceFixedCoordinateCohomology
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
