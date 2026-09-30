import H0mework.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticActionCofiberCyclePrimePowerSplice
import H0mework.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticFactorizationWholeRelationGeneratedUniversalSolutionFixedness

/-!
# Universal solution through the actual cycle row splice

The already generated q-rich universal solution supplies a literal global
whole-relation cycle.  Restricting that same cycle through the point-free
prime-power splice reads exactly the component consumed by frozen rigidity,
and therefore reads zero.  This closes provenance between the generic row
homotopies and the existing universal fixedness theorem without accepting a
point lift, endpoint equality, or fixedness premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticUniversalSolutionCycleSplice

open CategoryTheory
open CanonicalUnitArithmeticActionCofiberCyclePrimePowerSplice
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticFactorizationWholeRelationGeneratedUniversalSolutionFixedness
open CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity
open CanonicalUnitArithmeticIntegralActionCofiberFamily
open CanonicalUnitArithmeticLocalCoordinateClassCycleEvaluation
open CochainMappingCoconeMappedBoundaryAtom

noncomputable section

noncomputable def universalSourcePoint (value : UniversalSolutionKernel) :
    localIntegralUnitSingle ⟶ ScalarWholeRelationComplex :=
  tautologicalWholeSourcePointMap (universalInclusion value)
    (LinearMap.mem_ker.mp value.2.1)

theorem universalSourcePoint_wholeCoordinateValue
    (stage : Nat) (value : UniversalSolutionKernel) :
    wholeCoordinatePointValue (universalSourcePoint value) stage =
      localWholeAntiInvariantComponent stage
        (localTensorRestriction stage (universalInclusion value)) := by
  let sourcePoint := universalSourcePoint value
  have globalFst :
      globalToLocalWholeRelationMap stage ≫
          CochainComplex.mappingCocone.fst
            (localScalarDifferentialMap stage) =
        CochainComplex.mappingCocone.fst scalarDifferentialMap ≫
          globalToLocalMap stage := by
    unfold globalToLocalWholeRelationMap
    exact CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
      scalarDifferentialMap (localScalarDifferentialMap stage)
      (globalToLocalMap stage) (globalToLocalRelationMap stage)
      (globalToLocal_differential_square stage)
  have mapEquality :
      (sourcePoint ≫ globalToLocalWholeRelationMap stage) ≫
          localWholeAntiInvariantCoordinateMap stage =
        tautologicalScalarVertexPointMap (universalInclusion value) ≫
          globalToLocalMap stage ≫
            localWholeAntiInvariantSingleMap stage := by
    unfold localWholeAntiInvariantCoordinateMap
    calc
      (sourcePoint ≫ globalToLocalWholeRelationMap stage) ≫
            (CochainComplex.mappingCocone.fst
              (localScalarDifferentialMap stage) ≫
                localWholeAntiInvariantSingleMap stage) =
          sourcePoint ≫
            ((globalToLocalWholeRelationMap stage ≫
              CochainComplex.mappingCocone.fst
                (localScalarDifferentialMap stage)) ≫
              localWholeAntiInvariantSingleMap stage) := by simp
      _ = sourcePoint ≫
            ((CochainComplex.mappingCocone.fst scalarDifferentialMap ≫
                globalToLocalMap stage) ≫
              localWholeAntiInvariantSingleMap stage) := by
            rw [globalFst]
      _ = (sourcePoint ≫
              CochainComplex.mappingCocone.fst scalarDifferentialMap) ≫
            globalToLocalMap stage ≫
              localWholeAntiInvariantSingleMap stage := by simp
      _ = tautologicalScalarVertexPointMap (universalInclusion value) ≫
            globalToLocalMap stage ≫
              localWholeAntiInvariantSingleMap stage := by
            rw [show sourcePoint ≫
                CochainComplex.mappingCocone.fst scalarDifferentialMap =
              tautologicalScalarVertexPointMap (universalInclusion value) by
                exact tautologicalWholeSourcePointMap_fst _ _]
  have coordinate := tautologicalScalarVertexPointMap_coordinate stage
    (universalInclusion value)
  have finalMap :
      (sourcePoint ≫ globalToLocalWholeRelationMap stage) ≫
          localWholeAntiInvariantCoordinateMap stage =
        (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
          (elementHom
            (localWholeAntiInvariantComponent stage
              (localTensorRestriction stage (universalInclusion value)))) :=
    mapEquality.trans coordinate
  have evaluated := congrArg
    (fun map => (map.f 0).hom localIntegralUnitGenerator) finalMap
  have transported := congrArg
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (LocalScalarInnerObject stage)).hom.hom evaluated
  have rhsEvaluation :
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (LocalScalarInnerObject stage)).hom.hom
          ((((CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
            (elementHom (M := LocalScalarInnerObject stage)
              (localWholeAntiInvariantComponent stage
                (localTensorRestriction stage
                  (universalInclusion value))))).f 0).hom
            localIntegralUnitGenerator) =
        localWholeAntiInvariantComponent stage
          (localTensorRestriction stage (universalInclusion value)) := by
    change (elementHom (M := LocalScalarInnerObject stage)
      (localWholeAntiInvariantComponent stage
        (localTensorRestriction stage (universalInclusion value)))).hom 1 = _
    rw [elementHom_one]
  unfold wholeCoordinatePointValue wholeCoordinatePointMap restrictedPoint
  change
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (LocalScalarInnerObject stage)).hom.hom
        (((universalSourcePoint value ≫
          globalToLocalWholeRelationMap stage) ≫
            localWholeAntiInvariantCoordinateMap stage).f 0
              localIntegralUnitGenerator) = _
  exact transported.trans rhsEvaluation

theorem universalSourcePoint_wholeCoordinateValue_eq_zero
    (stage : Nat) (value : UniversalSolutionKernel) :
    wholeCoordinatePointValue (universalSourcePoint value) stage = 0 := by
  rw [universalSourcePoint_wholeCoordinateValue]
  exact universalSolution_localAntiInvariant_eq_zero stage value

end
end CanonicalUnitArithmeticUniversalSolutionCycleSplice
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
