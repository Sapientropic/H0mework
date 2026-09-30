import H0mework.Versions.Y.Arithmetic.RiemannLineage.FullRowSquare
import H0mework.Versions.Y.Arithmetic.EulerDerived.AdjugateSuccessor
import H0mework.Realization.MappingCone.TotalFibreNaturality

/-!
# Successor cube for the full q-rich factor-row square

The actual arithmetic restriction maps the whole role, every quotient role,
and the prime-power row action in one cube.  Canonical total-fibre
transposition is therefore natural before any analytic specialization.

The cube uses the existing `seedOccurrence`, total-fibre restriction, and
factor-row restriction.  It introduces no parallel carrier, inverse
transition, endpoint equality, or fixedness premise.
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
namespace QRich

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainMappingCoconeDeterminantAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberSuccessor

noncomputable section

noncomputable def blockRowFamilyRestrictionMap (stage : Nat) :
    blockRowFamilySingle (stage + 1) ⟶ blockRowFamilySingle stage :=
  (CochainComplex.singleFunctor (ModuleCat BlockCoordinateRing) 0).map
    (ModuleCat.ofHom
      (blockWholeRelationRestriction seedOccurrence.root stage))

theorem blockPrimePowerFamilyRestriction_square (stage : Nat) :
    blockRowFamilyRestrictionMap stage ≫ blockPrimePowerFamilyMap stage =
      blockPrimePowerFamilyMap (stage + 1) ≫
        blockRowFamilyRestrictionMap stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockPrimePowerFamilyProjection stage
        (blockWholeRelationRestriction seedOccurrence.root stage value) =
      blockWholeRelationRestriction seedOccurrence.root stage
        (blockPrimePowerFamilyProjection (stage + 1) value)
    funext row
    change
      (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) •
          blockInnerRestriction seedOccurrence.root stage
            (value (liftFactorRow seedOccurrence.root stage row)) =
        blockInnerRestriction seedOccurrence.root stage
          (((((rowPrime (liftFactorRow seedOccurrence.root stage row) : Nat) :
              BlockCoordinateRing) ^
                rowExponent (liftFactorRow seedOccurrence.root stage row)) •
            value (liftFactorRow seedOccurrence.root stage row)))
    rw [map_smul, liftFactorRow_prime, liftFactorRow_exponent]
  · exact ConcreteCategory.congr_hom
      ((HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0
        (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))
        degree degreeZero).eq_of_tgt _ _) value

theorem blockQuotientFamilyRestriction_square (stage : Nat) :
    blockDirectRestriction seedOccurrence.root stage ≫
        blockQuotientFamilyMap stage =
      blockQuotientFamilyMap (stage + 1) ≫
        blockRowFamilyRestrictionMap stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockQuotientFamilyProjection stage
        (blockWholeVertexRestriction seedOccurrence.root stage value) =
      blockWholeRelationRestriction seedOccurrence.root stage
        (blockQuotientFamilyProjection (stage + 1) value)
    funext row
    have square := LinearMap.congr_fun
      (blockInnerAntiInvariant_restriction_square
        seedOccurrence.root stage)
      (value (some (liftFactorRow seedOccurrence.root stage row)))
    change blockInnerAntiInvariant seedOccurrence.root stage
        (blockInnerRestriction seedOccurrence.root stage
          (value (some (liftFactorRow seedOccurrence.root stage row)))) =
      blockInnerRestriction seedOccurrence.root stage
        (blockInnerAntiInvariant seedOccurrence.root (stage + 1)
          (value (some (liftFactorRow seedOccurrence.root stage row))))
    exact square.symm
  · exact ConcreteCategory.congr_hom
      ((HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0
        (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))
        degree degreeZero).eq_of_tgt _ _) value

theorem blockWholeFamilyRestriction_square (stage : Nat) :
    blockDirectRestriction seedOccurrence.root stage ≫
        blockWholeFamilyMap stage =
      blockWholeFamilyMap (stage + 1) ≫
        blockRowFamilyRestrictionMap stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeFamilyProjection stage
        (blockWholeVertexRestriction seedOccurrence.root stage value) =
      blockWholeRelationRestriction seedOccurrence.root stage
        (blockWholeFamilyProjection (stage + 1) value)
    funext row
    have square := LinearMap.congr_fun
      (blockInnerAntiInvariant_restriction_square
        seedOccurrence.root stage) (value none)
    change blockInnerAntiInvariant seedOccurrence.root stage
        (blockInnerRestriction seedOccurrence.root stage (value none)) =
      blockInnerRestriction seedOccurrence.root stage
        (blockInnerAntiInvariant seedOccurrence.root (stage + 1) (value none))
    exact square.symm
  · exact ConcreteCategory.congr_hom
      ((HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0
        (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))
        degree degreeZero).eq_of_tgt _ _) value

theorem localTotalFiberRestriction_fst (stage : Nat) :
    localTotalFiberRestriction stage ≫
        CochainComplex.mappingCocone.fst
          (totalRow (blockDirectEulerOperator stage)
            (blockDirectDeterminantMultiplication stage)) =
      CochainComplex.mappingCocone.fst
          (totalRow (blockDirectEulerOperator (stage + 1))
            (blockDirectDeterminantMultiplication (stage + 1))) ≫
        (localTotalFiberShearSuccessor stage).pairTransition := by
  unfold localTotalFiberRestriction
  exact CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
    (totalRow (blockDirectEulerOperator (stage + 1))
      (blockDirectDeterminantMultiplication (stage + 1)))
    (totalRow (blockDirectEulerOperator stage)
      (blockDirectDeterminantMultiplication stage))
    (localTotalFiberShearSuccessor stage).pairTransition
    (blockDirectRestriction seedOccurrence.root stage)
    (localTotalFiberShearSuccessor stage).pairTransition_row_square

theorem localTotalEndpointProjection_successor (stage : Nat) :
    localTotalFiberRestriction stage ≫ localTotalEndpointProjection stage =
      localTotalEndpointProjection (stage + 1) ≫
        blockDirectRestriction seedOccurrence.root stage := by
  unfold localTotalEndpointProjection
  calc
    localTotalFiberRestriction stage ≫
          CochainComplex.mappingCocone.fst
            (totalRow (blockDirectEulerOperator stage)
              (blockDirectDeterminantMultiplication stage)) ≫
        (biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
          LocalWholeComplex stage) =
      CochainComplex.mappingCocone.fst
          (totalRow (blockDirectEulerOperator (stage + 1))
            (blockDirectDeterminantMultiplication (stage + 1))) ≫
        (localTotalFiberShearSuccessor stage).pairTransition ≫
          (biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
            LocalWholeComplex stage) := by
              rw [← Category.assoc, localTotalFiberRestriction_fst]
              simp only [Category.assoc]
    _ = CochainComplex.mappingCocone.fst
          (totalRow (blockDirectEulerOperator (stage + 1))
            (blockDirectDeterminantMultiplication (stage + 1))) ≫
        (biprod.snd : LocalWholeComplex (stage + 1) ⊞
            LocalWholeComplex (stage + 1) ⟶
          LocalWholeComplex (stage + 1)) ≫
        blockDirectRestriction seedOccurrence.root stage := by
          rw [(localTotalFiberShearSuccessor stage).pairTransition_second]

theorem fullRowDerivedSquare_right_successor (stage : Nat) :
    localTotalFiberRestriction stage ≫
        (localTotalEndpointProjection stage ≫
          blockWholeFamilyMap stage) =
      (localTotalEndpointProjection (stage + 1) ≫
          blockWholeFamilyMap (stage + 1)) ≫
        blockRowFamilyRestrictionMap stage := by
  simp only [Category.assoc]
  rw [← Category.assoc, localTotalEndpointProjection_successor]
  simp only [Category.assoc]
  rw [blockWholeFamilyRestriction_square]

theorem fullRowDerivedSquare_twoCell (stage : Nat) :
    Cochain.ofHomotopy
        ((fullRowDerivedSquare (stage + 1)).square.compRight
          (blockRowFamilyRestrictionMap stage)) =
      Cochain.ofHomotopy
        ((fullRowDerivedSquare stage).square.compLeft
          (blockDirectRestriction seedOccurrence.root stage)) := by
  ext source target related : 1
  have highComponent := Cochain.congr_v
    (fullRowDerivedSquare_cochain (stage + 1)) source target related
  have lowComponent := Cochain.congr_v
    (fullRowDerivedSquare_cochain stage) source target related
  change
    (fullRowDerivedSquare (stage + 1)).square.hom source target ≫
        (blockRowFamilyRestrictionMap stage).f target =
      (blockDirectRestriction seedOccurrence.root stage).f source ≫
        (fullRowDerivedSquare stage).square.hom source target
  change (fullRowDerivedSquare (stage + 1)).square.hom source target =
      (-blockFactorizationFamilyCochain (stage + 1)).v
        source target related at highComponent
  change (fullRowDerivedSquare stage).square.hom source target =
      (-blockFactorizationFamilyCochain stage).v
        source target related at lowComponent
  rw [highComponent, lowComponent]
  by_cases sourceOne : source = 1
  · subst source
    have targetZero : target = 0 := by omega
    subst target
    change
      ((-𝟙 (ModuleCat.of BlockCoordinateRing
          (BlockRowFamily (stage + 1)))) ≫
        (blockRowFamilyRestrictionMap stage).f 0) =
      ((blockDirectRestriction seedOccurrence.root stage).f 1 ≫
        (-𝟙 (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))))
    rfl
  · simp [blockFactorizationFamilyCochain, sourceOne]

/-- The actual successor cube for all factor rows of one root occurrence. -/
noncomputable def fullRowDerivedCube (stage : Nat) :
    CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt
      (fullRowDerivedSquare (stage + 1)) (fullRowDerivedSquare stage) where
  upperLeft := blockDirectRestriction seedOccurrence.root stage
  upperRight := localTotalFiberRestriction stage
  lowerLeft := blockRowFamilyRestrictionMap stage
  lowerRight := blockRowFamilyRestrictionMap stage
  upperSquare := (localTotalInclusion_successor stage).symm
  lowerSquare := blockPrimePowerFamilyRestriction_square stage
  leftSquare := blockQuotientFamilyRestriction_square stage
  rightSquare := fullRowDerivedSquare_right_successor stage
  twoCell := fullRowDerivedSquare_twoCell stage

/-- Canonical transposition of the full row square commutes strictly with the
actual successor cube. -/
theorem fullRowGeneratedTotalIso_naturality (stage : Nat) :
    (fullRowDerivedCube stage).horizontalTotalTransition ≫
        (fullRowDerivedSquare stage).generatedTotalIso.hom =
      (fullRowDerivedSquare (stage + 1)).generatedTotalIso.hom ≫
        (fullRowDerivedCube stage).verticalTotalTransition :=
  (fullRowDerivedCube stage).generatedTotalIso_naturality

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
