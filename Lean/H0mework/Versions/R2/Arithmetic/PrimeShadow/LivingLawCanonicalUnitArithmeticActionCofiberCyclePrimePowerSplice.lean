import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticLocalCoordinateClassCycleEvaluation
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticSourceFixedCoordinateCohomology

/-!
# Actual prime-power rows on a global action-cofiber cycle

An already generated global source point is restricted to each exact local
whole-relation occurrence.  The existing factorization-row homotopy then
gives the literal prime-power landing and canonical quotient-zero for its
anti-invariant coordinate.  The existing source successor preserves that
same component.

This is the direct domain-to-framework splice.  It does not submit a division
root, a completed schedule, finite generation, fixedness, or an endpoint
readback.  A downstream owner must supply its point from the generated
determinant zero fibre, not as a caller-selected q-rich value.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticActionCofiberCyclePrimePowerSplice

open CategoryTheory
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticIntegralActionCofiberFamily
open CanonicalUnitArithmeticLocalCoordinateClassCycleEvaluation
open CanonicalUnitArithmeticSourceFixedCoordinateCohomology
open CochainComplex.HomComplex

noncomputable section

variable (point : localIntegralUnitSingle ⟶ ScalarWholeRelationComplex)

noncomputable def restrictedPoint (stage : Nat) :
    localIntegralUnitSingle ⟶ LocalScalarWholeRelationComplex stage :=
  point ≫ globalToLocalWholeRelationMap stage

noncomputable def wholeCoordinatePointMap (stage : Nat) :
    localIntegralUnitSingle ⟶ localScalarInnerSingle stage :=
  restrictedPoint point stage ≫ localWholeAntiInvariantCoordinateMap stage

noncomputable def quotientCoordinatePointMap (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    localIntegralUnitSingle ⟶ localScalarInnerSingle stage :=
  restrictedPoint point stage ≫
    localQuotientAntiInvariantCoordinateMap stage row

def wholeCoordinatePointValue (stage : Nat) : LocalScalarInner stage :=
  ((wholeCoordinatePointMap point stage).f 0).hom localIntegralUnitGenerator

def quotientCoordinatePointValue (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) : LocalScalarInner stage :=
  ((quotientCoordinatePointMap point stage row).f 0).hom
    localIntegralUnitGenerator

theorem homotopic_single_zero_maps_equal
    {target : ModuleCat ℤ}
    {left right : localIntegralUnitSingle ⟶
      (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj target}
    (homotopy : Homotopy left right) :
    left = right := by
  apply HomologicalComplex.from_single_hom_ext
  have component := homotopy.comm 0
  simp [dNext, prevD, localIntegralUnitSingle,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors] at component
  exact component

theorem pointMap_primePower_landing
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    wholeCoordinatePointMap point stage =
      (rowPrime row : Nat) ^ rowExponent row •
        quotientCoordinatePointMap point stage row := by
  let localPoint := restrictedPoint point stage
  have homotopy :=
    (localFactorizationRowHomotopy stage row).compLeft localPoint
  have zeroDifference :
      localPoint ≫
          (localWholeAntiInvariantCoordinateMap stage -
            localRowPrimePower row •
              localQuotientAntiInvariantCoordinateMap stage row) = 0 :=
    homotopic_single_zero_maps_equal homotopy
  rw [Preadditive.comp_sub, Preadditive.comp_zsmul] at zeroDifference
  change wholeCoordinatePointMap point stage -
      localRowPrimePower row •
        quotientCoordinatePointMap point stage row = 0 at zeroDifference
  have landing := sub_eq_zero.mp zeroDifference
  simpa only [localRowPrimePower, ← Nat.cast_pow, natCast_zsmul] using landing

theorem pointValue_primePower_landing
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    wholeCoordinatePointValue point stage =
      (rowPrime row : Nat) ^ rowExponent row •
        quotientCoordinatePointValue point stage row := by
  have landing := congrArg
    (fun map => (map.f 0).hom localIntegralUnitGenerator)
    (pointMap_primePower_landing point stage row)
  simpa [wholeCoordinatePointValue, quotientCoordinatePointValue] using landing

theorem pointValue_quotientZero
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    PrimePowerQuotientEvaluation.evaluator
        (LocalScalarInner stage)
        (wholeCoordinatePointValue point stage)
        (rowPrime row) (rowExponent row) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff
    (wholeCoordinatePointValue point stage)).2
  exact ⟨quotientCoordinatePointValue point stage row,
    (pointValue_primePower_landing point stage row).symm⟩

theorem restrictedPoint_successor (stage : Nat) :
    restrictedPoint point (stage + 1) ≫
        localWholeRelationSuccessorMap stage =
      restrictedPoint point stage := by
  unfold restrictedPoint
  rw [Category.assoc, globalToLocalWholeRelationMap_successor]

theorem wholeCoordinatePointMap_successor (stage : Nat) :
    wholeCoordinatePointMap point (stage + 1) ≫
        localScalarInnerSuccessorMap stage =
      wholeCoordinatePointMap point stage := by
  unfold wholeCoordinatePointMap
  rw [Category.assoc,
    ← localWholeAntiInvariantCoordinateMap_successor_square]
  rw [← Category.assoc, restrictedPoint_successor]

theorem wholeCoordinatePointValue_successor (stage : Nat) :
    localScalarInnerSuccessor stage
        (wholeCoordinatePointValue point (stage + 1)) =
      wholeCoordinatePointValue point stage := by
  have square := congrArg
    (fun map => (map.f 0).hom localIntegralUnitGenerator)
    (wholeCoordinatePointMap_successor point stage)
  change localScalarInnerSuccessor stage
      (wholeCoordinatePointValue point (stage + 1)) =
    wholeCoordinatePointValue point stage
  change localScalarInnerSuccessor stage
      (((wholeCoordinatePointMap point (stage + 1)).f 0).hom
        localIntegralUnitGenerator) =
    ((wholeCoordinatePointMap point stage).f 0).hom
      localIntegralUnitGenerator
  have successorApply (value : LocalScalarInner (stage + 1)) :
      ((localScalarInnerSuccessorMap stage).f 0).hom value =
        localScalarInnerSuccessor stage value := by
    rfl
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at square
  rw [successorApply] at square
  exact square

end
end CanonicalUnitArithmeticActionCofiberCyclePrimePowerSplice
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
