import H0mework.Realization.MappingCone.BoundaryAtom
import H0mework.Arithmetic.EulerGlobal.CofiberFamily

/-!
# Evaluation of a zero local coordinate class on an actual cycle

If the whole anti-invariant coordinate map is zero in the hom-complex
cohomology class, it is null-homotopic.  The mapping-cocone universal
property turns any actual local factorization cycle into a source point;
null-homotopy then makes its anti-invariant evaluation literally zero.

This adapter generates neither a cycle nor a coefficient realization.  A
downstream endpoint can use it only after supplying an actual cycle in the
same local scalar complex.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticLocalCoordinateClassCycleEvaluation

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticIntegralActionCofiberFamily
open CategoryTheory
open SaturationMonoid.CochainMappingCoconeMappedBoundaryAtom

noncomputable section

theorem localWholeAntiInvariantClass_zero_homotopy
    (stage : Nat) (classZero : localWholeAntiInvariantClass stage = 0) :
    Nonempty (Homotopy (localWholeAntiInvariantCoordinateMap stage) 0) := by
  change CochainComplex.HomComplex.CohomologyClass.mk
      (CochainComplex.HomComplex.Cocycle.ofHom
        (localWholeAntiInvariantCoordinateMap stage)) = 0 at classZero
  have membership :=
    (CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff _).1
      classZero
  rcases (CochainComplex.HomComplex.mem_coboundaries_iff
      (CochainComplex.HomComplex.Cocycle.ofHom
        (localWholeAntiInvariantCoordinateMap stage)) (-1) (by omega)).1
      membership with ⟨cochain, coboundary⟩
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy
    (localWholeAntiInvariantCoordinateMap stage) 0).symm ⟨cochain, ?_⟩⟩
  change CochainComplex.HomComplex.δ (-1) 0 cochain =
    CochainComplex.HomComplex.Cochain.ofHom
      (localWholeAntiInvariantCoordinateMap stage) at coboundary
  simpa only [CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero] using
    coboundary.symm

abbrev localIntegralUnitSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj IntegralUnit

def localIntegralUnitGenerator : localIntegralUnitSingle.X 0 := by
  exact (HomologicalComplex.singleObjXSelf
    (ComplexShape.up ℤ) 0 IntegralUnit).inv.hom 1

def localScalarVertexElementHom (stage : Nat) (value : LocalScalarVertex stage) :
    IntegralUnit ⟶ LocalScalarVertexObject stage :=
  elementHom value

noncomputable def localScalarVertexPointMap
    (stage : Nat) (value : LocalScalarVertex stage) :
    localIntegralUnitSingle ⟶ localScalarVertexSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (localScalarVertexElementHom stage value)

theorem localScalarVertexPointMap_differential_zero
    (stage : Nat) (value : LocalScalarVertex stage)
    (cycle : localExtendedDifferential stage value = 0) :
    localScalarVertexPointMap stage value ≫
        localScalarDifferentialMap stage = 0 := by
  unfold localScalarVertexPointMap localScalarDifferentialMap
  rw [← Functor.map_comp]
  unfold localScalarVertexElementHom
  rw [elementHom_comp]
  change (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (elementHom
      (M := LocalScalarRelationObject stage)
      (localExtendedDifferential stage value)) = 0
  rw [cycle, elementHom_zero]
  simp

noncomputable def localWholeCyclePointMap
    (stage : Nat) (value : LocalScalarVertex stage)
    (cycle : localExtendedDifferential stage value = 0) :
    localIntegralUnitSingle ⟶ LocalScalarWholeRelationComplex stage :=
  CochainComplex.mappingCocone.lift
    (localScalarDifferentialMap stage)
    (localScalarVertexPointMap stage value) 0 (by
      rw [localScalarVertexPointMap_differential_zero stage value cycle]
      simp)

@[reassoc] theorem localWholeCyclePointMap_fst
    (stage : Nat) (value : LocalScalarVertex stage)
    (cycle : localExtendedDifferential stage value = 0) :
    localWholeCyclePointMap stage value cycle ≫
        CochainComplex.mappingCocone.fst
          (localScalarDifferentialMap stage) =
      localScalarVertexPointMap stage value := by
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

theorem localWholeCyclePointMap_coordinate
    (stage : Nat) (value : LocalScalarVertex stage)
    (cycle : localExtendedDifferential stage value = 0) :
    localWholeCyclePointMap stage value cycle ≫
        localWholeAntiInvariantCoordinateMap stage =
      (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
        (elementHom
          (M := LocalScalarInnerObject stage)
          (localWholeAntiInvariantComponent stage value)) := by
  unfold localWholeAntiInvariantCoordinateMap
  rw [← Category.assoc,
    localWholeCyclePointMap_fst]
  unfold localScalarVertexPointMap localWholeAntiInvariantSingleMap
  rw [← Functor.map_comp]
  apply congrArg
  unfold localScalarVertexElementHom
  rw [elementHom_comp]
  rfl

theorem localWholeAntiInvariantClass_zero_evaluates_cycle
    (stage : Nat) (classZero : localWholeAntiInvariantClass stage = 0)
    (value : LocalScalarVertex stage)
    (cycle : localExtendedDifferential stage value = 0) :
    localWholeAntiInvariantComponent stage value = 0 := by
  obtain ⟨homotopy⟩ :=
    localWholeAntiInvariantClass_zero_homotopy stage classZero
  let point := localWholeCyclePointMap stage value cycle
  have composed := homotopy.compLeft point
  have component := ConcreteCategory.congr_hom (composed.comm 0)
    localIntegralUnitGenerator
  have coordinate := localWholeCyclePointMap_coordinate stage value cycle
  have coordinateAt := congrArg
    (fun arrow => (arrow.f 0).hom localIntegralUnitGenerator) coordinate
  simp only [HomologicalComplex.comp_f] at coordinateAt
  change ((point ≫ localWholeAntiInvariantCoordinateMap stage).f 0).hom
      localIntegralUnitGenerator = _ at coordinateAt
  rw [coordinateAt] at component
  simp [dNext, prevD, localIntegralUnitSingle,
    localIntegralUnitGenerator, localScalarInnerSingle,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self] at component
  rw [elementHom_one] at component
  have transported := congrArg
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (LocalScalarInnerObject stage)).hom.hom component
  simpa using transported

end
end CanonicalUnitArithmeticLocalCoordinateClassCycleEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
