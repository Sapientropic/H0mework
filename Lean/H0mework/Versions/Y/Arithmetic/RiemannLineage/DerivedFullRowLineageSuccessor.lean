import H0mework.Versions.Y.Arithmetic.RiemannLineage.DerivedFullRowLineageOuterSuccessor

/-!
# Successor of the bundled q-rich outer and transposed points

The upper and lower successor faces assemble the bundled outer point into the
actual full-row cube.  Naturality of canonical total-fibre transposition then
generates the strict successor theorem for the q-rich transposed point.
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
open CochainMappingCoconeFunctoriality
open CochainMappingCoconeTotalFiberSymmetry
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom

noncomputable section

theorem fullRowUpperTransition_eq_localCorrectedEndpointRestriction
    (stage : Nat) :
    (fullRowDerivedCube stage).upperTransition =
      localCorrectedEndpointRestriction stage := by
  rfl

theorem fullRowHorizontalTotalTransition_fst (stage : Nat) :
    (fullRowDerivedCube stage).horizontalTotalTransition ≫
        CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) =
      CochainComplex.mappingCocone.fst
          (fullRowHorizontalMap (stage + 1)) ≫
        (fullRowDerivedCube stage).upperTransition := by
  unfold CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.horizontalTotalTransition
  exact CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
    (fullRowHorizontalMap (stage + 1))
    (fullRowHorizontalMap stage)
    (fullRowDerivedCube stage).upperTransition
    (fullRowDerivedCube stage).lowerTransition
    (fullRowDerivedCube stage).horizontalMapSquare

theorem fullRowHorizontalTotalTransition_snd (stage : Nat) :
    (Cochain.ofHom
        (fullRowDerivedCube stage).horizontalTotalTransition).comp
      (CochainComplex.mappingCocone.snd (fullRowHorizontalMap stage))
        (zero_add (-1)) =
      (CochainComplex.mappingCocone.snd
          (fullRowHorizontalMap (stage + 1))).comp
        (Cochain.ofHom (fullRowDerivedCube stage).lowerTransition)
          (add_zero (-1)) := by
  unfold CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.horizontalTotalTransition
  exact CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
    (fullRowHorizontalMap (stage + 1))
    (fullRowHorizontalMap stage)
    (fullRowDerivedCube stage).upperTransition
    (fullRowDerivedCube stage).lowerTransition
    (fullRowDerivedCube stage).horizontalMapSquare

/-- The universal q-rich outer point is a strict component of the actual
successor cube. -/
theorem qRichLineageFullRowOuterPoint_successor (stage : Nat) :
    qRichLineageFullRowOuterPoint (stage + 1) ≫
        (fullRowDerivedCube stage).horizontalTotalTransition =
      qRichLineageSingleOneRestriction stage ≫
        qRichLineageFullRowOuterPoint stage := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext
    (fullRowHorizontalMap stage) degree
  · have generated :
        (qRichLineageFullRowOuterPoint (stage + 1) ≫
            (fullRowDerivedCube stage).horizontalTotalTransition) ≫
          CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) =
        (qRichLineageSingleOneRestriction stage ≫
            qRichLineageFullRowOuterPoint stage) ≫
          CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) := by
      calc
        (qRichLineageFullRowOuterPoint (stage + 1) ≫
            (fullRowDerivedCube stage).horizontalTotalTransition) ≫
          CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) =
          qRichLineageFullRowOuterPoint (stage + 1) ≫
            ((fullRowDerivedCube stage).horizontalTotalTransition ≫
              CochainComplex.mappingCocone.fst
                (fullRowHorizontalMap stage)) := Category.assoc _ _ _
        _ = qRichLineageFullRowOuterPoint (stage + 1) ≫
            (CochainComplex.mappingCocone.fst
                (fullRowHorizontalMap (stage + 1)) ≫
              (fullRowDerivedCube stage).upperTransition) := by
          rw [fullRowHorizontalTotalTransition_fst]
        _ = (qRichLineageFullRowOuterPoint (stage + 1) ≫
              CochainComplex.mappingCocone.fst
                (fullRowHorizontalMap (stage + 1))) ≫
            (fullRowDerivedCube stage).upperTransition :=
          (Category.assoc _ _ _).symm
        _ = qRichDerivedLineagePoint (stage + 1) ≫
            (fullRowDerivedCube stage).upperTransition := by
          rw [qRichLineageFullRowOuterPoint_fst]
        _ = qRichDerivedLineagePoint (stage + 1) ≫
            localCorrectedEndpointRestriction stage := by
          rw [fullRowUpperTransition_eq_localCorrectedEndpointRestriction]
        _ = qRichLineageSingleOneRestriction stage ≫
            qRichDerivedLineagePoint stage :=
          qRichDerivedLineagePoint_successor stage
        _ = qRichLineageSingleOneRestriction stage ≫
            (qRichLineageFullRowOuterPoint stage ≫
              CochainComplex.mappingCocone.fst
                (fullRowHorizontalMap stage)) := by
          rw [qRichLineageFullRowOuterPoint_fst]
        _ = (qRichLineageSingleOneRestriction stage ≫
              qRichLineageFullRowOuterPoint stage) ≫
            CochainComplex.mappingCocone.fst
              (fullRowHorizontalMap stage) :=
          (Category.assoc _ _ _).symm
    exact congrArg (fun arrow => arrow.f degree) generated
  · let previous := degree + (-1)
    have transitionSnd := Cochain.congr_v
      (fullRowHorizontalTotalTransition_snd stage)
      degree previous rfl
    have transitionSndComponent :
        (fullRowDerivedCube stage).horizontalTotalTransition.f degree ≫
            (CochainComplex.mappingCocone.snd
              (fullRowHorizontalMap stage)).v degree previous rfl =
          (CochainComplex.mappingCocone.snd
              (fullRowHorizontalMap (stage + 1))).v
                degree previous rfl ≫
            (fullRowDerivedCube stage).lowerTransition.f previous := by
      simpa [Cochain.comp_v] using transitionSnd
    have highOuter := qRichLineageFullRowOuterPoint_snd
      (stage + 1) degree previous rfl
    have lowOuter := qRichLineageFullRowOuterPoint_snd
      stage degree previous rfl
    have shiftSuccessor := Cochain.congr_v
      (qRichLineageFullRowOuterShift_successor stage)
      degree previous rfl
    have shiftSuccessorComponent :
        (qRichLineageFullRowOuterShift (stage + 1)).v
              degree previous rfl ≫
            (fullRowDerivedCube stage).lowerTransition.f previous =
          (qRichLineageSingleOneRestriction stage).f degree ≫
            (qRichLineageFullRowOuterShift stage).v
              degree previous rfl := by
      simpa [Cochain.comp_zero_cochain_v,
        Cochain.zero_cochain_comp_v] using shiftSuccessor
    simp only [HomologicalComplex.comp_f]
    calc
      ((qRichLineageFullRowOuterPoint (stage + 1)).f degree ≫
          (fullRowDerivedCube stage).horizontalTotalTransition.f degree) ≫
        (CochainComplex.mappingCocone.snd
          (fullRowHorizontalMap stage)).v degree previous rfl =
        (qRichLineageFullRowOuterPoint (stage + 1)).f degree ≫
          ((fullRowDerivedCube stage).horizontalTotalTransition.f degree ≫
            (CochainComplex.mappingCocone.snd
              (fullRowHorizontalMap stage)).v degree previous rfl) :=
        Category.assoc _ _ _
      _ = (qRichLineageFullRowOuterPoint (stage + 1)).f degree ≫
          ((CochainComplex.mappingCocone.snd
              (fullRowHorizontalMap (stage + 1))).v
                degree previous rfl ≫
            (fullRowDerivedCube stage).lowerTransition.f previous) := by
        rw [transitionSndComponent]
      _ = ((qRichLineageFullRowOuterPoint (stage + 1)).f degree ≫
            (CochainComplex.mappingCocone.snd
              (fullRowHorizontalMap (stage + 1))).v
                degree previous rfl) ≫
          (fullRowDerivedCube stage).lowerTransition.f previous :=
        (Category.assoc _ _ _).symm
      _ = (qRichLineageFullRowOuterShift (stage + 1)).v
            degree previous rfl ≫
          (fullRowDerivedCube stage).lowerTransition.f previous := by
        rw [highOuter]
      _ = (qRichLineageSingleOneRestriction stage).f degree ≫
          (qRichLineageFullRowOuterShift stage).v
            degree previous rfl := shiftSuccessorComponent
      _ = (qRichLineageSingleOneRestriction stage).f degree ≫
          ((qRichLineageFullRowOuterPoint stage).f degree ≫
            (CochainComplex.mappingCocone.snd
              (fullRowHorizontalMap stage)).v degree previous rfl) := by
        rw [lowOuter]
      _ = ((qRichLineageSingleOneRestriction stage).f degree ≫
          (qRichLineageFullRowOuterPoint stage).f degree) ≫
        (CochainComplex.mappingCocone.snd
          (fullRowHorizontalMap stage)).v degree previous rfl :=
        (Category.assoc _ _ _).symm

/-- The q-rich transposed point is the strict generated component of the
actual successor cube.  The factorial scale remains on its source line. -/
theorem qRichLineageFullRowTransposedPoint_successor (stage : Nat) :
    qRichLineageFullRowTransposedPoint (stage + 1) ≫
        (fullRowDerivedCube stage).verticalTotalTransition =
      qRichLineageSingleOneRestriction stage ≫
        qRichLineageFullRowTransposedPoint stage := by
  unfold qRichLineageFullRowTransposedPoint
  calc
    (qRichLineageFullRowOuterPoint (stage + 1) ≫
        (fullRowDerivedSquare (stage + 1)).generatedTotalIso.hom) ≫
      (fullRowDerivedCube stage).verticalTotalTransition =
      qRichLineageFullRowOuterPoint (stage + 1) ≫
        ((fullRowDerivedSquare (stage + 1)).generatedTotalIso.hom ≫
          (fullRowDerivedCube stage).verticalTotalTransition) :=
      Category.assoc _ _ _
    _ = qRichLineageFullRowOuterPoint (stage + 1) ≫
        ((fullRowDerivedCube stage).horizontalTotalTransition ≫
          (fullRowDerivedSquare stage).generatedTotalIso.hom) := by
      rw [fullRowGeneratedTotalIso_naturality]
    _ = (qRichLineageFullRowOuterPoint (stage + 1) ≫
          (fullRowDerivedCube stage).horizontalTotalTransition) ≫
        (fullRowDerivedSquare stage).generatedTotalIso.hom :=
      (Category.assoc _ _ _).symm
    _ = (qRichLineageSingleOneRestriction stage ≫
          qRichLineageFullRowOuterPoint stage) ≫
        (fullRowDerivedSquare stage).generatedTotalIso.hom := by
      rw [qRichLineageFullRowOuterPoint_successor]
    _ = qRichLineageSingleOneRestriction stage ≫
        (qRichLineageFullRowOuterPoint stage ≫
          (fullRowDerivedSquare stage).generatedTotalIso.hom) :=
      Category.assoc _ _ _

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

