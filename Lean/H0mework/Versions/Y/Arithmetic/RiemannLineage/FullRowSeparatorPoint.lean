import H0mework.Versions.Y.Arithmetic.RiemannLineage.DerivedFullRowLineage
import H0mework.Versions.Y.Arithmetic.RiemannLineage.FullRowCaps

/-!
# The local full-row q-rich separator point

The complete q-rich derived datum is lifted through the horizontal mapping
cocone and transposed by the generated total-fibre isomorphism.  Its C
coordinate is exactly the actual quotient cap, and the source-owned left
orientation has a provably nonzero C coordinate.  This is a local separator,
not yet an integral/global descent or a fixedness theorem.
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
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CochainMappingCoconeMappedBoundaryAtomOver

noncomputable section

theorem localQRichDerivedPoint_fullRowHorizontalMap_fst_zero
    (stage : Nat) (base : BlockDualBase) :
    (localQRichDerivedPoint stage base ≫ fullRowHorizontalMap stage) ≫
        CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage) = 0 := by
  calc
    (localQRichDerivedPoint stage base ≫ fullRowHorizontalMap stage) ≫
        CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage) =
      localQRichDerivedPoint stage base ≫
        (fullRowHorizontalMap stage ≫
          CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap stage)) := Category.assoc _ _ _
    _ = localQRichDerivedPoint stage base ≫
        (CochainComplex.mappingCocone.fst
            (localTotalInclusion stage) ≫
          blockQuotientFamilyMap stage) := by
      rw [show fullRowHorizontalMap stage ≫
          CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap stage) =
        CochainComplex.mappingCocone.fst
            (localTotalInclusion stage) ≫
          blockQuotientFamilyMap stage by
        exact CochainMappingCoconeHomotopyFunctoriality.mappingCoconeMap_fst
          (localTotalInclusion stage) (blockPrimePowerFamilyMap stage)
          (blockQuotientFamilyMap stage)
          (localTotalEndpointProjection stage ≫ blockWholeFamilyMap stage)
          (fullRowDerivedSquare stage).square]
    _ = localDerivedStrictSource stage
          (localQRichDerivedPoint stage base) ≫
        blockQuotientFamilyMap stage := by
      simp only [localDerivedStrictSource, Category.assoc]
    _ = 0 := by
      rw [localQRichDerivedPoint_strictSource_zero, Limits.zero_comp]

noncomputable def fullRowShiftedCap (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-1) :=
  (Cochain.ofHom (point ≫ fullRowHorizontalMap stage)).comp
    (CochainComplex.mappingCocone.snd
      (blockPrimePowerFamilyMap stage)) (zero_add (-1))

theorem fullRowShiftedCap_eq (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    fullRowShiftedCap stage point =
      rawFamilyCap stage point (blockWholeFamilyMap stage) +
        sourceFamilyCorrectionCap stage point := by
  unfold fullRowShiftedCap
  rw [Cochain.ofHom_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain,
    fullRowHorizontalMap_snd, Cochain.comp_add]
  unfold rawFamilyCap sourceFamilyCorrectionCap
  unfold localDerivedEndpointCochain localDerivedStrictSource
  simp only [Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain]

theorem fullRowShiftedCap_eq_primePowerRawQuotient (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    fullRowShiftedCap stage point =
      rawFamilyPrimePowerQuotientCap stage point := by
  rw [fullRowShiftedCap_eq]
  have relation := rawFamilyCap_row stage point
  apply sub_eq_zero.mp
  calc
    (rawFamilyCap stage point (blockWholeFamilyMap stage) +
          sourceFamilyCorrectionCap stage point) -
        rawFamilyPrimePowerQuotientCap stage point =
      rawFamilyCap stage point (blockWholeFamilyMap stage) -
          rawFamilyPrimePowerQuotientCap stage point +
        sourceFamilyCorrectionCap stage point := by abel
    _ = 0 := relation

theorem localQRichDerivedPoint_fullRowHorizontalMap_cochain
    (stage : Nat) (base : BlockDualBase) :
    Cochain.ofHom
        (localQRichDerivedPoint stage base ≫ fullRowHorizontalMap stage) =
      (rawFamilyPrimePowerQuotientCap stage
        (localQRichDerivedPoint stage base)).comp
          (CochainComplex.mappingCocone.inr
            (blockPrimePowerFamilyMap stage)).1 (by omega) := by
  ext source : 1
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext
    (blockPrimePowerFamilyMap stage) source
  · have fstDegree := congrArg (fun arrow => arrow.f source)
      (localQRichDerivedPoint_fullRowHorizontalMap_fst_zero stage base)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      at fstDegree
    simpa [Cochain.comp_v] using fstDegree
  · have shifted := Cochain.congr_v
      (fullRowShiftedCap_eq_primePowerRawQuotient stage
        (localQRichDerivedPoint stage base))
      source (source + (-1)) rfl
    simpa [fullRowShiftedCap, Cochain.comp_v] using shifted

theorem qRichFullRowOuterShift_compatibility (stage : Nat)
    (base : BlockDualBase) :
    δ (-1) 0 (qRichFullRowOuterShift stage base) +
        Cochain.ofHom
          (localQRichDerivedPoint stage base ≫
            fullRowHorizontalMap stage) = 0 := by
  rw [qRichFullRowOuterShift_delta,
    localQRichDerivedPoint_fullRowHorizontalMap_cochain]
  exact neg_add_cancel _

noncomputable def qRichFullRowOuterPoint (stage : Nat)
    (base : BlockDualBase) :
    ScalarSingleOne (R := BlockCoordinateRing) ⟶
      (fullRowDerivedSquare stage).horizontalTotal := by
  change ScalarSingleOne (R := BlockCoordinateRing) ⟶
    CochainComplex.mappingCocone (fullRowHorizontalMap stage)
  exact CochainComplex.mappingCocone.lift
    (fullRowHorizontalMap stage)
    (localQRichDerivedPoint stage base)
    (qRichFullRowOuterShift stage base)
    (qRichFullRowOuterShift_compatibility stage base)

noncomputable def qRichFullRowTransposedPoint (stage : Nat)
    (base : BlockDualBase) :
    ScalarSingleOne (R := BlockCoordinateRing) ⟶
      (fullRowDerivedSquare stage).verticalTotal :=
  qRichFullRowOuterPoint stage base ≫
    (fullRowDerivedSquare stage).generatedTotalIso.hom

theorem qRichFullRowOuterPoint_fst (stage : Nat)
    (base : BlockDualBase) :
    qRichFullRowOuterPoint stage base ≫
        CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) =
      localQRichDerivedPoint stage base := by
  change CochainComplex.mappingCocone.lift
      (fullRowHorizontalMap stage)
      (localQRichDerivedPoint stage base)
      (qRichFullRowOuterShift stage base)
      (qRichFullRowOuterShift_compatibility stage base) ≫
    CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) = _
  simp

theorem qRichFullRowOuterPoint_snd (stage : Nat)
    (base : BlockDualBase) (degree previous : ℤ)
    (degreePrevious : degree + (-1) = previous) :
    (qRichFullRowOuterPoint stage base).f degree ≫
        (CochainComplex.mappingCocone.snd
          (fullRowHorizontalMap stage)).v
            degree previous degreePrevious =
      (qRichFullRowOuterShift stage base).v
        degree previous degreePrevious := by
  change (CochainComplex.mappingCocone.lift
      (fullRowHorizontalMap stage)
      (localQRichDerivedPoint stage base)
      (qRichFullRowOuterShift stage base)
      (qRichFullRowOuterShift_compatibility stage base)).f degree ≫
    (CochainComplex.mappingCocone.snd
      (fullRowHorizontalMap stage)).v
        degree previous degreePrevious = _
  simp

/-- Total-fibre transposition exposes the actual q cap as its C coordinate. -/
theorem qRichFullRowTransposedPoint_C (stage : Nat)
    (base : BlockDualBase) (degree previous : ℤ)
    (degreePrevious : degree + (-1) = previous) :
    (qRichFullRowTransposedPoint stage base).f degree ≫
        (CochainComplex.mappingCocone.fst
          (CochainMappingCoconeTotalFiberSymmetry.verticalMap
            (fullRowDerivedSquare stage).horizontalSource
            (fullRowDerivedSquare stage).horizontalTarget
            (fullRowDerivedSquare stage).verticalLeft
            (fullRowDerivedSquare stage).verticalRight
            (fullRowDerivedSquare stage).square)).f degree ≫
      (CochainComplex.mappingCocone.snd
        (fullRowDerivedSquare stage).verticalLeft).v
          degree previous degreePrevious =
    (qRichFullRowQuotientCap stage base).v
      degree previous degreePrevious := by
  subst previous
  simp only [qRichFullRowTransposedPoint, HomologicalComplex.comp_f,
    Category.assoc,
    CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.generatedTotalIso_hom_f,
    CochainMappingCoconeTotalFiberSymmetry.transposeComponent_C]
  rw [← Category.assoc]
  rw [qRichFullRowOuterPoint_snd]
  have qCoordinate := Cochain.congr_v
    (qRichFullRowOuterShift_comp_fst stage base)
    degree (degree + (-1)) rfl
  simpa [Cochain.comp_v] using qCoordinate

theorem qRichFullRowQuotientCap_left_ne_zero (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    qRichFullRowQuotientCap stage blockLeftEndpointBase ≠ 0 := by
  intro capZero
  have componentZero := Cochain.congr_v capZero 1 0 (by omega)
  have generatorZero := ConcreteCategory.congr_hom componentZero
    scalarSingleOneGenerator
  have rowZero := congrFun generatorZero row
  have coordinateZero := congrFun rowZero (row.1, 0)
  change blockQuotientFamilyProjection stage
      ((localDerivedEndpointCochain stage
        (localQRichDerivedPoint stage blockLeftEndpointBase)).v
          1 0 (by omega) scalarSingleOneGenerator) row (row.1, 0) = 0
    at coordinateZero
  rw [localQRichDerivedPoint,
    localCorrectedEndpoint_endpointCochain, map_neg] at coordinateZero
  change -blockQuotientAntiInvariantProjection stage row
      (blockQRichEndpointVertexMap stage blockLeftEndpointBase)
        (row.1, 0) = 0 at coordinateZero
  rw [blockQRichEndpoint_quotientAntiInvariant] at coordinateZero
  simp [blockLeftEndpointBase] at coordinateZero
  have quotientCastNe :
      (quotientCoefficient row : BlockCoordinateRing) ≠ 0 := by
    change MvPolynomial.C ((quotientCoefficient row : Nat) : ℤ) ≠ 0
    rw [MvPolynomial.C_ne_zero]
    exact_mod_cast blockQRichQuotientCoefficient_ne_zero stage row
  exact quotientCastNe coordinateZero

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
