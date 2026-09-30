import H0mework.Versions.Y.Arithmetic.RiemannLineage.DerivedLineagePoint
import H0mework.Versions.Y.Arithmetic.RiemannLineage.FullRowSuccessor

/-!
# The q-rich derived lineage on the full factor-row total fibre

This module lifts the complete q-rich source line through the all-row square.
The quotient cap is generated before specialization and the outer equation is
inhomogeneous: its coboundary cancels the actual horizontal image.  The
construction therefore retains a literal nonzero q coordinate instead of
asking a closed homogeneous shift to create one.
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

/-- Read one row-family coordinate from the universal q-rich endpoint
cochain. -/
noncomputable def qRichLineageFamilyCap (stage : Nat)
    (coordinate : LocalWholeComplex stage ⟶ blockRowFamilySingle stage) :
    Cochain QRichLineageSingleOne (blockRowFamilySingle stage) (-1) :=
  (qRichLineageEndpointCochain stage).comp
    (Cochain.ofHom
      (localTotalEndpointProjection stage ≫ coordinate))
    (add_zero (-1))

/-- The total-fibre readback of the universal endpoint cochain is literally
the negative strict q-rich endpoint. -/
theorem qRichLineageEndpointCochain_readback (stage : Nat) :
    (qRichLineageEndpointCochain stage).comp
        (Cochain.ofHom (localTotalEndpointProjection stage))
          (add_zero (-1)) =
      Cochain.fromSingleMk
        (-ModuleCat.ofHom (blockQRichEndpointVertexMap stage))
        (show (1 : ℤ) + (-1) = 0 by omega) := by
  have sectionDegree := congrArg (fun arrow => arrow.f 0)
    (localTotalEndpointProjection_section stage)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    at sectionDegree
  unfold qRichLineageEndpointCochain qRichLineageTotalEndpointMap
  rw [← Cochain.fromSingleMk_postcomp]
  rw [Preadditive.neg_comp, Category.assoc, sectionDegree]
  have generator :
      -(ModuleCat.ofHom (blockQRichEndpointVertexMap stage) ≫
          𝟙 (BlockDirectObject seedOccurrence.root stage 0)) =
        -ModuleCat.ofHom (blockQRichEndpointVertexMap stage) :=
    congrArg Neg.neg (Category.comp_id _)
  rw [generator]

theorem qRichLineageFamilyCap_eq_fromSingle (stage : Nat)
    (coordinate : LocalWholeComplex stage ⟶ blockRowFamilySingle stage) :
    qRichLineageFamilyCap stage coordinate =
      Cochain.fromSingleMk
        (-(ModuleCat.ofHom (blockQRichEndpointVertexMap stage) ≫
          coordinate.f 0)) (show (1 : ℤ) + (-1) = 0 by omega) := by
  unfold qRichLineageFamilyCap
  rw [Cochain.ofHom_comp]
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain]
  rw [qRichLineageEndpointCochain_readback]
  rw [← Cochain.fromSingleMk_postcomp, Preadditive.neg_comp]

/-- The strict q-rich endpoint satisfies the all-row landing equation as an
actual degree-zero map. -/
theorem blockQRichEndpoint_family_landing (stage : Nat) :
    ModuleCat.ofHom (blockQRichEndpointVertexMap stage) ≫
        (blockWholeFamilyMap stage).f 0 =
      (ModuleCat.ofHom (blockQRichEndpointVertexMap stage) ≫
        (blockQuotientFamilyMap stage).f 0) ≫
          (blockPrimePowerFamilyMap stage).f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro base
  funext row index
  have generated := congrFun
    (congrFun (blockQRichEndpointVertexMap_differential_zero stage base) row)
    index
  change
    blockInnerAntiInvariant seedOccurrence.root stage
        ((blockQRichEndpointVertexMap stage base) none) index =
      (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) *
        blockInnerAntiInvariant seedOccurrence.root stage
          ((blockQRichEndpointVertexMap stage base) (some row)) index
  change
    blockInnerAntiInvariant seedOccurrence.root stage
          ((blockQRichEndpointVertexMap stage base) none) index -
        (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) *
          blockInnerAntiInvariant seedOccurrence.root stage
            ((blockQRichEndpointVertexMap stage base) (some row)) index = 0
    at generated
  exact sub_eq_zero.mp generated

noncomputable def qRichLineageFullRowQuotientCap (stage : Nat) :
    Cochain QRichLineageSingleOne (blockRowFamilySingle stage) (-1) :=
  qRichLineageFamilyCap stage (blockQuotientFamilyMap stage)

noncomputable def qRichLineageFullRowWholeCap (stage : Nat) :
    Cochain QRichLineageSingleOne (blockRowFamilySingle stage) (-1) :=
  qRichLineageFamilyCap stage (blockWholeFamilyMap stage)

noncomputable def qRichLineageFullRowPrimePowerCap (stage : Nat) :
    Cochain QRichLineageSingleOne (blockRowFamilySingle stage) (-1) :=
  (qRichLineageFullRowQuotientCap stage).comp
    (Cochain.ofHom (blockPrimePowerFamilyMap stage)) (add_zero (-1))

theorem qRichLineageFullRowQuotientCap_delta (stage : Nat) :
    δ (-1) 0 (qRichLineageFullRowQuotientCap stage) = 0 := by
  unfold qRichLineageFullRowQuotientCap qRichLineageFamilyCap
  rw [δ_comp_ofHom, qRichLineageEndpointCochain_delta,
    Cochain.zero_comp]

/-- Whole and prime-power-scaled quotient caps coincide before any point
specialization. -/
theorem qRichLineageFullRowWholeCap_eq_primePower (stage : Nat) :
    qRichLineageFullRowWholeCap stage =
      qRichLineageFullRowPrimePowerCap stage := by
  rw [qRichLineageFullRowWholeCap,
    qRichLineageFamilyCap_eq_fromSingle]
  unfold qRichLineageFullRowPrimePowerCap
  rw [qRichLineageFullRowQuotientCap,
    qRichLineageFamilyCap_eq_fromSingle]
  rw [← Cochain.fromSingleMk_postcomp]
  rw [Preadditive.neg_comp,
    ← blockQRichEndpoint_family_landing]

/-- The map between the two first-level total fibres in the all-row square. -/
noncomputable abbrev fullRowHorizontalMap (stage : Nat) :
    CochainComplex.mappingCocone
        (fullRowDerivedSquare stage).horizontalSource ⟶
      CochainComplex.mappingCocone
        (fullRowDerivedSquare stage).horizontalTarget :=
  CochainMappingCoconeTotalFiberSymmetry.horizontalMap
    (fullRowDerivedSquare stage).horizontalSource
    (fullRowDerivedSquare stage).horizontalTarget
    (fullRowDerivedSquare stage).verticalLeft
    (fullRowDerivedSquare stage).verticalRight
    (fullRowDerivedSquare stage).square

theorem fullRowHorizontalMap_snd (stage : Nat) :
    (Cochain.ofHom (fullRowHorizontalMap stage)).comp
        (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap stage)) (zero_add (-1)) =
      (CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).comp
          (Cochain.ofHom
            (localTotalEndpointProjection stage ≫
              blockWholeFamilyMap stage)) (add_zero (-1)) +
        (Cochain.ofHom
          (CochainComplex.mappingCocone.fst
            (localTotalInclusion stage))).comp
          (Cochain.ofHomotopy
            (blockFactorizationFamilyHomotopy stage))
          (add_zero (-1)) := by
  unfold fullRowHorizontalMap
  unfold CochainMappingCoconeTotalFiberSymmetry.horizontalMap
  rw [CochainMappingCoconeHomotopyFunctoriality.mappingCoconeMap_snd,
    fullRowDerivedSquare_cochain,
    blockFactorizationFamilyHomotopy_cochain]
  simp

theorem qRichDerivedLineagePoint_endpointCochain (stage : Nat) :
    (Cochain.ofHom (qRichDerivedLineagePoint stage)).comp
        (CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)) (zero_add (-1)) =
      qRichLineageEndpointCochain stage := by
  unfold qRichDerivedLineagePoint
  rw [CochainComplex.mappingCocone.ofHom_lift,
    CochainComplex.mappingCocone.liftCochain_comp_snd]

theorem qRichDerivedLineagePoint_fstCochain_zero (stage : Nat) :
    (Cochain.ofHom (qRichDerivedLineagePoint stage)).comp
        (Cochain.ofHom (CochainComplex.mappingCocone.fst
          (localTotalInclusion stage))) (zero_add 0) = 0 := by
  rw [← Cochain.ofHom_comp, qRichDerivedLineagePoint_fst,
    Cochain.ofHom_zero]

theorem qRichDerivedLineagePoint_fullRowHorizontalMap_fst_zero
    (stage : Nat) :
    (qRichDerivedLineagePoint stage ≫ fullRowHorizontalMap stage) ≫
        CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage) = 0 := by
  calc
    (qRichDerivedLineagePoint stage ≫ fullRowHorizontalMap stage) ≫
        CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage) =
      qRichDerivedLineagePoint stage ≫
        (fullRowHorizontalMap stage ≫
          CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap stage)) := Category.assoc _ _ _
    _ = qRichDerivedLineagePoint stage ≫
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
    _ = (qRichDerivedLineagePoint stage ≫
          CochainComplex.mappingCocone.fst
            (localTotalInclusion stage)) ≫
        blockQuotientFamilyMap stage := (Category.assoc _ _ _).symm
    _ = 0 := by rw [qRichDerivedLineagePoint_fst, Limits.zero_comp]

noncomputable def qRichLineageFullRowShiftedCap (stage : Nat) :
    Cochain QRichLineageSingleOne (blockRowFamilySingle stage) (-1) :=
  (Cochain.ofHom
      (qRichDerivedLineagePoint stage ≫ fullRowHorizontalMap stage)).comp
    (CochainComplex.mappingCocone.snd
      (blockPrimePowerFamilyMap stage)) (zero_add (-1))

theorem qRichLineageFullRowShiftedCap_eq_whole (stage : Nat) :
    qRichLineageFullRowShiftedCap stage =
      qRichLineageFullRowWholeCap stage := by
  have endpointCoordinate :
      (Cochain.ofHom (qRichDerivedLineagePoint stage)).comp
          ((CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).comp
              (Cochain.ofHom
                (localTotalEndpointProjection stage ≫
                  blockWholeFamilyMap stage)) (add_zero (-1)))
          (zero_add (-1)) =
        (qRichLineageEndpointCochain stage).comp
          (Cochain.ofHom
            (localTotalEndpointProjection stage ≫
              blockWholeFamilyMap stage)) (add_zero (-1)) := by
    rw [← Cochain.comp_assoc_of_third_is_zero_cochain,
      qRichDerivedLineagePoint_endpointCochain]
  have strictCoordinate :
      (Cochain.ofHom (qRichDerivedLineagePoint stage)).comp
          ((Cochain.ofHom (CochainComplex.mappingCocone.fst
            (localTotalInclusion stage))).comp
              (Cochain.ofHomotopy
                (blockFactorizationFamilyHomotopy stage))
              (add_zero (-1)))
          (zero_add (-1)) = 0 := by
    rw [← Cochain.comp_assoc_of_second_is_zero_cochain,
      qRichDerivedLineagePoint_fstCochain_zero,
      Cochain.zero_comp]
  unfold qRichLineageFullRowShiftedCap
  rw [Cochain.ofHom_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain,
    fullRowHorizontalMap_snd, Cochain.comp_add]
  unfold qRichLineageFullRowWholeCap qRichLineageFamilyCap
  rw [endpointCoordinate, strictCoordinate, add_zero]

theorem qRichLineageFullRowShiftedCap_eq_primePower (stage : Nat) :
    qRichLineageFullRowShiftedCap stage =
      qRichLineageFullRowPrimePowerCap stage := by
  rw [qRichLineageFullRowShiftedCap_eq_whole,
    qRichLineageFullRowWholeCap_eq_primePower]

/-- The horizontal image has zero first coordinate and its shifted coordinate
is exactly the actual prime-power-scaled q cap. -/
theorem qRichDerivedLineagePoint_fullRowHorizontalMap_cochain
    (stage : Nat) :
    Cochain.ofHom
        (qRichDerivedLineagePoint stage ≫ fullRowHorizontalMap stage) =
      (qRichLineageFullRowPrimePowerCap stage).comp
        (CochainComplex.mappingCocone.inr
          (blockPrimePowerFamilyMap stage)).1 (by omega) := by
  ext source : 1
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext
    (blockPrimePowerFamilyMap stage) source
  · have fstDegree := congrArg (fun arrow => arrow.f source)
      (qRichDerivedLineagePoint_fullRowHorizontalMap_fst_zero stage)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      at fstDegree
    simpa [Cochain.comp_v] using fstDegree
  · have shifted := Cochain.congr_v
      (qRichLineageFullRowShiftedCap_eq_primePower stage)
      source (source + (-1)) rfl
    simpa [qRichLineageFullRowShiftedCap, Cochain.comp_v] using shifted

/-- The universal outer shift has the actual q cap as first coordinate. -/
noncomputable def qRichLineageFullRowOuterShift (stage : Nat) :
    Cochain QRichLineageSingleOne
      (CochainComplex.mappingCocone (blockPrimePowerFamilyMap stage)) (-1) :=
  CochainComplex.mappingCocone.liftCochain
    (blockPrimePowerFamilyMap stage)
    (qRichLineageFullRowQuotientCap stage)
    (0 : Cochain QRichLineageSingleOne
      (blockRowFamilySingle stage) (-2)) (by omega)

theorem qRichLineageFullRowOuterShift_comp_fst (stage : Nat) :
    (qRichLineageFullRowOuterShift stage).comp
        (Cochain.ofHom (CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage))) (add_zero (-1)) =
      qRichLineageFullRowQuotientCap stage := by
  exact CochainComplex.mappingCocone.liftCochain_comp_fst
    (blockPrimePowerFamilyMap stage)
    (qRichLineageFullRowQuotientCap stage)
    (0 : Cochain QRichLineageSingleOne
      (blockRowFamilySingle stage) (-2)) (by omega)

theorem qRichLineageFullRowOuterShift_comp_snd (stage : Nat) :
    (qRichLineageFullRowOuterShift stage).comp
        (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap stage))
            (show (-1 : ℤ) + (-1) = -2 by omega) =
      (0 : Cochain QRichLineageSingleOne
        (blockRowFamilySingle stage) (-2)) := by
  exact CochainComplex.mappingCocone.liftCochain_comp_snd
    (blockPrimePowerFamilyMap stage)
    (qRichLineageFullRowQuotientCap stage)
    (0 : Cochain QRichLineageSingleOne
      (blockRowFamilySingle stage) (-2)) (by omega)

theorem qRichLineageFullRowOuterShift_delta (stage : Nat) :
    δ (-1) 0 (qRichLineageFullRowOuterShift stage) =
      -(qRichLineageFullRowPrimePowerCap stage).comp
        (CochainComplex.mappingCocone.inr
          (blockPrimePowerFamilyMap stage)).1 (by omega) := by
  unfold qRichLineageFullRowOuterShift
  rw [CochainComplex.mappingCocone.δ_liftCochain
    (blockPrimePowerFamilyMap stage)
    (qRichLineageFullRowQuotientCap stage)
    (0 : Cochain QRichLineageSingleOne
      (blockRowFamilySingle stage) (-2)) (by omega) 0 (by omega)]
  rw [qRichLineageFullRowQuotientCap_delta, δ_zero]
  unfold qRichLineageFullRowPrimePowerCap
  simp

theorem qRichLineageFullRowOuterShift_compatibility (stage : Nat) :
    δ (-1) 0 (qRichLineageFullRowOuterShift stage) +
        Cochain.ofHom
          (qRichDerivedLineagePoint stage ≫
            fullRowHorizontalMap stage) = 0 := by
  rw [qRichLineageFullRowOuterShift_delta,
    qRichDerivedLineagePoint_fullRowHorizontalMap_cochain]
  exact neg_add_cancel _

/-- The universal q-rich outer point.  Unlike the old historical point, its
outer coordinate is inhomogeneous and carries the actual q cap. -/
noncomputable def qRichLineageFullRowOuterPoint (stage : Nat) :
    QRichLineageSingleOne ⟶
      (fullRowDerivedSquare stage).horizontalTotal := by
  change QRichLineageSingleOne ⟶
    CochainComplex.mappingCocone (fullRowHorizontalMap stage)
  exact CochainComplex.mappingCocone.lift
    (fullRowHorizontalMap stage)
    (qRichDerivedLineagePoint stage)
    (qRichLineageFullRowOuterShift stage)
    (qRichLineageFullRowOuterShift_compatibility stage)

noncomputable def qRichLineageFullRowTransposedPoint (stage : Nat) :
    QRichLineageSingleOne ⟶
      (fullRowDerivedSquare stage).verticalTotal :=
  qRichLineageFullRowOuterPoint stage ≫
    (fullRowDerivedSquare stage).generatedTotalIso.hom

theorem qRichLineageFullRowOuterPoint_fst (stage : Nat) :
    qRichLineageFullRowOuterPoint stage ≫
        CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) =
      qRichDerivedLineagePoint stage := by
  change CochainComplex.mappingCocone.lift
      (fullRowHorizontalMap stage)
      (qRichDerivedLineagePoint stage)
      (qRichLineageFullRowOuterShift stage)
      (qRichLineageFullRowOuterShift_compatibility stage) ≫
    CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage) = _
  simp

theorem qRichLineageFullRowOuterPoint_snd (stage : Nat)
    (degree previous : ℤ)
    (degreePrevious : degree + (-1) = previous) :
    (qRichLineageFullRowOuterPoint stage).f degree ≫
        (CochainComplex.mappingCocone.snd
          (fullRowHorizontalMap stage)).v
            degree previous degreePrevious =
      (qRichLineageFullRowOuterShift stage).v
        degree previous degreePrevious := by
  change (CochainComplex.mappingCocone.lift
      (fullRowHorizontalMap stage)
      (qRichDerivedLineagePoint stage)
      (qRichLineageFullRowOuterShift stage)
      (qRichLineageFullRowOuterShift_compatibility stage)).f degree ≫
    (CochainComplex.mappingCocone.snd
      (fullRowHorizontalMap stage)).v
        degree previous degreePrevious = _
  simp

/-- Canonical transposition exposes the actual universal q cap as its C
coordinate. -/
theorem qRichLineageFullRowTransposedPoint_C (stage : Nat)
    (degree previous : ℤ)
    (degreePrevious : degree + (-1) = previous) :
    (qRichLineageFullRowTransposedPoint stage).f degree ≫
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
    (qRichLineageFullRowQuotientCap stage).v
      degree previous degreePrevious := by
  subst previous
  simp only [qRichLineageFullRowTransposedPoint,
    HomologicalComplex.comp_f, Category.assoc,
    CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.generatedTotalIso_hom_f,
    CochainMappingCoconeTotalFiberSymmetry.transposeComponent_C]
  rw [← Category.assoc]
  rw [qRichLineageFullRowOuterPoint_snd]
  have qCoordinate := Cochain.congr_v
    (qRichLineageFullRowOuterShift_comp_fst stage)
    degree (degree + (-1)) rfl
  simpa [Cochain.comp_v] using qCoordinate

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
