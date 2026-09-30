import H0mework.Arithmetic.RiemannLineage.DerivedFullRowLineage

/-!
# Successor of the bundled q-rich caps and outer shift

The factorial source transition, actual row restriction, and lower
mapping-cocone transition carry the universal q cap and its inhomogeneous
outer shift strictly from one arithmetic stage to the previous stage.
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

/-- The universal q cap commutes strictly with the actual factor-row
restriction and the factorial source transition. -/
theorem qRichLineageFullRowQuotientCap_successor (stage : Nat) :
    (qRichLineageFullRowQuotientCap (stage + 1)).comp
        (Cochain.ofHom (blockRowFamilyRestrictionMap stage))
          (add_zero (-1)) =
      (Cochain.ofHom (qRichLineageSingleOneRestriction stage)).comp
        (qRichLineageFullRowQuotientCap stage) (zero_add (-1)) := by
  unfold qRichLineageFullRowQuotientCap
  rw [qRichLineageFamilyCap_eq_fromSingle,
    qRichLineageFamilyCap_eq_fromSingle]
  rw [← Cochain.fromSingleMk_postcomp]
  unfold qRichLineageSingleOneRestriction
  rw [← Cochain.fromSingleMk_precomp]
  congr 1
  rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
  have endpoint := blockQRichEndpointVertexMap_restriction_scale stage
  have quotientSquare := congrArg (fun arrow => arrow.f 0)
    (blockQuotientFamilyRestriction_square stage)
  simp only [HomologicalComplex.comp_f] at quotientSquare
  have endpointDegree :
      ModuleCat.ofHom (blockQRichEndpointVertexMap (stage + 1)) ≫
          (blockDirectRestriction seedOccurrence.root stage).f 0 =
        ModuleCat.ofHom
          ((blockQRichSuccessorScale stage : BlockCoordinateRing) •
            LinearMap.id) ≫
          ModuleCat.ofHom (blockQRichEndpointVertexMap stage) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro base
    have generated := LinearMap.congr_fun endpoint base
    simpa [blockDirectRestriction, BlockDirectObject] using generated
  calc
    ModuleCat.ofHom (blockQRichEndpointVertexMap (stage + 1)) ≫
          (blockQuotientFamilyMap (stage + 1)).f 0 ≫
            (blockRowFamilyRestrictionMap stage).f 0 =
      ModuleCat.ofHom (blockQRichEndpointVertexMap (stage + 1)) ≫
        ((blockQuotientFamilyMap (stage + 1)).f 0 ≫
          (blockRowFamilyRestrictionMap stage).f 0) := rfl
    _ = ModuleCat.ofHom (blockQRichEndpointVertexMap (stage + 1)) ≫
        ((blockDirectRestriction seedOccurrence.root stage).f 0 ≫
          (blockQuotientFamilyMap stage).f 0) := by rw [← quotientSquare]
    _ = (ModuleCat.ofHom (blockQRichEndpointVertexMap (stage + 1)) ≫
          (blockDirectRestriction seedOccurrence.root stage).f 0) ≫
        (blockQuotientFamilyMap stage).f 0 :=
      (Category.assoc _ _ _).symm
    _ = (ModuleCat.ofHom
          ((blockQRichSuccessorScale stage : BlockCoordinateRing) •
            LinearMap.id) ≫
          ModuleCat.ofHom (blockQRichEndpointVertexMap stage)) ≫
        (blockQuotientFamilyMap stage).f 0 := by rw [endpointDegree]
    _ = ModuleCat.ofHom
          ((blockQRichSuccessorScale stage : BlockCoordinateRing) •
            LinearMap.id) ≫
        ModuleCat.ofHom (blockQRichEndpointVertexMap stage) ≫
          (blockQuotientFamilyMap stage).f 0 := Category.assoc _ _ _

theorem fullRowLowerTransition_fst (stage : Nat) :
    (fullRowDerivedCube stage).lowerTransition ≫
        CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage) =
      CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap (stage + 1)) ≫
        blockRowFamilyRestrictionMap stage := by
  unfold CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.lowerTransition
  exact CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
    (blockPrimePowerFamilyMap (stage + 1))
    (blockPrimePowerFamilyMap stage)
    (blockRowFamilyRestrictionMap stage)
    (blockRowFamilyRestrictionMap stage)
    (blockPrimePowerFamilyRestriction_square stage)

theorem fullRowLowerTransition_snd (stage : Nat) :
    (Cochain.ofHom (fullRowDerivedCube stage).lowerTransition).comp
        (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap stage)) (zero_add (-1)) =
      (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap (stage + 1))).comp
        (Cochain.ofHom (blockRowFamilyRestrictionMap stage))
          (add_zero (-1)) := by
  unfold CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.lowerTransition
  exact CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
    (blockPrimePowerFamilyMap (stage + 1))
    (blockPrimePowerFamilyMap stage)
    (blockRowFamilyRestrictionMap stage)
    (blockRowFamilyRestrictionMap stage)
    (blockPrimePowerFamilyRestriction_square stage)

/-- The inhomogeneous q-rich outer shift is itself strictly natural. -/
theorem qRichLineageFullRowOuterShift_successor (stage : Nat) :
    (qRichLineageFullRowOuterShift (stage + 1)).comp
        (Cochain.ofHom (fullRowDerivedCube stage).lowerTransition)
          (add_zero (-1)) =
      (Cochain.ofHom (qRichLineageSingleOneRestriction stage)).comp
        (qRichLineageFullRowOuterShift stage) (zero_add (-1)) := by
  ext source target related : 1
  simp only [Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext
    (blockPrimePowerFamilyMap stage) target
  · have transitionFst := congrArg (fun arrow => arrow.f target)
      (fullRowLowerTransition_fst stage)
    simp only [HomologicalComplex.comp_f] at transitionFst
    have highFst := Cochain.congr_v
      (qRichLineageFullRowOuterShift_comp_fst (stage + 1))
      source target related
    have lowFst := Cochain.congr_v
      (qRichLineageFullRowOuterShift_comp_fst stage)
      source target related
    have capSuccessor := Cochain.congr_v
      (qRichLineageFullRowQuotientCap_successor stage)
      source target related
    have highFstComponent :
        (qRichLineageFullRowOuterShift (stage + 1)).v
              source target related ≫
            (CochainComplex.mappingCocone.fst
              (blockPrimePowerFamilyMap (stage + 1))).f target =
          (qRichLineageFullRowQuotientCap (stage + 1)).v
            source target related := by
      simpa [Cochain.comp_v] using highFst
    have lowFstComponent :
        (qRichLineageFullRowOuterShift stage).v
              source target related ≫
            (CochainComplex.mappingCocone.fst
              (blockPrimePowerFamilyMap stage)).f target =
          (qRichLineageFullRowQuotientCap stage).v
            source target related := by
      simpa [Cochain.comp_v] using lowFst
    have capSuccessorComponent :
        (qRichLineageFullRowQuotientCap (stage + 1)).v
              source target related ≫
            (blockRowFamilyRestrictionMap stage).f target =
          (qRichLineageSingleOneRestriction stage).f source ≫
            (qRichLineageFullRowQuotientCap stage).v
              source target related := by
      simpa [Cochain.comp_v] using capSuccessor
    calc
      ((qRichLineageFullRowOuterShift (stage + 1)).v
          source target related ≫
        (fullRowDerivedCube stage).lowerTransition.f target) ≫
          (CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap stage)).f target =
        (qRichLineageFullRowOuterShift (stage + 1)).v
          source target related ≫
        ((fullRowDerivedCube stage).lowerTransition.f target ≫
          (CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap stage)).f target) :=
        Category.assoc _ _ _
      _ = (qRichLineageFullRowOuterShift (stage + 1)).v
          source target related ≫
        ((CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap (stage + 1))).f target ≫
          (blockRowFamilyRestrictionMap stage).f target) := by
        rw [transitionFst]
      _ = ((qRichLineageFullRowOuterShift (stage + 1)).v
            source target related ≫
          (CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap (stage + 1))).f target) ≫
        (blockRowFamilyRestrictionMap stage).f target :=
        (Category.assoc _ _ _).symm
      _ = (qRichLineageFullRowQuotientCap (stage + 1)).v
            source target related ≫
          (blockRowFamilyRestrictionMap stage).f target := by
        rw [highFstComponent]
      _ = (qRichLineageSingleOneRestriction stage).f source ≫
          (qRichLineageFullRowQuotientCap stage).v
            source target related := capSuccessorComponent
      _ = (qRichLineageSingleOneRestriction stage).f source ≫
          ((qRichLineageFullRowOuterShift stage).v
              source target related ≫
            (CochainComplex.mappingCocone.fst
              (blockPrimePowerFamilyMap stage)).f target) := by
        rw [lowFstComponent]
      _ = ((qRichLineageSingleOneRestriction stage).f source ≫
          (qRichLineageFullRowOuterShift stage).v
            source target related) ≫
          (CochainComplex.mappingCocone.fst
            (blockPrimePowerFamilyMap stage)).f target :=
        (Category.assoc _ _ _).symm
  · let previous := target + (-1)
    have transitionSnd := Cochain.congr_v
      (fullRowLowerTransition_snd stage) target previous rfl
    have transitionSndComponent :
        (fullRowDerivedCube stage).lowerTransition.f target ≫
            (CochainComplex.mappingCocone.snd
              (blockPrimePowerFamilyMap stage)).v target previous rfl =
          (CochainComplex.mappingCocone.snd
              (blockPrimePowerFamilyMap (stage + 1))).v
                target previous rfl ≫
            (blockRowFamilyRestrictionMap stage).f previous := by
      simpa [Cochain.comp_v] using transitionSnd
    have highSnd := Cochain.congr_v
      (qRichLineageFullRowOuterShift_comp_snd (stage + 1))
      source previous (by omega)
    have lowSnd := Cochain.congr_v
      (qRichLineageFullRowOuterShift_comp_snd stage)
      source previous (by omega)
    have highSndComponent :
        (qRichLineageFullRowOuterShift (stage + 1)).v
              source target related ≫
            (CochainComplex.mappingCocone.snd
              (blockPrimePowerFamilyMap (stage + 1))).v
                target previous rfl = 0 := by
      rw [Cochain.comp_v
        (qRichLineageFullRowOuterShift (stage + 1))
        (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap (stage + 1)))
        (show (-1 : ℤ) + (-1) = -2 by omega)
        source target previous related rfl] at highSnd
      simpa using highSnd
    have lowSndComponent :
        (qRichLineageFullRowOuterShift stage).v
              source target related ≫
            (CochainComplex.mappingCocone.snd
              (blockPrimePowerFamilyMap stage)).v target previous rfl = 0 := by
      rw [Cochain.comp_v
        (qRichLineageFullRowOuterShift stage)
        (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap stage))
        (show (-1 : ℤ) + (-1) = -2 by omega)
        source target previous related rfl] at lowSnd
      simpa using lowSnd
    calc
      ((qRichLineageFullRowOuterShift (stage + 1)).v
          source target related ≫
        (fullRowDerivedCube stage).lowerTransition.f target) ≫
          (CochainComplex.mappingCocone.snd
            (blockPrimePowerFamilyMap stage)).v target previous rfl =
        (qRichLineageFullRowOuterShift (stage + 1)).v
          source target related ≫
        ((fullRowDerivedCube stage).lowerTransition.f target ≫
          (CochainComplex.mappingCocone.snd
            (blockPrimePowerFamilyMap stage)).v target previous rfl) :=
        Category.assoc _ _ _
      _ = (qRichLineageFullRowOuterShift (stage + 1)).v
          source target related ≫
        ((CochainComplex.mappingCocone.snd
            (blockPrimePowerFamilyMap (stage + 1))).v
              target previous rfl ≫
          (blockRowFamilyRestrictionMap stage).f previous) := by
        rw [transitionSndComponent]
      _ = ((qRichLineageFullRowOuterShift (stage + 1)).v
            source target related ≫
          (CochainComplex.mappingCocone.snd
            (blockPrimePowerFamilyMap (stage + 1))).v
              target previous rfl) ≫
        (blockRowFamilyRestrictionMap stage).f previous :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [highSndComponent, Limits.zero_comp]
      _ = (qRichLineageSingleOneRestriction stage).f source ≫ 0 := by
        simp
      _ = (qRichLineageSingleOneRestriction stage).f source ≫
          ((qRichLineageFullRowOuterShift stage).v
              source target related ≫
            (CochainComplex.mappingCocone.snd
              (blockPrimePowerFamilyMap stage)).v target previous rfl) := by
        rw [lowSndComponent]
      _ = ((qRichLineageSingleOneRestriction stage).f source ≫
          (qRichLineageFullRowOuterShift stage).v
            source target related) ≫
          (CochainComplex.mappingCocone.snd
            (blockPrimePowerFamilyMap stage)).v target previous rfl :=
        (Category.assoc _ _ _).symm

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
