import H0mework.Arithmetic.RiemannLineage.LineagePoint

/-!
# The full actual factor-row square

Every factor row of one finite arithmetic stage is assembled into a single
row-family carrier.  The whole anti-invariant coordinate, the rowwise
quotient coordinates, and multiplication by the corresponding actual prime
powers form one homotopy-commutative square over the existing total fibre.

This module constructs only the finite all-row square.  It contains no
successor cube, endpoint cap, analytic specialization, fixedness statement,
or choice of an inverse-fibre component.
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
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom

noncomputable section

abbrev BlockRowFamily (stage : Nat) :=
  BlockWholeRelation seedOccurrence.root stage

noncomputable abbrev blockRowFamilySingle (stage : Nat) :
    CochainComplex (ModuleCat BlockCoordinateRing) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat BlockCoordinateRing) 0).obj
    (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))

def blockWholeFamilyProjection (stage : Nat) :
    BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockRowFamily stage where
  toFun value row :=
    blockInnerAntiInvariant seedOccurrence.root stage (value none)
  map_add' left right := by
    funext row
    exact (blockInnerAntiInvariant seedOccurrence.root stage).map_add
      (left none) (right none)
  map_smul' scalar value := by
    funext row
    exact (blockInnerAntiInvariant seedOccurrence.root stage).map_smul
      scalar (value none)

def blockQuotientFamilyProjection (stage : Nat) :
    BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockRowFamily stage where
  toFun value row :=
    blockInnerAntiInvariant seedOccurrence.root stage (value (some row))
  map_add' left right := by
    funext row
    exact (blockInnerAntiInvariant seedOccurrence.root stage).map_add
      (left (some row)) (right (some row))
  map_smul' scalar value := by
    funext row
    exact (blockInnerAntiInvariant seedOccurrence.root stage).map_smul
      scalar (value (some row))

def blockPrimePowerFamilyProjection (stage : Nat) :
    BlockRowFamily stage →ₗ[BlockCoordinateRing] BlockRowFamily stage where
  toFun value row :=
    ((((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) •
      value row)
  map_add' left right := by
    funext row
    simp only [Pi.add_apply]
    rw [smul_add]
  map_smul' scalar value := by
    funext row
    simp only [Pi.smul_apply, RingHom.id_apply]
    change _ • (scalar • value row) = scalar • (_ • value row)
    module

noncomputable def blockWholeFamilyMap (stage : Nat) :
    LocalWholeComplex stage ⟶ blockRowFamilySingle stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeFamilyProjection stage)
    · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      simp [blockRowFamilySingle]
    · simp [blockRowFamilySingle, blockDirectDifferential, sourceZero]

noncomputable def blockQuotientFamilyMap (stage : Nat) :
    LocalWholeComplex stage ⟶ blockRowFamilySingle stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockQuotientFamilyProjection stage)
    · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      simp [blockRowFamilySingle]
    · simp [blockRowFamilySingle, blockDirectDifferential, sourceZero]

noncomputable def blockPrimePowerFamilyMap (stage : Nat) :
    blockRowFamilySingle stage ⟶ blockRowFamilySingle stage :=
  (CochainComplex.singleFunctor (ModuleCat BlockCoordinateRing) 0).map
    (ModuleCat.ofHom (blockPrimePowerFamilyProjection stage))

namespace ClosedOuterShiftKernel

universe u

variable {R : Type u} [CommRing R]
variable {K L : ModuleCat R}

abbrev SingleZero (M : ModuleCat R) :
    CochainComplex (ModuleCat R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat R) 0).obj M

variable (phi : SingleZero K ⟶ SingleZero L)

/-- A closed degree `-1` shift into the mapping cocone of an injective
degree-zero arrow is forced to vanish. -/
theorem closedShift_eq_zero_of_degreeZero_injective
    (injective : Function.Injective (phi.f 0).hom)
    (shift : Cochain
      (CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne (R := R))
      (CochainComplex.mappingCocone phi) (-1))
    (closed : δ (-1) 0 shift = 0) :
    shift = 0 := by
  obtain ⟨generator, rfl⟩ :=
    Cochain.fromSingleMk_surjective shift 0 (by omega)
  have closed' := closed
  rw [Cochain.δ_fromSingleMk _ _ 0 1 (by omega)] at closed'
  have generator_d_zero :
      generator ≫ (CochainComplex.mappingCocone phi).d 0 1 = 0 := by
    have evaluated := congrArg
      (Cochain.fromSingleEquiv
        (X := CochainMappingCoconeMappedBoundaryAtomOver.ScalarUnit (R := R))
        (K := CochainComplex.mappingCocone phi)
        (show 1 + 0 = 1 by omega)) closed'
    simpa using evaluated
  have postcomposed := congrArg
    (fun arrow => arrow ≫
      (CochainComplex.mappingCocone.snd phi).v 1 0 (by omega))
    generator_d_zero
  simp only [Limits.zero_comp, Category.assoc] at postcomposed
  rw [CochainMappingCoconeTotalFiberSymmetry.mappingCocone_d_snd
    phi 0 1 (by omega)] at postcomposed
  have previousZero : IsZero ((SingleZero L).X (0 + (-1))) :=
    HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 L (0 + (-1)) (by omega)
  have sndZero :
      (CochainComplex.mappingCocone.snd phi).v
        0 (0 + (-1)) rfl = 0 :=
    previousZero.eq_of_tgt _ _
  rw [sndZero, Limits.zero_comp, sub_zero] at postcomposed
  have composite_zero :
      (generator ≫
          (CochainComplex.mappingCocone.fst phi).f 0) ≫
        phi.f 0 = 0 := by
    simpa only [Preadditive.comp_neg, neg_eq_zero,
      Category.assoc] using postcomposed
  have fst_zero :
      generator ≫
          (CochainComplex.mappingCocone.fst phi).f 0 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro scalar
    apply injective
    have evaluated := ConcreteCategory.congr_hom composite_zero scalar
    simpa using evaluated
  have generator_zero : generator = 0 := by
    apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext phi 0
    · simpa only [Limits.zero_comp] using fst_zero
    · exact previousZero.eq_of_tgt _ _
  rw [generator_zero]
  exact Cochain.fromSingleMk_zero
    (CochainMappingCoconeMappedBoundaryAtomOver.ScalarUnit (R := R))
    (CochainComplex.mappingCocone phi) 1 0 (-1) (by omega)

end ClosedOuterShiftKernel

theorem blockPrimePowerFamilyProjection_injective (stage : Nat) :
    Function.Injective (blockPrimePowerFamilyProjection stage) := by
  intro left right equality
  funext row index
  have evaluated := congrFun (congrFun equality row) index
  change
    (((((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row)) *
        left row index) =
      (((((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row)) *
        right row index) at evaluated
  have prime_ne :
      (((rowPrime row : Nat) : BlockCoordinateRing)) ≠ 0 := by
    change MvPolynomial.C (((rowPrime row : Nat) : ℤ)) ≠ 0
    rw [MvPolynomial.C_ne_zero]
    exact_mod_cast (rowPrime row).property.ne_zero
  exact mul_left_cancel₀ (pow_ne_zero _ prime_ne) evaluated

theorem blockPrimePowerFamilyMap_degreeZero_injective (stage : Nat) :
    Function.Injective ((blockPrimePowerFamilyMap stage).f 0).hom := by
  intro left right equality
  have component :
      (blockPrimePowerFamilyMap stage).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))).hom ≫
          ModuleCat.ofHom (blockPrimePowerFamilyProjection stage) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))).inv := by
    exact HomologicalComplex.single_map_f_self
      (ComplexShape.up ℤ) 0
      (ModuleCat.ofHom (blockPrimePowerFamilyProjection stage))
  rw [component] at equality
  have mapped := congrArg
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))).hom.hom
    equality
  simp only [ConcreteCategory.comp_apply] at mapped
  have sourceEqual :=
    blockPrimePowerFamilyProjection_injective stage mapped
  apply (ModuleCat.mono_iff_injective
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))).hom).mp
      inferInstance
  exact sourceEqual

theorem closedFullRowOuterShift_eq_zero (stage : Nat)
    (shift : Cochain
      (CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing))
      (CochainComplex.mappingCocone (blockPrimePowerFamilyMap stage)) (-1))
    (closed : δ (-1) 0 shift = 0) :
    shift = 0 :=
  ClosedOuterShiftKernel.closedShift_eq_zero_of_degreeZero_injective
    (blockPrimePowerFamilyMap stage)
    (blockPrimePowerFamilyMap_degreeZero_injective stage) shift closed

noncomputable def blockFactorizationFamilyCochain (stage : Nat) :
    Cochain (LocalWholeComplex stage) (blockRowFamilySingle stage) (-1) :=
  Cochain.mk fun source target _degree => by
    by_cases sourceOne : source = 1
    · subst source
      have targetZero : target = 0 := by omega
      subst target
      exact 𝟙 (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage))
    · exact 0

theorem blockFamilyDifference_eq_delta (stage : Nat) :
    Cochain.ofHom
        (blockWholeFamilyMap stage -
          blockQuotientFamilyMap stage ≫ blockPrimePowerFamilyMap stage) =
      δ (-1) 0 (blockFactorizationFamilyCochain stage) := by
  ext source : 1
  by_cases sourceZero : source = 0
  · subst source
    simp [blockFactorizationFamilyCochain, blockWholeFamilyMap,
      blockQuotientFamilyMap, blockPrimePowerFamilyMap,
      blockWholeFamilyProjection, blockQuotientFamilyProjection,
      blockPrimePowerFamilyProjection, δ_v, blockRowFamilySingle]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro value
    rfl
  · have sourceNeOne : source + 1 ≠ 1 := by omega
    simp [blockFactorizationFamilyCochain, blockWholeFamilyMap,
      blockQuotientFamilyMap, blockPrimePowerFamilyMap,
      blockRowFamilySingle, blockDirectDifferential,
      sourceZero, sourceNeOne, δ_v]

noncomputable def blockFactorizationFamilyHomotopy (stage : Nat) :
    Homotopy
      (blockWholeFamilyMap stage -
        blockQuotientFamilyMap stage ≫ blockPrimePowerFamilyMap stage)
      0 :=
  (Cochain.equivHomotopy _ _).symm
    ⟨blockFactorizationFamilyCochain stage, by
      rw [Cochain.ofHom_zero, add_zero]
      exact blockFamilyDifference_eq_delta stage⟩

theorem blockFactorizationFamilyHomotopy_cochain (stage : Nat) :
    Cochain.ofHomotopy (blockFactorizationFamilyHomotopy stage) =
      blockFactorizationFamilyCochain stage := by
  ext source target related
  simp [blockFactorizationFamilyHomotopy, Cochain.ofHomotopy]
  split_ifs
  rfl

private noncomputable def homotopyEqOfSubHomotopy
    {K L : CochainComplex (ModuleCat BlockCoordinateRing) ℤ}
    (first second : K ⟶ L)
    (differenceHomotopy : Homotopy (first - second) 0) :
    Homotopy first second := by
  let middle := Homotopy.add differenceHomotopy (Homotopy.refl second)
  exact (Homotopy.ofEq (sub_add_cancel first second).symm).trans
    (middle.trans (Homotopy.ofEq (zero_add second)))

private noncomputable def quotientFamilyToWholeHomotopy (stage : Nat) :
    Homotopy
      (blockQuotientFamilyMap stage ≫ blockPrimePowerFamilyMap stage)
      (blockWholeFamilyMap stage) :=
  (homotopyEqOfSubHomotopy
    (blockWholeFamilyMap stage)
    (blockQuotientFamilyMap stage ≫ blockPrimePowerFamilyMap stage)
    (blockFactorizationFamilyHomotopy stage)).symm

noncomputable abbrev fullRowDerivedSquare (stage : Nat) :
    CochainMappingCoconeTotalFiberSymmetry.HomotopyCommutativeCochainSquareAt
      (ModuleCat BlockCoordinateRing) where
  upperLeft := LocalWholeComplex stage
  upperRight := LocalTotalFiber stage
  lowerLeft := blockRowFamilySingle stage
  lowerRight := blockRowFamilySingle stage
  horizontalSource := localTotalInclusion stage
  horizontalTarget := blockPrimePowerFamilyMap stage
  verticalLeft := blockQuotientFamilyMap stage
  verticalRight :=
    localTotalEndpointProjection stage ≫ blockWholeFamilyMap stage
  square :=
    (Homotopy.ofEq (by rfl)).trans
      ((quotientFamilyToWholeHomotopy stage).trans
        (Homotopy.ofEq (by simp)))

theorem fullRowDerivedSquare_cochain (stage : Nat) :
    Cochain.ofHomotopy (fullRowDerivedSquare stage).square =
      -blockFactorizationFamilyCochain stage := by
  ext source target related
  simp [fullRowDerivedSquare, quotientFamilyToWholeHomotopy,
    homotopyEqOfSubHomotopy, blockFactorizationFamilyHomotopy,
    Cochain.ofHomotopy]
  split_ifs
  rfl

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
