import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

/-!
# Generated exterior-Yukawa mass rank, kernel, and finite mixing

This module closes Stage 8C for the actual breaking/Yukawa map from Stage 8B.
For the selected decomposable `Λ⁴V` breaking vector, a degree-two basis state
has nonzero mass image exactly when its two-index subset is disjoint from the
four breaking indices.  The three-element complement therefore supplies
exactly `choose 3 2 = 3` independent massive channels.  Lean proves the exact
range, rank `3`, and kernel finrank `18` inside the actual 21-dimensional
`Λ²V` matter summand.  Zero breaking produces the zero mass map.

A separate proof-only two-generation prototype defines every entry of a
`2 × 2` mass matrix by evaluating the same legal exterior Yukawa map on
explicit actual scalar, input, and output basis channels.  Both off-diagonal
entries are proved nonzero, hence the derived matrix is not diagonal.  No
numeric mass matrix is accepted as an input.

Boundary: the finite-generation tensor is a prototype flavor layer, not a
claim that Stage 7 generated two physical generations and not a CKM/PMNS fit.
The rank/kernel theorem is physical-representation-level; the flavor matrix is
kept separately proof-only until a generation producer exists.  Full field
variations and currents belong to Stage 8D.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorYukawaMassSpectrum

open SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal

open scoped TensorProduct

noncomputable section

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

theorem exteriorYukawaMassMap_basisPair_of_disjoint
    (matterIndex : ExteriorBasisIndex 2)
    (scalarIndex : ExteriorBasisIndex 4)
    (disjoint : Disjoint matterIndex.1 scalarIndex.1) :
    exteriorYukawaMassMap (su7ExteriorBasis 4 scalarIndex)
        (su7ExteriorBasis 2 matterIndex) =
      (Set.powersetCard.permOfDisjoint disjoint).sign •
        su7ExteriorBasis 6 (Set.powersetCard.disjUnion disjoint) := by
  apply Subtype.ext
  simpa [exteriorYukawaMassMap, exteriorWedge,
    su7ExteriorBasis, exteriorPower.basis_apply] using
    ExteriorAlgebra.ιMulti_family_mul_of_disjoint ℂ su7FundamentalBasis
      matterIndex scalarIndex disjoint

theorem exteriorYukawaMassMap_basisPair_of_not_disjoint
    (matterIndex : ExteriorBasisIndex 2)
    (scalarIndex : ExteriorBasisIndex 4)
    (notDisjoint : ¬ Disjoint matterIndex.1 scalarIndex.1) :
    exteriorYukawaMassMap (su7ExteriorBasis 4 scalarIndex)
        (su7ExteriorBasis 2 matterIndex) = 0 := by
  apply Subtype.ext
  simpa [exteriorYukawaMassMap, exteriorWedge,
    su7ExteriorBasis, exteriorPower.basis_apply] using
    ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint ℂ su7FundamentalBasis
      matterIndex scalarIndex notDisjoint

theorem exteriorYukawaMassMap_basis_of_disjoint
    (index : ExteriorBasisIndex 2)
    (disjoint : Disjoint index.1 exteriorBreakingScalarIndex.1) :
    exteriorYukawaMassMap exteriorBreakingScalar
        (su7ExteriorBasis 2 index) =
      (Set.powersetCard.permOfDisjoint disjoint).sign •
        su7ExteriorBasis 6 (Set.powersetCard.disjUnion disjoint) := by
  apply Subtype.ext
  simpa [exteriorYukawaMassMap, exteriorWedge, exteriorBreakingScalar,
    su7ExteriorBasis, exteriorPower.basis_apply] using
    ExteriorAlgebra.ιMulti_family_mul_of_disjoint ℂ su7FundamentalBasis
      index exteriorBreakingScalarIndex disjoint

theorem exteriorYukawaMassMap_basis_of_not_disjoint
    (index : ExteriorBasisIndex 2)
    (notDisjoint : ¬ Disjoint index.1 exteriorBreakingScalarIndex.1) :
    exteriorYukawaMassMap exteriorBreakingScalar
        (su7ExteriorBasis 2 index) = 0 := by
  apply Subtype.ext
  simpa [exteriorYukawaMassMap, exteriorWedge, exteriorBreakingScalar,
    su7ExteriorBasis, exteriorPower.basis_apply] using
    ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint ℂ su7FundamentalBasis
      index exteriorBreakingScalarIndex notDisjoint

def exteriorMassiveDegreeTwoSubset : Fin 3 → Finset SU7MotherIndex
  | 0 => {weakZeroIndex, weakOneIndex}
  | 1 => {weakZeroIndex, hyperMinusIndex}
  | 2 => {weakOneIndex, hyperMinusIndex}

def exteriorMassiveDegreeTwoIndex
    (channel : Fin 3) : ExteriorBasisIndex 2 :=
  ⟨exteriorMassiveDegreeTwoSubset channel, by
    fin_cases channel <;>
      simp [exteriorMassiveDegreeTwoSubset, weakZeroIndex, weakOneIndex,
        hyperMinusIndex]⟩

theorem exteriorMassiveDegreeTwo_disjoint
    (channel : Fin 3) :
    Disjoint (exteriorMassiveDegreeTwoIndex channel).1
      exteriorBreakingScalarIndex.1 := by
  fin_cases channel <;> decide

def exteriorMassiveDegreeSixIndex
    (channel : Fin 3) : ExteriorBasisIndex 6 :=
  Set.powersetCard.disjUnion
    (exteriorMassiveDegreeTwo_disjoint channel)

theorem exteriorMassiveDegreeSixIndex_injective :
    Function.Injective exteriorMassiveDegreeSixIndex := by
  decide

theorem every_disjoint_degreeTwoIndex_is_massive :
    ∀ index : ExteriorBasisIndex 2,
      Disjoint index.1 exteriorBreakingScalarIndex.1 →
        ∃ channel : Fin 3,
          index = exteriorMassiveDegreeTwoIndex channel := by
  rintro ⟨subset, subsetCard⟩ disjoint
  change subset.card = 2 at subsetCard
  rcases Finset.card_eq_two.mp subsetCard with
    ⟨first, second, distinct, rfl⟩
  have firstNotBreaking :=
    (Finset.disjoint_left.mp disjoint)
      (by simp : first ∈ ({first, second} : Finset SU7MotherIndex))
  have secondNotBreaking :=
    (Finset.disjoint_left.mp disjoint)
      (by simp : second ∈ ({first, second} : Finset SU7MotherIndex))
  fin_cases first <;> fin_cases second <;>
    simp_all [exteriorBreakingScalarIndex, exteriorBreakingScalarSubset,
      colorZeroIndex, colorOneIndex, colorTwoIndex, hyperPlusIndex,
      exteriorMassiveDegreeTwoIndex, exteriorMassiveDegreeTwoSubset,
      weakZeroIndex, weakOneIndex, hyperMinusIndex] <;>
    decide

def exteriorMassiveOutputFamily
    (channel : Fin 3) : ExteriorDegreeSixMatterCarrier :=
  su7ExteriorBasis 6 (exteriorMassiveDegreeSixIndex channel)

theorem exteriorMassiveOutputFamily_linearIndependent :
    LinearIndependent ℂ exteriorMassiveOutputFamily := by
  exact (su7ExteriorBasis 6).linearIndependent.comp
    exteriorMassiveDegreeSixIndex
    exteriorMassiveDegreeSixIndex_injective

def exteriorMassiveOutputSubspace :
    Submodule ℂ ExteriorDegreeSixMatterCarrier :=
  Submodule.span ℂ (Set.range exteriorMassiveOutputFamily)

theorem exteriorMassiveOutputSubspace_finrank :
    Module.finrank ℂ exteriorMassiveOutputSubspace = 3 := by
  rw [exteriorMassiveOutputSubspace,
    finrank_span_eq_card exteriorMassiveOutputFamily_linearIndependent]
  simp

theorem exteriorYukawaMassMap_basis_mem_massiveOutput
    (index : ExteriorBasisIndex 2) :
    exteriorYukawaMassMap exteriorBreakingScalar
        (su7ExteriorBasis 2 index) ∈ exteriorMassiveOutputSubspace := by
  by_cases disjoint :
      Disjoint index.1 exteriorBreakingScalarIndex.1
  · rcases every_disjoint_degreeTwoIndex_is_massive index disjoint with
      ⟨channel, rfl⟩
    rw [exteriorYukawaMassMap_basis_of_disjoint
      (exteriorMassiveDegreeTwoIndex channel)
      (exteriorMassiveDegreeTwo_disjoint channel)]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨channel, rfl⟩
  · rw [exteriorYukawaMassMap_basis_of_not_disjoint index disjoint]
    exact Submodule.zero_mem _

theorem exteriorYukawaMassMap_range_le_massiveOutput :
    LinearMap.range
        (exteriorYukawaMassMap exteriorBreakingScalar) ≤
      exteriorMassiveOutputSubspace := by
  rintro output ⟨input, rfl⟩
  rw [← (su7ExteriorBasis 2).sum_repr input, map_sum]
  apply Submodule.sum_mem
  intro index _
  rw [map_smul]
  exact Submodule.smul_mem _ _
    (exteriorYukawaMassMap_basis_mem_massiveOutput index)

def exteriorMassiveInputFamily
    (channel : Fin 3) : ExteriorDegreeTwoMatterCarrier :=
  su7ExteriorBasis 2 (exteriorMassiveDegreeTwoIndex channel)

def exteriorMassiveImageFamily
    (channel : Fin 3) : ExteriorDegreeSixMatterCarrier :=
  exteriorYukawaMassMap exteriorBreakingScalar
    (exteriorMassiveInputFamily channel)

def exteriorMassiveSignUnit (channel : Fin 3) : ℂˣ :=
  Units.map (Int.castRingHom ℂ)
    (Set.powersetCard.permOfDisjoint
      (exteriorMassiveDegreeTwo_disjoint channel)).sign

theorem exteriorMassiveImageFamily_eq
    (channel : Fin 3) :
    exteriorMassiveImageFamily channel =
      exteriorMassiveSignUnit channel •
        exteriorMassiveOutputFamily channel := by
  rw [exteriorMassiveImageFamily, exteriorMassiveInputFamily,
    exteriorYukawaMassMap_basis_of_disjoint
      (exteriorMassiveDegreeTwoIndex channel)
      (exteriorMassiveDegreeTwo_disjoint channel)]
  let signUnit : ℤˣ :=
    (Set.powersetCard.permOfDisjoint
      (exteriorMassiveDegreeTwo_disjoint channel)).sign
  change
    signUnit • exteriorMassiveOutputFamily channel =
      Units.map (Int.castRingHom ℂ).toMonoidHom signUnit •
        exteriorMassiveOutputFamily channel
  rw [Units.smul_def, Units.smul_def]
  exact (Int.cast_smul_eq_zsmul ℂ signUnit.val
    (exteriorMassiveOutputFamily channel)).symm

theorem exteriorMassiveImageFamily_linearIndependent :
    LinearIndependent ℂ exteriorMassiveImageFamily := by
  rw [show exteriorMassiveImageFamily = fun channel =>
      exteriorMassiveSignUnit channel •
        exteriorMassiveOutputFamily channel by
    funext channel
    exact exteriorMassiveImageFamily_eq channel]
  exact exteriorMassiveOutputFamily_linearIndependent.units_smul
    exteriorMassiveSignUnit

def exteriorMassiveRangeFamily
    (channel : Fin 3) :
    LinearMap.range (exteriorYukawaMassMap exteriorBreakingScalar) :=
  ⟨exteriorMassiveImageFamily channel,
    exteriorMassiveInputFamily channel, rfl⟩

theorem exteriorMassiveRangeFamily_linearIndependent :
    LinearIndependent ℂ exteriorMassiveRangeFamily := by
  apply LinearIndependent.of_comp
    (LinearMap.range (exteriorYukawaMassMap exteriorBreakingScalar)).subtype
  simpa [Function.comp_def, exteriorMassiveRangeFamily] using
    exteriorMassiveImageFamily_linearIndependent

theorem exteriorYukawaMassMap_rank :
    Module.finrank ℂ
        (LinearMap.range
          (exteriorYukawaMassMap exteriorBreakingScalar)) = 3 := by
  apply le_antisymm
  · calc
      Module.finrank ℂ
          (LinearMap.range
            (exteriorYukawaMassMap exteriorBreakingScalar)) ≤
          Module.finrank ℂ exteriorMassiveOutputSubspace :=
        Submodule.finrank_mono
          exteriorYukawaMassMap_range_le_massiveOutput
      _ = 3 := exteriorMassiveOutputSubspace_finrank
  · simpa using
      exteriorMassiveRangeFamily_linearIndependent.fintype_card_le_finrank

theorem exteriorYukawaMassMap_range_eq_massiveOutput :
    LinearMap.range
        (exteriorYukawaMassMap exteriorBreakingScalar) =
      exteriorMassiveOutputSubspace := by
  apply Submodule.eq_of_le_of_finrank_eq
    exteriorYukawaMassMap_range_le_massiveOutput
  rw [exteriorYukawaMassMap_rank,
    exteriorMassiveOutputSubspace_finrank]

theorem exteriorYukawaMassMap_kernel_finrank :
    Module.finrank ℂ
        (LinearMap.ker
          (exteriorYukawaMassMap exteriorBreakingScalar)) = 18 := by
  have rankNullity :=
    LinearMap.finrank_range_add_finrank_ker
      (exteriorYukawaMassMap exteriorBreakingScalar)
  rw [exteriorYukawaMassMap_rank,
    su7ExteriorPower_finrank] at rankNullity
  norm_num [Nat.choose] at rankNullity ⊢
  omega

@[simp] theorem exteriorYukawaMassMap_zeroBreaking :
    exteriorYukawaMassMap (0 : ExteriorBreakingScalarCarrier) = 0 := by
  apply LinearMap.ext
  intro matter
  simp [exteriorYukawaMassMap]

/-! ## A proof-only two-generation mixing prototype -/

def finiteGenerationInputSubset : Fin 2 → Finset SU7MotherIndex
  | 0 => {weakZeroIndex, weakOneIndex}
  | 1 => {weakZeroIndex, hyperMinusIndex}

def finiteGenerationInputIndex
    (generation : Fin 2) : ExteriorBasisIndex 2 :=
  ⟨finiteGenerationInputSubset generation, by
    fin_cases generation <;>
      simp [finiteGenerationInputSubset, weakZeroIndex, weakOneIndex,
        hyperMinusIndex]⟩

def finiteGenerationOutputSubset : Fin 2 → Finset SU7MotherIndex
  | 0 =>
      {colorZeroIndex, colorOneIndex, colorTwoIndex,
        weakZeroIndex, weakOneIndex, hyperMinusIndex}
  | 1 =>
      {colorZeroIndex, colorOneIndex, weakZeroIndex,
        weakOneIndex, hyperPlusIndex, hyperMinusIndex}

def finiteGenerationOutputIndex
    (generation : Fin 2) : ExteriorBasisIndex 6 :=
  ⟨finiteGenerationOutputSubset generation, by
    fin_cases generation <;>
      simp [finiteGenerationOutputSubset, colorZeroIndex, colorOneIndex,
        colorTwoIndex, weakZeroIndex, weakOneIndex, hyperPlusIndex,
        hyperMinusIndex]⟩

def finiteGenerationScalarSubset :
    Fin 2 → Fin 2 → Finset SU7MotherIndex
  | 0, 0 =>
      {colorZeroIndex, colorOneIndex, colorTwoIndex, hyperMinusIndex}
  | 0, 1 =>
      {colorZeroIndex, colorOneIndex, colorTwoIndex, weakOneIndex}
  | 1, 0 =>
      {colorZeroIndex, colorOneIndex, hyperPlusIndex, hyperMinusIndex}
  | 1, 1 =>
      {colorZeroIndex, colorOneIndex, weakOneIndex, hyperPlusIndex}

def finiteGenerationScalarIndex
    (outputGeneration inputGeneration : Fin 2) : ExteriorBasisIndex 4 :=
  ⟨finiteGenerationScalarSubset outputGeneration inputGeneration, by
    fin_cases outputGeneration <;> fin_cases inputGeneration <;>
      simp [finiteGenerationScalarSubset, colorZeroIndex, colorOneIndex,
        colorTwoIndex, weakOneIndex, hyperPlusIndex, hyperMinusIndex]⟩

theorem finiteGeneration_pair_disjoint
    (outputGeneration inputGeneration : Fin 2) :
    Disjoint (finiteGenerationInputIndex inputGeneration).1
      (finiteGenerationScalarIndex outputGeneration inputGeneration).1 := by
  fin_cases outputGeneration <;> fin_cases inputGeneration <;> decide

theorem finiteGeneration_pair_union
    (outputGeneration inputGeneration : Fin 2) :
    Set.powersetCard.disjUnion
        (finiteGeneration_pair_disjoint outputGeneration inputGeneration) =
      finiteGenerationOutputIndex outputGeneration := by
  apply Subtype.ext
  fin_cases outputGeneration <;> fin_cases inputGeneration <;> decide

def finiteGenerationBreakingTensor
    (outputGeneration inputGeneration : Fin 2) :
    ExteriorBreakingScalarCarrier :=
  su7ExteriorBasis 4
    (finiteGenerationScalarIndex outputGeneration inputGeneration)

def finiteGenerationInputFamily
    (generation : Fin 2) : ExteriorDegreeTwoMatterCarrier :=
  su7ExteriorBasis 2 (finiteGenerationInputIndex generation)

def finiteGenerationOutputCoordinate
    (generation : Fin 2) :
    Module.Dual ℂ ExteriorDegreeSixMatterCarrier :=
  (su7ExteriorBasis 6).coord
    (finiteGenerationOutputIndex generation)

/-- Every entry is read from an actual exterior Yukawa channel.  No numerical
mass matrix is accepted as an argument. -/
def finiteGenerationMassMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  fun outputGeneration inputGeneration =>
    finiteGenerationOutputCoordinate outputGeneration
      (exteriorYukawaMassMap
        (finiteGenerationBreakingTensor outputGeneration inputGeneration)
        (finiteGenerationInputFamily inputGeneration))

theorem finiteGenerationMassMatrix_entry
    (outputGeneration inputGeneration : Fin 2) :
    finiteGenerationMassMatrix outputGeneration inputGeneration =
      (Set.powersetCard.permOfDisjoint
        (finiteGeneration_pair_disjoint
          outputGeneration inputGeneration)).sign • (1 : ℂ) := by
  rw [finiteGenerationMassMatrix, finiteGenerationBreakingTensor,
    finiteGenerationInputFamily,
    exteriorYukawaMassMap_basisPair_of_disjoint
      (finiteGenerationInputIndex inputGeneration)
      (finiteGenerationScalarIndex outputGeneration inputGeneration)
      (finiteGeneration_pair_disjoint outputGeneration inputGeneration),
    finiteGeneration_pair_union]
  simp [finiteGenerationOutputCoordinate]

theorem finiteGenerationMassMatrix_entry_ne_zero
    (outputGeneration inputGeneration : Fin 2) :
    finiteGenerationMassMatrix outputGeneration inputGeneration ≠ 0 := by
  rw [finiteGenerationMassMatrix_entry]
  intro signedOneZero
  exact one_ne_zero
    ((smul_eq_zero_iff_eq
      (Set.powersetCard.permOfDisjoint
        (finiteGeneration_pair_disjoint
          outputGeneration inputGeneration)).sign).mp signedOneZero)

theorem finiteGenerationMassMatrix_offDiagonal_nonzero :
    finiteGenerationMassMatrix 0 1 ≠ 0 ∧
      finiteGenerationMassMatrix 1 0 ≠ 0 :=
  ⟨finiteGenerationMassMatrix_entry_ne_zero 0 1,
    finiteGenerationMassMatrix_entry_ne_zero 1 0⟩

theorem finiteGenerationMassMatrix_not_diagonal :
    finiteGenerationMassMatrix ≠
      Matrix.diagonal (fun generation =>
        finiteGenerationMassMatrix generation generation) := by
  intro diagonal
  have offDiagonal := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => matrix 0 1) diagonal
  have offDiagonalZero : finiteGenerationMassMatrix 0 1 = 0 := by
    simpa [Matrix.diagonal_apply,
      show (0 : Fin 2) ≠ 1 by decide] using offDiagonal
  exact finiteGenerationMassMatrix_entry_ne_zero 0 1 offDiagonalZero

/-! ## One joint breaking scalar for the complete mixing matrix -/

/-- Linearity in the breaking input, kept here below the mass-spectrum layer
so the joint scalar does not depend on the later variation receipt. -/
theorem exteriorYukawaMassMap_add_breaking
    (first second : ExteriorBreakingScalarCarrier) :
    exteriorYukawaMassMap (first + second) =
      exteriorYukawaMassMap first + exteriorYukawaMassMap second := by
  apply LinearMap.ext
  intro matter
  change
    exteriorWedge 2 4 matter (first + second) =
      exteriorWedge 2 4 matter first + exteriorWedge 2 4 matter second
  exact map_add (exteriorWedge 2 4 matter) first second

theorem finiteGenerationBreakingTensor_action_sameInput
    (output input : Fin 2) :
    exteriorYukawaMassMap
        (finiteGenerationBreakingTensor output input)
        (finiteGenerationInputFamily input) =
      (Set.powersetCard.permOfDisjoint
        (finiteGeneration_pair_disjoint output input)).sign •
        su7ExteriorBasis 6 (finiteGenerationOutputIndex output) := by
  rw [finiteGenerationBreakingTensor, finiteGenerationInputFamily,
    exteriorYukawaMassMap_basisPair_of_disjoint
      (finiteGenerationInputIndex input)
      (finiteGenerationScalarIndex output input)
      (finiteGeneration_pair_disjoint output input),
    finiteGeneration_pair_union]

theorem finiteGenerationBreakingTensor_action_otherInput
    (output input otherInput : Fin 2) (different : input ≠ otherInput) :
    exteriorYukawaMassMap
        (finiteGenerationBreakingTensor output input)
        (finiteGenerationInputFamily otherInput) = 0 := by
  rw [finiteGenerationBreakingTensor, finiteGenerationInputFamily,
    exteriorYukawaMassMap_basisPair_of_not_disjoint]
  fin_cases output <;> fin_cases input <;> fin_cases otherInput <;>
    simp_all <;> decide

/-- One scalar contains all four legal exterior channels.  Matrix entries no
longer choose their own breaking vector. -/
def finiteGenerationJointBreakingScalar :
    ExteriorBreakingScalarCarrier :=
  ∑ output : Fin 2,
    ∑ input : Fin 2,
      finiteGenerationBreakingTensor output input

theorem finiteGenerationJointBreakingScalar_is_genuinely_broken :
    exteriorBreakingScalarRepresentation hyperchargeQuarterTurn
        finiteGenerationJointBreakingScalar ≠
      finiteGenerationJointBreakingScalar := by
  have h01 :
      finiteGenerationScalarIndex 0 0 ≠
        finiteGenerationScalarIndex 0 1 := by decide
  have h10 :
      finiteGenerationScalarIndex 0 0 ≠
        finiteGenerationScalarIndex 1 0 := by decide
  have h11 :
      finiteGenerationScalarIndex 0 0 ≠
        finiteGenerationScalarIndex 1 1 := by decide
  intro fixed
  have coordinateEquality := congrArg
    ((su7ExteriorBasis 4).coord
      (finiteGenerationScalarIndex 0 0)) fixed
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    finiteGenerationBreakingTensor, exteriorBreakingScalarRepresentation,
    hyperchargeQuarterTurn_exterior_basis,
    h01, h10, h11] at coordinateEquality
  have coordinateCharacter_ne_one :
      ((exteriorHyperchargeCharacter quarterTurn
          (finiteGenerationScalarIndex 0 0) : Circle) : ℂ) ≠ 1 := by
    have weight : exteriorHyperchargeWeight
        (finiteGenerationScalarIndex 0 0) = -1 := by decide
    rw [exteriorHyperchargeCharacter_eq_zpow, weight]
    intro equality
    rw [zpow_neg_one] at equality
    rw [Circle.coe_inv_eq_conj] at equality
    have imaginaryEquality := congrArg Complex.im equality
    norm_num [quarterTurn] at imaginaryEquality
  exact coordinateCharacter_ne_one coordinateEquality

/-- Mixing readout of any one scalar on the fixed two-channel input/output
families. -/
def finiteGenerationMassMatrixOfScalar
    (scalar : ExteriorBreakingScalarCarrier) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun output input =>
    finiteGenerationOutputCoordinate output
      (exteriorYukawaMassMap scalar
        (finiteGenerationInputFamily input))

/-- Final finite mixing matrix generated by the one joint scalar. -/
def finiteGenerationJointMassMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  finiteGenerationMassMatrixOfScalar finiteGenerationJointBreakingScalar

theorem finiteGenerationOutputIndex_injective :
    Function.Injective finiteGenerationOutputIndex := by
  decide

@[simp] theorem finiteGenerationOutputCoordinate_basis
    (output target : Fin 2) :
    finiteGenerationOutputCoordinate output
        (su7ExteriorBasis 6 (finiteGenerationOutputIndex target)) =
      if output = target then 1 else 0 := by
  by_cases equal : output = target
  · subst target
    simp [finiteGenerationOutputCoordinate]
  · have indexDifferent :
        finiteGenerationOutputIndex output ≠
          finiteGenerationOutputIndex target :=
      fun equality => equal (finiteGenerationOutputIndex_injective equality)
    simp [finiteGenerationOutputCoordinate, equal, indexDifferent]

theorem finiteGenerationJointBreakingScalar_action
    (input : Fin 2) :
    exteriorYukawaMassMap finiteGenerationJointBreakingScalar
        (finiteGenerationInputFamily input) =
      ∑ output : Fin 2,
        (Set.powersetCard.permOfDisjoint
          (finiteGeneration_pair_disjoint output input)).sign •
          su7ExteriorBasis 6 (finiteGenerationOutputIndex output) := by
  fin_cases input <;>
    simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
      exteriorYukawaMassMap_add_breaking,
      finiteGenerationBreakingTensor_action_sameInput,
      finiteGenerationBreakingTensor_action_otherInput]

/-- The one-scalar matrix agrees entrywise with the earlier channel
calculation.  The earlier per-entry scalar family is now only a proof aid. -/
theorem finiteGenerationJointMassMatrix_entry
    (output input : Fin 2) :
    finiteGenerationJointMassMatrix output input =
      finiteGenerationMassMatrix output input := by
  rw [finiteGenerationJointMassMatrix,
    finiteGenerationMassMatrixOfScalar,
    finiteGenerationJointBreakingScalar_action,
    map_sum, finiteGenerationMassMatrix_entry]
  fin_cases output <;>
    simp [finiteGenerationOutputCoordinate_basis]

theorem finiteGenerationJointMassMatrix_entry_ne_zero
    (output input : Fin 2) :
    finiteGenerationJointMassMatrix output input ≠ 0 := by
  rw [finiteGenerationJointMassMatrix_entry]
  exact finiteGenerationMassMatrix_entry_ne_zero output input

theorem finiteGenerationJointMassMatrix_offDiagonal_nonzero :
    finiteGenerationJointMassMatrix 0 1 ≠ 0 ∧
      finiteGenerationJointMassMatrix 1 0 ≠ 0 :=
  ⟨finiteGenerationJointMassMatrix_entry_ne_zero 0 1,
    finiteGenerationJointMassMatrix_entry_ne_zero 1 0⟩

theorem finiteGenerationJointMassMatrix_not_diagonal :
    finiteGenerationJointMassMatrix ≠
      Matrix.diagonal (fun generation =>
        finiteGenerationJointMassMatrix generation generation) := by
  intro diagonal
  have offDiagonal := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => matrix 0 1) diagonal
  have offDiagonalZero : finiteGenerationJointMassMatrix 0 1 = 0 := by
    simpa [Matrix.diagonal_apply,
      show (0 : Fin 2) ≠ 1 by decide] using offDiagonal
  exact finiteGenerationJointMassMatrix_entry_ne_zero 0 1 offDiagonalZero

theorem finiteGenerationJointBreakingScalar_ne_zero :
    finiteGenerationJointBreakingScalar ≠ 0 := by
  intro scalarZero
  have entryZero : finiteGenerationJointMassMatrix 0 1 = 0 := by
    simp [finiteGenerationJointMassMatrix,
      finiteGenerationMassMatrixOfScalar, scalarZero,
      exteriorYukawaMassMap_zeroBreaking]
  exact finiteGenerationJointMassMatrix_entry_ne_zero 0 1 entryZero

theorem finiteGenerationJointMassMap_ne_zero :
    exteriorYukawaMassMap finiteGenerationJointBreakingScalar ≠ 0 := by
  intro massMapZero
  have entryZero : finiteGenerationJointMassMatrix 0 1 = 0 := by
    simp [finiteGenerationJointMassMatrix,
      finiteGenerationMassMatrixOfScalar, massMapZero]
  exact finiteGenerationJointMassMatrix_entry_ne_zero 0 1 entryZero

/-- The former one-channel scalar is not the joint four-channel scalar.  This
is the algebraic nail used to keep the legacy Stage-8 configuration as a
negative regression. -/
theorem exteriorBreakingScalar_ne_finiteGenerationJointBreakingScalar :
    exteriorBreakingScalar ≠ finiteGenerationJointBreakingScalar := by
  have h00 : exteriorBreakingScalarIndex ≠
      finiteGenerationScalarIndex 0 0 := by decide
  have h01 : exteriorBreakingScalarIndex ≠
      finiteGenerationScalarIndex 0 1 := by decide
  have h10 : exteriorBreakingScalarIndex ≠
      finiteGenerationScalarIndex 1 0 := by decide
  have h11 : exteriorBreakingScalarIndex ≠
      finiteGenerationScalarIndex 1 1 := by decide
  intro equality
  have coordinateEquality := congrArg
    ((su7ExteriorBasis 4).coord exteriorBreakingScalarIndex) equality
  simp [exteriorBreakingScalar, finiteGenerationJointBreakingScalar,
    Fin.sum_univ_two, finiteGenerationBreakingTensor,
    h00, h01, h10, h11] at coordinateEquality

/-- Corrected Stage-8B receipt.  Its distinguished scalar is the same joint
scalar consumed by the mass map and mixing readout below. -/
structure StageEightBJointBreakingYukawaReceipt : Prop where
  scalarCarrier_finrank :
    Module.finrank ℂ ExteriorBreakingScalarCarrier = 35
  jointBreakingScalar_nonzero : finiteGenerationJointBreakingScalar ≠ 0
  actualMotherElement_moves_jointBreakingScalar :
    exteriorBreakingScalarRepresentation hyperchargeQuarterTurn
        finiteGenerationJointBreakingScalar ≠
      finiteGenerationJointBreakingScalar
  yukawaMassMap_equivariant : ∀
      (groupElement : SU7MotherGroup)
      (scalar : ExteriorBreakingScalarCarrier)
      (matter : ExteriorDegreeTwoMatterCarrier),
    exteriorYukawaMassMap
        (exteriorBreakingScalarRepresentation groupElement scalar)
        (su7ExteriorPowerRepresentation 2 groupElement matter) =
      su7ExteriorPowerRepresentation 6 groupElement
        (exteriorYukawaMassMap scalar matter)
  chiralOutput_left : ∀ field : DiracExteriorMatterCarrier,
    diracMatrixMatterAction leftChiralityProjector
        (chiralExteriorYukawaAction finiteGenerationJointBreakingScalar field) =
      chiralExteriorYukawaAction finiteGenerationJointBreakingScalar field
  chiralInput_right : ∀ field : DiracExteriorMatterCarrier,
    chiralExteriorYukawaAction finiteGenerationJointBreakingScalar
        (diracMatrixMatterAction rightChiralityProjector field) =
      chiralExteriorYukawaAction finiteGenerationJointBreakingScalar field
  chiralYukawa_equivariant : ∀ groupElement : SU7MotherGroup,
    (chiralExteriorYukawaAction
        (exteriorBreakingScalarRepresentation groupElement
          finiteGenerationJointBreakingScalar)).comp
          (diracExteriorMatterGaugeRepresentation groupElement) =
      (diracExteriorMatterGaugeRepresentation groupElement).comp
        (chiralExteriorYukawaAction finiteGenerationJointBreakingScalar)

theorem stageEightBJointBreakingYukawaReceipt :
    StageEightBJointBreakingYukawaReceipt where
  scalarCarrier_finrank := exteriorBreakingScalarCarrier_finrank
  jointBreakingScalar_nonzero := finiteGenerationJointBreakingScalar_ne_zero
  actualMotherElement_moves_jointBreakingScalar :=
    finiteGenerationJointBreakingScalar_is_genuinely_broken
  yukawaMassMap_equivariant := exteriorYukawaMassMap_su7_equivariant
  chiralOutput_left :=
    chiralExteriorYukawaAction_output_left finiteGenerationJointBreakingScalar
  chiralInput_right :=
    chiralExteriorYukawaAction_consumes_right
      finiteGenerationJointBreakingScalar
  chiralYukawa_equivariant := fun groupElement =>
    chiralExteriorYukawaAction_su7_equivariant groupElement
      finiteGenerationJointBreakingScalar

/-- Corrected Stage-8C receipt: mass map and every mixing entry consume one
and the same breaking scalar. -/
structure StageEightCJointMassMixingReceipt : Prop where
  jointScalar_nonzero : finiteGenerationJointBreakingScalar ≠ 0
  jointMassMap_nonzero :
    exteriorYukawaMassMap finiteGenerationJointBreakingScalar ≠ 0
  mixing_from_same_scalar :
    finiteGenerationJointMassMatrix =
      finiteGenerationMassMatrixOfScalar
        finiteGenerationJointBreakingScalar
  finiteMixing_offDiagonal :
    finiteGenerationJointMassMatrix 0 1 ≠ 0 ∧
      finiteGenerationJointMassMatrix 1 0 ≠ 0
  finiteMixing_notDiagonal :
    finiteGenerationJointMassMatrix ≠
      Matrix.diagonal (fun generation =>
        finiteGenerationJointMassMatrix generation generation)
  noBreaking_noMass :
    exteriorYukawaMassMap (0 : ExteriorBreakingScalarCarrier) = 0

theorem stageEightCJointMassMixingReceipt :
    StageEightCJointMassMixingReceipt where
  jointScalar_nonzero := finiteGenerationJointBreakingScalar_ne_zero
  jointMassMap_nonzero := finiteGenerationJointMassMap_ne_zero
  mixing_from_same_scalar := rfl
  finiteMixing_offDiagonal :=
    finiteGenerationJointMassMatrix_offDiagonal_nonzero
  finiteMixing_notDiagonal :=
    finiteGenerationJointMassMatrix_not_diagonal
  noBreaking_noMass := exteriorYukawaMassMap_zeroBreaking

/-! ## Proof-only Stage-8C receipt -/

structure StageEightCMassMixingReceipt : Prop where
  generatedMass_rank :
    Module.finrank ℂ
        (LinearMap.range
          (exteriorYukawaMassMap exteriorBreakingScalar)) = 3
  generatedMass_kernel_finrank :
    Module.finrank ℂ
        (LinearMap.ker
          (exteriorYukawaMassMap exteriorBreakingScalar)) = 18
  generatedMass_exactRange :
    LinearMap.range
        (exteriorYukawaMassMap exteriorBreakingScalar) =
      exteriorMassiveOutputSubspace
  generatedMass_nonzero :
    exteriorYukawaMassMap exteriorBreakingScalar
        exteriorYukawaDegreeTwoProbe ≠ 0
  noBreaking_noMass :
    exteriorYukawaMassMap (0 : ExteriorBreakingScalarCarrier) = 0
  finiteMixing_offDiagonal :
    finiteGenerationMassMatrix 0 1 ≠ 0 ∧
      finiteGenerationMassMatrix 1 0 ≠ 0
  finiteMixing_notDiagonal :
    finiteGenerationMassMatrix ≠
      Matrix.diagonal (fun generation =>
        finiteGenerationMassMatrix generation generation)

theorem stageEightCMassMixingReceipt :
    StageEightCMassMixingReceipt where
  generatedMass_rank := exteriorYukawaMassMap_rank
  generatedMass_kernel_finrank :=
    exteriorYukawaMassMap_kernel_finrank
  generatedMass_exactRange :=
    exteriorYukawaMassMap_range_eq_massiveOutput
  generatedMass_nonzero := exteriorYukawaProbe_massMap_ne_zero
  noBreaking_noMass := exteriorYukawaMassMap_zeroBreaking
  finiteMixing_offDiagonal :=
    finiteGenerationMassMatrix_offDiagonal_nonzero
  finiteMixing_notDiagonal := finiteGenerationMassMatrix_not_diagonal

end
end SaturationMonoid.PhysicsCore.SU7ExteriorYukawaMassSpectrum
