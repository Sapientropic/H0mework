import H0mework.Physics.Dirac.FullDiracAdjointProfileOperatorResidual
import H0mework.Physics.Exterior.ExteriorMotherLieRepresentation
import H0mework.Physics.Matter.ExteriorYukawaHermitianCompletion
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Full exterior-material local formal-adjoint operator

This module works directly on the full exterior carrier.  It does not use the
P286 restriction, a time-axis specialization, or a supplied pairing/balance
premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore
namespace StageNineFullDiracAdjointLocalOperator

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open Matrix
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineEnrichedProofFreeSource
open StageNineExteriorYukawaHermitianCompletion
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineFullDiracAdjointMaterial
open StageNineFullDiracAdjointCoupledTemporalResidual
open StageNineFullDiracAdjointProfileResidual
open StageNineFullDiracAdjointProfileOperatorResidual
open StageNineExteriorMotherLieRepresentation
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTimeVelocity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra

noncomputable section

open scoped ContDiff

local instance su7MotherIndexLinearOrder : LinearOrder SU7MotherIndex :=
  SU7ExteriorMatterRestriction.instLinearOrderSU7MotherIndex

private theorem exteriorCoordinatePair_add_left
    (degree : Nat)
    (first second right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (first + second) right =
      exteriorCoordinatePair degree first right +
        exteriorCoordinatePair degree second right := by
  simp [exteriorCoordinatePair, Finset.sum_add_distrib, add_mul]

private theorem exteriorCoordinatePair_add_right
    (degree : Nat)
    (left first second : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (first + second) =
      exteriorCoordinatePair degree left first +
        exteriorCoordinatePair degree left second := by
  simp [exteriorCoordinatePair, Finset.sum_add_distrib, mul_add]

private theorem exteriorCoordinatePair_smul_left
    (degree : Nat) (scalar : ℂ)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (scalar • left) right =
      starRingEnd ℂ scalar * exteriorCoordinatePair degree left right := by
  unfold exteriorCoordinatePair
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [mul_assoc]

private theorem exteriorCoordinatePair_smul_right
    (degree : Nat) (scalar : ℂ)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (scalar • right) =
      scalar * exteriorCoordinatePair degree left right := by
  unfold exteriorCoordinatePair
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

private theorem fullInternalPair_add_left
    (first second right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (first + second) right =
      fullInternalPair first right + fullInternalPair second right := by
  simp [fullInternalPair, exteriorCoordinatePair_add_left]
  ring

private theorem fullInternalPair_smul_left
    (scalar : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (scalar • left) right =
      starRingEnd ℂ scalar * fullInternalPair left right := by
  simp [fullInternalPair, exteriorCoordinatePair_smul_left]
  ring

private theorem fullInternalPair_add_right
    (left first second : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair left (first + second) =
      fullInternalPair left first + fullInternalPair left second := by
  simp [fullInternalPair, exteriorCoordinatePair_add_right]
  ring

private theorem fullInternalPair_smul_right
    (scalar : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair left (scalar • right) =
      scalar * fullInternalPair left right := by
  simp [fullInternalPair, exteriorCoordinatePair_smul_right]
  ring

@[simp] private theorem fullInternalPair_zero_left
    (right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair 0 right = 0 := by
  simp [fullInternalPair, exteriorCoordinatePair]

@[simp] private theorem fullInternalPair_zero_right
    (left : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair left 0 = 0 := by
  simp [fullInternalPair, exteriorCoordinatePair]

private theorem fullCanonicalDiracAdjoint_apply_explicit
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint matter candidate =
      fullInternalPair (matter 2) (candidate 0) +
      fullInternalPair (matter 3) (candidate 1) +
      fullInternalPair (matter 0) (candidate 2) +
      fullInternalPair (matter 1) (candidate 3) := by
  change
    (∑ spin : DiracSpinorIndex,
      fullInternalPair
        (diracMatrixMatterAction diracAdjointSpinSwap matter spin)
        (candidate spin)) = _
  simp [diracAdjointSpinSwap, diracMatrixMatterAction,
    Fin.sum_univ_four]

/-- The canonical full adjoint turns every identity-coframe Dirac principal
into minus dual precomposition by that same principal. -/
theorem fullCanonicalDiracAdjoint_identityPrincipal
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (identityCoframeMatterPrincipal direction matter) =
      -(fullCanonicalDiracAdjoint matter).comp
        (identityCoframeMatterPrincipal direction) := by
  apply LinearMap.ext
  intro candidate
  fin_cases direction <;>
    simp only [LinearMap.neg_apply, LinearMap.comp_apply] <;>
    rw [fullCanonicalDiracAdjoint_apply_explicit] <;>
    simp [identityCoframeMatterPrincipal,
      diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four,
      fullInternalPair_smul_left,
      fullInternalPair_smul_right,
      fullCanonicalDiracAdjoint_apply_explicit] <;>
    ring

/-- Each concrete gamma matrix is self-adjoint for the canonical Dirac
pairing (the minus sign in the principal law comes only from conjugating
`Complex.I`). -/
theorem fullCanonicalDiracAdjoint_gamma
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction (diracGamma direction) matter) =
      (fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction (diracGamma direction)) := by
  apply LinearMap.ext
  intro candidate
  fin_cases direction <;>
    simp only [LinearMap.comp_apply] <;>
    rw [fullCanonicalDiracAdjoint_apply_explicit] <;>
    simp [diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, fullInternalPair_smul_left,
      fullInternalPair_smul_right,
      fullCanonicalDiracAdjoint_apply_explicit] <;>
    ring

/-- Formal adjunction reverses a product of concrete gamma actions. -/
theorem fullCanonicalDiracAdjoint_gammaProduct
    (first second : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction
          (diracGamma first * diracGamma second) matter) =
      ((fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction (diracGamma second))).comp
          (diracMatrixMatterAction (diracGamma first)) := by
  rw [diracMatrixMatterAction_mul]
  change
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction (diracGamma first)
          (diracMatrixMatterAction (diracGamma second) matter)) = _
  rw [fullCanonicalDiracAdjoint_gamma,
    fullCanonicalDiracAdjoint_gamma]

/-- Every oriented Lorentz bivector used by the spin connection is
skew-adjoint for the full canonical Dirac pairing. -/
theorem fullCanonicalDiracAdjoint_gammaBivector
    (pair : Fin 6) (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction
          (diracGamma (lorentzBivectorFirst pair) *
            diracGamma (lorentzBivectorSecond pair)) matter) =
      -(fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction
          (diracGamma (lorentzBivectorFirst pair) *
            diracGamma (lorentzBivectorSecond pair))) := by
  rw [fullCanonicalDiracAdjoint_gammaProduct]
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.neg_apply, LinearMap.comp_apply]
  fin_cases pair <;>
    simp [lorentzBivectorFirst, lorentzBivectorSecond,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      diracMatrixMatterAction, Fin.sum_univ_four,
      fullCanonicalDiracAdjoint_apply_explicit,
      fullInternalPair_smul_right] <;>
    ring

private theorem diracMatrixMatterAction_sum_matrix
    {Index : Type} [Fintype Index]
    (matrix : Index → DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (∑ index, matrix index) matter =
      ∑ index, diracMatrixMatterAction (matrix index) matter := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty =>
      funext row
      simp [diracMatrixMatterAction]
  | @insert index indices hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
        diracMatrixMatterAction_add_matrix, ih]

private theorem fullCanonicalDiracAdjoint_sum
    {Index : Type} [Fintype Index]
    (matter : Index → DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (∑ index, matter index) =
      ∑ index, fullCanonicalDiracAdjoint (matter index) := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simp
  | @insert index indices hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
        fullCanonicalDiracAdjoint_add, ih]

private theorem spinLiftTerm_formalAdjoint
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) (pair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    let coefficient : ℂ :=
      (2 : ℂ)⁻¹ *
        (loweredLorentzConnectionCoefficient connection direction pair : ℂ)
    let bivector :=
      diracGamma (lorentzBivectorFirst pair) *
        diracGamma (lorentzBivectorSecond pair)
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction (coefficient • bivector) matter) =
      -(fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction (coefficient • bivector)) := by
  dsimp only
  rw [diracMatrixMatterAction_smul_matrix,
    fullCanonicalDiracAdjoint_smul,
    fullCanonicalDiracAdjoint_gammaBivector]
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.comp_apply]
  rw [diracMatrixMatterAction_smul_matrix]
  have coefficientStar :
      starRingEnd ℂ
          ((2 : ℂ)⁻¹ *
            (loweredLorentzConnectionCoefficient connection direction pair : ℂ)) =
        (2 : ℂ)⁻¹ *
          (loweredLorentzConnectionCoefficient connection direction pair : ℂ) := by
    rw [starRingEnd_apply, star_mul, star_inv₀]
    norm_num
    ring
  rw [coefficientStar]
  rw [map_smul]
  ring

/-- The source-generated Lorentz spin connection is skew-adjoint on the full
exterior matter carrier. -/
theorem fullCanonicalDiracAdjoint_spinConnection
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction
          (diracSpinConnectionLift connection direction) matter) =
      -(fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction
          (diracSpinConnectionLift connection direction)) := by
  unfold diracSpinConnectionLift
  rw [diracMatrixMatterAction_sum_matrix,
    fullCanonicalDiracAdjoint_sum]
  simp_rw [spinLiftTerm_formalAdjoint connection direction]
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.sum_apply, LinearMap.neg_apply,
    LinearMap.comp_apply]
  rw [diracMatrixMatterAction_sum_matrix, map_sum]
  rw [Finset.sum_neg_distrib]

/-! ## Full exterior SU(7) pairing law -/

private theorem sum_det_updateCol_transpose_eq_sum_det_updateRow
    {n : Type*} [Fintype n] [DecidableEq n]
    (base variation : Matrix n n ℂ) :
    (∑ index : n,
        (base.updateCol index (variationᵀ index)).det) =
      ∑ index : n,
        (base.updateRow index (variation index)).det := by
  calc
    _ = ∑ index : n, ∑ other : n,
          base.adjugate index other * variation other index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← Matrix.cramer_apply base (variationᵀ index) index,
        Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mulVec, dotProduct]
    _ = ∑ index : n, ∑ other : n,
          base.adjugate other index * variation index other := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← Matrix.cramer_transpose_apply base (variation index) index,
        Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mulVec, dotProduct, ← Matrix.adjugate_transpose]

private theorem star_sum_det_updateRow
    {n : Type*} [Fintype n] [DecidableEq n]
    (base variation : Matrix n n ℂ) :
    star (∑ index : n,
        (base.updateRow index (variation index)).det) =
      ∑ index : n,
        (baseᴴ.updateRow index (variationᴴ index)).det := by
  calc
    _ = ∑ index : n,
          star ((base.updateRow index (variation index)).det) := by
      rw [star_sum]
    _ = ∑ index : n,
          ((base.updateRow index (variation index))ᴴ).det := by
      apply Finset.sum_congr rfl
      intro index _
      exact (Matrix.det_conjTranspose
        (base.updateRow index (variation index))).symm
    _ = ∑ index : n,
          (baseᴴ.updateCol index ((variationᴴ)ᵀ index)).det := by
      apply Finset.sum_congr rfl
      intro index _
      apply congrArg Matrix.det
      rw [← Matrix.updateCol_conjTranspose]
      congr 1
    _ = _ :=
      sum_det_updateCol_transpose_eq_sum_det_updateRow baseᴴ variationᴴ

private def exteriorBasisCoordinateMatrix
    (degree : Nat)
    (output input : ExteriorBasisIndex degree) :
    Matrix (Fin degree) (Fin degree) ℂ :=
  Matrix.of fun inputPosition outputPosition =>
    (su7FundamentalBasis.repr
      (exteriorBasisInput degree input inputPosition))
        (exteriorPositionEquiv output outputPosition).1

private def exteriorBasisActionCoordinateRow
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (output input : ExteriorBasisIndex degree)
    (inputPosition : Fin degree) : Fin degree → ℂ :=
  fun outputPosition =>
    (su7FundamentalBasis.repr
      (fundamentalMotherLieAction matrix
        (exteriorBasisInput degree input inputPosition)))
      (exteriorPositionEquiv output outputPosition).1

private def exteriorBasisActionCoordinateMatrix
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (output input : ExteriorBasisIndex degree) :
    Matrix (Fin degree) (Fin degree) ℂ :=
  Matrix.of
    (exteriorBasisActionCoordinateRow degree matrix output input)

private theorem exteriorBasisLieAction_coordinate_eq_sum_det_updateRow
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (output input : ExteriorBasisIndex degree) :
    (su7ExteriorBasis degree).repr
        (exteriorBasisLieAction degree matrix input) output =
      ∑ position : Fin degree,
        ((exteriorBasisCoordinateMatrix degree output input).updateRow
          position
          (exteriorBasisActionCoordinateRow degree matrix output input
            position)).det := by
  unfold exteriorBasisLieAction
  change
    (su7ExteriorBasis degree).repr
        (∑ position : Fin degree,
          (exteriorPower.ιMulti ℂ degree)
            (exteriorBasisLieActionInput degree matrix input position))
        output = _
  rw [map_sum]
  simp_rw [exteriorBasisLieActionTerm_eq_update]
  rw [Finset.sum_apply']
  change
    (∑ position : Fin degree,
      (su7FundamentalBasis.exteriorPower degree).repr
        ((exteriorPower.ιMulti ℂ degree)
          (Function.update (exteriorBasisInput degree input) position
            (fundamentalMotherLieAction matrix
              (exteriorBasisInput degree input position)))) output) = _
  simp_rw [exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro position _
  have outputPositionValue (candidate : Fin degree) :
      Set.powersetCard.ofFinEmbEquiv.symm output candidate =
        (exteriorPositionEquiv output candidate).1 := by
    rfl
  apply congrArg Matrix.det
  ext row column
  by_cases equality : row = position
  · subst row
    simp [exteriorBasisCoordinateMatrix,
      exteriorBasisActionCoordinateRow, exteriorBasisInput,
      outputPositionValue]
  · simp [exteriorBasisCoordinateMatrix, exteriorBasisInput,
      equality, outputPositionValue]

private theorem fundamentalMotherLieAction_basis_coordinate
    (matrix : SU7MotherLieMatrix) (output input : SU7MotherIndex) :
    (su7FundamentalBasis.repr
        (fundamentalMotherLieAction matrix (su7FundamentalBasis input)))
        output =
      (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) output input := by
  simp [fundamentalMotherLieAction, su7FundamentalBasis, Matrix.mulVecLin]

private theorem exteriorBasisCoordinateMatrix_conjTranspose
    (degree : Nat) (output input : ExteriorBasisIndex degree) :
    (exteriorBasisCoordinateMatrix degree output input)ᴴ =
      exteriorBasisCoordinateMatrix degree input output := by
  ext row column
  by_cases equality :
      (exteriorPositionEquiv output row).1 =
        (exteriorPositionEquiv input column).1
  · simp [exteriorBasisCoordinateMatrix, exteriorBasisInput, equality]
  · simp [exteriorBasisCoordinateMatrix, exteriorBasisInput, equality,
      Ne.symm equality]

private theorem exteriorBasisActionCoordinateMatrix_conjTranspose
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (output input : ExteriorBasisIndex degree) :
    (exteriorBasisActionCoordinateMatrix degree matrix output input)ᴴ =
      -exteriorBasisActionCoordinateMatrix degree matrix input output := by
  ext row column
  have starEntry := congrArg
    (fun candidate : Matrix SU7MotherIndex SU7MotherIndex ℂ =>
      candidate (exteriorPositionEquiv input column).1
        (exteriorPositionEquiv output row).1)
    (specialUnitaryLieMatrix_star matrix)
  simpa [exteriorBasisActionCoordinateMatrix,
    exteriorBasisActionCoordinateRow, exteriorBasisInput,
    fundamentalMotherLieAction_basis_coordinate, star_eq_conjTranspose,
    Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.neg_apply] using
      starEntry

private theorem exteriorBasisLieAction_coordinate_eq_sum_det_updateRow_matrix
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (output input : ExteriorBasisIndex degree) :
    (su7ExteriorBasis degree).repr
        (exteriorBasisLieAction degree matrix input) output =
      ∑ position : Fin degree,
        ((exteriorBasisCoordinateMatrix degree output input).updateRow
          position
          ((exteriorBasisActionCoordinateMatrix degree matrix output input)
            position)).det := by
  rw [exteriorBasisLieAction_coordinate_eq_sum_det_updateRow]
  apply Finset.sum_congr rfl
  intro position _
  apply congrArg Matrix.det
  congr 1

/-- The derived action on every exterior degree is skew-adjoint in the
explicit exterior basis. -/
theorem exteriorBasisLieAction_coordinate_star
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (output input : ExteriorBasisIndex degree) :
    star ((su7ExteriorBasis degree).repr
      (exteriorBasisLieAction degree matrix input) output) =
      -((su7ExteriorBasis degree).repr
        (exteriorBasisLieAction degree matrix output) input) := by
  rw [exteriorBasisLieAction_coordinate_eq_sum_det_updateRow_matrix,
    exteriorBasisLieAction_coordinate_eq_sum_det_updateRow_matrix,
    star_sum_det_updateRow,
    exteriorBasisCoordinateMatrix_conjTranspose]
  have conjugateEntry (row column : Fin degree) :
      (exteriorBasisActionCoordinateMatrix degree matrix output input)ᴴ
          row column =
        -(exteriorBasisActionCoordinateMatrix degree matrix input output
          row column) :=
    congrArg
      (fun candidate : Matrix (Fin degree) (Fin degree) ℂ =>
        candidate row column)
      (exteriorBasisActionCoordinateMatrix_conjTranspose
        degree matrix output input)
  calc
    _ = ∑ position : Fin degree,
        ((exteriorBasisCoordinateMatrix degree input output).updateRow
          position
          (fun column =>
            -(exteriorBasisActionCoordinateMatrix degree matrix input output
              position column))).det := by
      apply Finset.sum_congr rfl
      intro position _
      apply congrArg Matrix.det
      congr 1
      funext column
      exact conjugateEntry position column
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro position _
      have negRow :
          (fun column =>
              -(exteriorBasisActionCoordinateMatrix degree matrix input output
                position column)) =
            (-1 : ℂ) •
              exteriorBasisActionCoordinateMatrix degree matrix input output
                position := by
        funext column
        simp
      rw [negRow, Matrix.det_updateRow_smul]
      simp

private theorem exteriorCoordinatePair_basis_action_left
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (input output : ExteriorBasisIndex degree) :
    exteriorCoordinatePair degree
        (exteriorMotherLieAction degree matrix
          (su7ExteriorBasis degree input))
        (su7ExteriorBasis degree output) =
      star ((su7ExteriorBasis degree).repr
        (exteriorBasisLieAction degree matrix input) output) := by
  rw [exteriorMotherLieAction_basis_slot]
  unfold exteriorCoordinatePair
  rw [Finset.sum_eq_single output]
  · simp
  · intro candidate _ notEqual
    simp [notEqual]
  · simp

private theorem exteriorCoordinatePair_basis_action_right
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (input output : ExteriorBasisIndex degree) :
    exteriorCoordinatePair degree
        (su7ExteriorBasis degree input)
        (exteriorMotherLieAction degree matrix
          (su7ExteriorBasis degree output)) =
      (su7ExteriorBasis degree).repr
        (exteriorBasisLieAction degree matrix output) input := by
  rw [exteriorMotherLieAction_basis_slot]
  unfold exteriorCoordinatePair
  rw [Finset.sum_eq_single input]
  · simp
  · intro candidate _ notEqual
    simp [notEqual]
  · simp

private theorem exteriorCoordinatePair_basis_action_skew
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (input output : ExteriorBasisIndex degree) :
    exteriorCoordinatePair degree
        (exteriorMotherLieAction degree matrix
          (su7ExteriorBasis degree input))
        (su7ExteriorBasis degree output) +
      exteriorCoordinatePair degree
        (su7ExteriorBasis degree input)
        (exteriorMotherLieAction degree matrix
          (su7ExteriorBasis degree output)) = 0 := by
  rw [exteriorCoordinatePair_basis_action_left,
    exteriorCoordinatePair_basis_action_right,
    exteriorBasisLieAction_coordinate_star degree matrix output input]
  simp

private theorem exteriorCoordinatePair_sum_left
    {Index : Type} [Fintype Index]
    (degree : Nat)
    (left : Index → ⋀[ℂ]^degree SU7FundamentalCarrier)
    (right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree (∑ index, left index) right =
      ∑ index, exteriorCoordinatePair degree (left index) right := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simp [exteriorCoordinatePair]
  | @insert index indices hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
        exteriorCoordinatePair_add_left, ih]

private theorem exteriorCoordinatePair_sum_right
    {Index : Type} [Fintype Index]
    (degree : Nat)
    (left : ⋀[ℂ]^degree SU7FundamentalCarrier)
    (right : Index → ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree left (∑ index, right index) =
      ∑ index, exteriorCoordinatePair degree left (right index) := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simp [exteriorCoordinatePair]
  | @insert index indices hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
        exteriorCoordinatePair_add_right, ih]

/-- The actual SU(7) mother Lie action is skew for the canonical coordinate
pairing on every exterior degree, not only on a selected subcarrier. -/
theorem exteriorCoordinatePair_motherLie_skew
    (degree : Nat) (matrix : SU7MotherLieMatrix)
    (left right : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorCoordinatePair degree
        (exteriorMotherLieAction degree matrix left) right +
      exteriorCoordinatePair degree left
        (exteriorMotherLieAction degree matrix right) = 0 := by
  classical
  rw [← (su7ExteriorBasis degree).sum_repr left,
    ← (su7ExteriorBasis degree).sum_repr right]
  simp only [map_sum, map_smul]
  rw [exteriorCoordinatePair_sum_left,
    exteriorCoordinatePair_sum_right]
  simp_rw [exteriorCoordinatePair_sum_right,
    exteriorCoordinatePair_sum_left,
    exteriorCoordinatePair_smul_left,
    exteriorCoordinatePair_smul_right]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro input _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro output _
  rw [← mul_add]
  rw [← mul_add]
  rw [exteriorCoordinatePair_basis_action_skew]
  simp

/-- The block sum `Λ⁶ ⊕ Λ² ⊕ Λ⁴` inherits the same skew pairing law. -/
theorem fullInternalPair_motherLie_skew
    (matrix : SU7MotherLieMatrix)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (exteriorSpinorMotherLieAction matrix left) right +
      fullInternalPair left (exteriorSpinorMotherLieAction matrix right) =
        0 := by
  rcases left with ⟨leftSix, leftTwo, leftFour⟩
  rcases right with ⟨rightSix, rightTwo, rightFour⟩
  have degreeSix := exteriorCoordinatePair_motherLie_skew 6 matrix
    leftSix rightSix
  have degreeTwo := exteriorCoordinatePair_motherLie_skew 2 matrix
    leftTwo rightTwo
  have degreeFour := exteriorCoordinatePair_motherLie_skew 4 matrix
    leftFour rightFour
  change
    (exteriorCoordinatePair 6
        (exteriorMotherLieAction 6 matrix leftSix) rightSix +
      exteriorCoordinatePair 2
        (exteriorMotherLieAction 2 matrix leftTwo) rightTwo +
      exteriorCoordinatePair 4
        (exteriorMotherLieAction 4 matrix leftFour) rightFour) +
    (exteriorCoordinatePair 6 leftSix
        (exteriorMotherLieAction 6 matrix rightSix) +
      exteriorCoordinatePair 2 leftTwo
        (exteriorMotherLieAction 2 matrix rightTwo) +
      exteriorCoordinatePair 4 leftFour
        (exteriorMotherLieAction 4 matrix rightFour)) = 0
  linear_combination degreeSix + degreeTwo + degreeFour

/-- The full SU(7) mother connection is skew-adjoint for the canonical full
Dirac adjoint, with no restriction to a selected matter subspace. -/
theorem fullCanonicalDiracAdjoint_motherLieConnection
    (matrix : SU7MotherLieMatrix)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracExteriorMotherLieAction matrix matter) =
      -(fullCanonicalDiracAdjoint matter).comp
        (diracExteriorMotherLieAction matrix) := by
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.neg_apply, LinearMap.comp_apply]
  rw [fullCanonicalDiracAdjoint_apply_explicit,
    fullCanonicalDiracAdjoint_apply_explicit]
  change
    fullInternalPair
          (exteriorSpinorMotherLieAction matrix (matter 2)) (candidate 0) +
      fullInternalPair
          (exteriorSpinorMotherLieAction matrix (matter 3)) (candidate 1) +
      fullInternalPair
          (exteriorSpinorMotherLieAction matrix (matter 0)) (candidate 2) +
      fullInternalPair
          (exteriorSpinorMotherLieAction matrix (matter 1)) (candidate 3) =
    -(fullInternalPair (matter 2)
          (exteriorSpinorMotherLieAction matrix (candidate 0)) +
      fullInternalPair (matter 3)
          (exteriorSpinorMotherLieAction matrix (candidate 1)) +
      fullInternalPair (matter 0)
          (exteriorSpinorMotherLieAction matrix (candidate 2)) +
      fullInternalPair (matter 1)
          (exteriorSpinorMotherLieAction matrix (candidate 3)))
  have spinZero := fullInternalPair_motherLie_skew matrix
    (matter 2) (candidate 0)
  have spinOne := fullInternalPair_motherLie_skew matrix
    (matter 3) (candidate 1)
  have spinTwo := fullInternalPair_motherLie_skew matrix
    (matter 0) (candidate 2)
  have spinThree := fullInternalPair_motherLie_skew matrix
    (matter 1) (candidate 3)
  linear_combination spinZero + spinOne + spinTwo + spinThree

/-- Gravity and gauge connection actions combine into the exact skew
connection operator consumed by the live adjoint equation. -/
theorem fullCanonicalDiracAdjoint_connectionAction
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    fullCanonicalDiracAdjoint
        (holonomicMatterConnectionAction configuration point direction) =
      -(fullCanonicalDiracAdjoint (configuration.matter point)).comp
        (holonomicIdentityCoframeMatterConnectionOperator
          configuration point direction) := by
  unfold holonomicMatterConnectionAction
    holonomicIdentityCoframeMatterConnectionOperator
  rw [fullCanonicalDiracAdjoint_add,
    fullCanonicalDiracAdjoint_spinConnection,
    fullCanonicalDiracAdjoint_motherLieConnection]
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, map_add]
  ring

/-- The actual internal Hermitian adjoint reverses the Yukawa arrow
`Λ⁶ → Λ²`. -/
def exteriorYukawaInternalHermitianAdjoint
    (scalar : ExteriorBreakingScalarCarrier) :
    Module.End ℂ SU7ExteriorSpinorMatterCarrier where
  toFun matter :=
    (0, (exteriorYukawaMassAdjoint scalar matter.1, 0))
  map_add' first second := by simp
  map_smul' coefficient matter := by simp

theorem exteriorYukawaInternalHermitianAdjoint_spec
    (scalar : ExteriorBreakingScalarCarrier)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (exteriorYukawaInternalAction scalar left) right =
      fullInternalPair left
        (exteriorYukawaInternalHermitianAdjoint scalar right) := by
  rcases left with ⟨leftSix, leftTwo, leftFour⟩
  rcases right with ⟨rightSix, rightTwo, rightFour⟩
  unfold fullInternalPair exteriorYukawaInternalAction
    exteriorYukawaInternalHermitianAdjoint
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simpa [exteriorCoordinatePair] using
    exteriorYukawaMassAdjoint_spec scalar leftTwo rightSix

/-- Dirac-wise lift of the missing internal Hermitian adjoint. -/
def diracExteriorYukawaInternalHermitianAdjoint
    (scalar : ExteriorBreakingScalarCarrier) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  internalMatterLinearAction
    (exteriorYukawaInternalHermitianAdjoint scalar)

theorem fullCanonicalDiracAdjoint_internalYukawa
    (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracExteriorYukawaInternalAction scalar matter) =
      (fullCanonicalDiracAdjoint matter).comp
        (diracExteriorYukawaInternalHermitianAdjoint scalar) := by
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.comp_apply]
  rw [fullCanonicalDiracAdjoint_apply_explicit,
    fullCanonicalDiracAdjoint_apply_explicit]
  change
    fullInternalPair
          (exteriorYukawaInternalAction scalar (matter 2)) (candidate 0) +
      fullInternalPair
          (exteriorYukawaInternalAction scalar (matter 3)) (candidate 1) +
      fullInternalPair
          (exteriorYukawaInternalAction scalar (matter 0)) (candidate 2) +
      fullInternalPair
          (exteriorYukawaInternalAction scalar (matter 1)) (candidate 3) =
    fullInternalPair (matter 2)
          (exteriorYukawaInternalHermitianAdjoint scalar (candidate 0)) +
      fullInternalPair (matter 3)
          (exteriorYukawaInternalHermitianAdjoint scalar (candidate 1)) +
      fullInternalPair (matter 0)
          (exteriorYukawaInternalHermitianAdjoint scalar (candidate 2)) +
      fullInternalPair (matter 1)
          (exteriorYukawaInternalHermitianAdjoint scalar (candidate 3))
  simp_rw [exteriorYukawaInternalHermitianAdjoint_spec]

/-- Dirac conjugation exchanges right and left chirality. -/
theorem fullCanonicalDiracAdjoint_rightChirality
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracMatrixMatterAction rightChiralityProjector matter) =
      (fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction leftChiralityProjector) := by
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.comp_apply]
  rw [fullCanonicalDiracAdjoint_apply_explicit]
  simp [rightChiralityProjector, leftChiralityProjector,
    diracGammaFive, diracMatrixMatterAction, Fin.sum_univ_four,
    fullInternalPair_smul_left, fullInternalPair_smul_right,
    fullCanonicalDiracAdjoint_apply_explicit,
    starRingEnd_apply, star_ofNat,
    fullInternalPair_zero_left, fullInternalPair_zero_right]

/-- Correct full-carrier adjoint of the installed right-chiral Yukawa map:
the internal arrow reverses `Λ⁶ → Λ²` and right chirality becomes left. -/
def diracDualRightChiralYukawaHermitianAdjoint
    (scalar : ExteriorBreakingScalarCarrier) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  (diracExteriorYukawaInternalHermitianAdjoint scalar).comp
    (diracMatrixMatterAction leftChiralityProjector)

theorem fullCanonicalDiracAdjoint_rightChiralYukawa
    (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint
        (diracDualRightChiralYukawaAction scalar matter) =
      (fullCanonicalDiracAdjoint matter).comp
        (diracDualRightChiralYukawaHermitianAdjoint scalar) := by
  unfold diracDualRightChiralYukawaAction
    diracDualRightChiralYukawaHermitianAdjoint
  simp only [LinearMap.comp_apply]
  rw [fullCanonicalDiracAdjoint_internalYukawa,
    fullCanonicalDiracAdjoint_rightChirality]
  have commute :=
    diracMatrixMatterAction_commutes_internal leftChiralityProjector
      (exteriorYukawaInternalHermitianAdjoint scalar)
  apply LinearMap.ext
  intro candidate
  have commuteAt := LinearMap.congr_fun commute candidate
  simp only [LinearMap.comp_apply] at commuteAt ⊢
  exact congrArg (fullCanonicalDiracAdjoint matter) commuteAt

private theorem fullCanonicalDiracAdjoint_neg
    (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (-matter) =
      -fullCanonicalDiracAdjoint matter := by
  apply eq_neg_of_add_eq_zero_right
  rw [← fullCanonicalDiracAdjoint_add]
  simp

private theorem fullCanonicalDiracAdjoint_sub
    (first second : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (first - second) =
      fullCanonicalDiracAdjoint first -
        fullCanonicalDiracAdjoint second := by
  rw [sub_eq_add_neg, fullCanonicalDiracAdjoint_add,
    fullCanonicalDiracAdjoint_neg]
  rfl

/-- Difference between the installed adjoint operator and the Hermitian
formal adjoint of the primal operator. -/
def fullDiracInstalledOrientationDefect
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  (∑ direction : LorentzianIndex,
      ((identityCoframeMatterPrincipal direction).comp
          (holonomicIdentityCoframeMatterConnectionOperator
            configuration point direction) -
        (holonomicIdentityCoframeMatterConnectionOperator
          configuration point direction).comp
            (identityCoframeMatterPrincipal direction))) +
    (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (configuration.scalar point)) -
      diracDualRightChiralYukawaHermitianAdjoint
        (scalarCoordinateEquiv.symm (configuration.scalar point)))

/-- Generic identity-coframe response residual before specializing to the
fixed Restart occurrence. -/
def fullDiracIdentityResponseResidual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
      configuration point).comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) -
    fullCanonicalDiracAdjoint
      (-identityCoframeMatterTimePrincipal
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            configuration point) -
        holonomicMatterConnectionAction configuration point
          canonicalLorentzianTimeDirection)

private theorem fullCanonicalDiracAdjoint_covariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex)
    (valuePairing :
      configuration.conjugateMatter point =
        fullCanonicalDiracAdjoint (configuration.matter point))
    (derivativePairing :
      holonomicConjugateMatterDerivativeDual configuration point direction =
        fullCanonicalDiracAdjoint
          (matterCoordinateEquiv.symm
            (fieldDirectionalDerivative
              (fun candidate =>
                matterCoordinateEquiv (configuration.matter candidate))
              point direction))) :
    fullCanonicalDiracAdjoint
        (holonomicMatterCovariantDerivative configuration point direction) =
      holonomicConjugateMatterDerivativeDual configuration point direction -
        (configuration.conjugateMatter point).comp
          (holonomicIdentityCoframeMatterConnectionOperator
            configuration point direction) := by
  have covariantDerivativeEq :
      holonomicMatterCovariantDerivative configuration point direction =
        matterCoordinateEquiv.symm
            (fieldDirectionalDerivative
              (fun candidate =>
                matterCoordinateEquiv (configuration.matter candidate))
              point direction) +
          holonomicMatterConnectionAction configuration point direction := by
    unfold holonomicMatterCovariantDerivative holonomicMatterConnectionAction
    abel
  rw [covariantDerivativeEq, fullCanonicalDiracAdjoint_add,
    fullCanonicalDiracAdjoint_connectionAction,
    ← valuePairing, ← derivativePairing]
  rfl

private theorem fullCanonicalDiracAdjoint_knownVector
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeOne : configuration.coframe point = 1)
    (valuePairing :
      configuration.conjugateMatter point =
        fullCanonicalDiracAdjoint (configuration.matter point))
    (derivativePairing : ∀ direction : Fin 3,
      holonomicConjugateMatterDerivativeDual configuration point
          direction.succ =
        fullCanonicalDiracAdjoint
          (matterCoordinateEquiv.symm
            (fieldDirectionalDerivative
              (fun candidate =>
                matterCoordinateEquiv (configuration.matter candidate))
              point direction.succ))) :
    fullCanonicalDiracAdjoint
        (holonomicDiracDualCurrentCoframeMatterKnownVector
          configuration point) =
      -(∑ direction : Fin 3,
          (holonomicConjugateMatterDerivativeDual configuration point
              direction.succ -
            (configuration.conjugateMatter point).comp
              (holonomicIdentityCoframeMatterConnectionOperator
                configuration point direction.succ)).comp
            (identityCoframeMatterPrincipal direction.succ)) +
        (configuration.conjugateMatter point).comp
          (diracDualRightChiralYukawaHermitianAdjoint
            (scalarCoordinateEquiv.symm (configuration.scalar point))) := by
  have spatialPrincipalEq :
      Complex.I •
          (∑ direction : Fin 3,
            diracMatrixMatterAction (diracGamma direction.succ)
              (holonomicMatterCovariantDerivative configuration point
                direction.succ)) =
        ∑ direction : Fin 3,
          identityCoframeMatterPrincipal direction.succ
            (holonomicMatterCovariantDerivative configuration point
              direction.succ) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro direction _
    rfl
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [coframeOne]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  rw [spatialPrincipalEq, fullCanonicalDiracAdjoint_add,
    fullCanonicalDiracAdjoint_sum]
  simp_rw [fullCanonicalDiracAdjoint_identityPrincipal]
  simp_rw [fullCanonicalDiracAdjoint_covariantDerivative
    configuration point _ valuePairing (derivativePairing _)]
  rw [fullCanonicalDiracAdjoint_rightChiralYukawa, ← valuePairing]
  rw [Finset.sum_neg_distrib]

private theorem fullCanonicalDiracAdjoint_rawIdentityResponse
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (valuePairing :
      configuration.conjugateMatter point =
        fullCanonicalDiracAdjoint (configuration.matter point)) :
    fullCanonicalDiracAdjoint
        (-identityCoframeMatterTimePrincipal
            (holonomicDiracDualCurrentCoframeMatterKnownVector
              configuration point) -
          holonomicMatterConnectionAction configuration point
            canonicalLorentzianTimeDirection) =
      (fullCanonicalDiracAdjoint
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            configuration point)).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) +
        (configuration.conjugateMatter point).comp
          (holonomicIdentityCoframeMatterConnectionOperator
            configuration point canonicalLorentzianTimeDirection) := by
  rw [fullCanonicalDiracAdjoint_sub,
    fullCanonicalDiracAdjoint_neg]
  change
    -(fullCanonicalDiracAdjoint
        (identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            configuration point))) -
      fullCanonicalDiracAdjoint
        (holonomicMatterConnectionAction configuration point
          canonicalLorentzianTimeDirection) = _
  rw [fullCanonicalDiracAdjoint_identityPrincipal,
    fullCanonicalDiracAdjoint_connectionAction, ← valuePairing]
  abel

/-- Exact sum-of-residuals formula.  After value/derivative pairing, the
response mismatch is precisely the installed-minus-Hermitian operator defect:
the spin-connection ordering commutator plus the forward-Yukawa versus
`Y† ∘ P_L` orientation defect. -/
theorem fullDiracIdentityResponseResidual_eq_orientationDefect
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeOne : configuration.coframe point = 1)
    (valuePairing :
      configuration.conjugateMatter point =
        fullCanonicalDiracAdjoint (configuration.matter point))
    (derivativePairing : ∀ direction : Fin 3,
      holonomicConjugateMatterDerivativeDual configuration point
          direction.succ =
        fullCanonicalDiracAdjoint
          (matterCoordinateEquiv.symm
            (fieldDirectionalDerivative
              (fun candidate =>
                matterCoordinateEquiv (configuration.matter candidate))
              point direction.succ))) :
    fullDiracIdentityResponseResidual configuration point =
      ((configuration.conjugateMatter point).comp
        (fullDiracInstalledOrientationDefect configuration point)).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
  unfold fullDiracIdentityResponseResidual
  rw [fullCanonicalDiracAdjoint_rawIdentityResponse
    configuration point valuePairing]
  rw [fullCanonicalDiracAdjoint_knownVector
    configuration point coframeOne valuePairing derivativePairing]
  unfold holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    fullDiracInstalledOrientationDefect
  apply LinearMap.ext
  intro candidate
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    map_add, map_sub, map_sum]
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  have temporalConnectionInvolutive :
      (configuration.conjugateMatter point)
          ((holonomicIdentityCoframeMatterConnectionOperator
            configuration point canonicalLorentzianTimeDirection)
            candidate) =
        (configuration.conjugateMatter point)
          ((holonomicIdentityCoframeMatterConnectionOperator
            configuration point canonicalLorentzianTimeDirection)
            ((identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection)
              ((identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection) candidate))) := by
    rw [identityCoframeMatterPrincipal_time_involutive]
  rw [temporalConnectionInvolutive]
  rw [show canonicalLorentzianTimeDirection =
      (0 : LorentzianIndex) by rfl]
  rw [show ((0 : Fin 3).succ : LorentzianIndex) = 1 by rfl,
    show ((1 : Fin 3).succ : LorentzianIndex) = 2 by rfl,
    show ((2 : Fin 3).succ : LorentzianIndex) = 3 by rfl]
  ring

/-! ## Fixed source specialization -/

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev FixedRestart (point : BasePoint) : StageNineHolonomicConfiguration :=
  profileOperatorRestartAt point

private theorem carry_valuePairing (point : BasePoint) :
    Carry.conjugateMatter point =
      fullCanonicalDiracAdjoint (Carry.matter point) := by
  rw [← canonicalCauchySlicePoint_projections point]
  exact carry_fullDiracAdjointPaired
    (canonicalTimeProjection point) (canonicalSpatialProjection point)

private theorem restart_valuePairing
    (point : BasePoint) (localPoint : BasePoint) :
    (FixedRestart point).conjugateMatter localPoint =
      fullCanonicalDiracAdjoint ((FixedRestart point).matter localPoint) := by
  unfold FixedRestart profileOperatorRestartAt
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  change
    Carry.conjugateMatter
        (canonicalSpacetimeContactTranslation point localPoint) =
      fullCanonicalDiracAdjoint
        (Carry.matter
          (canonicalSpacetimeContactTranslation point localPoint))
  exact carry_valuePairing _

private theorem restart_coordinatePairing
    (point localPoint : BasePoint) :
    holonomicConjugateMatterCoordinates (FixedRestart point) localPoint =
      fullCanonicalDiracAdjointCoordinate
        (matterCoordinateEquiv ((FixedRestart point).matter localPoint)) := by
  unfold holonomicConjugateMatterCoordinates
    fullCanonicalDiracAdjointCoordinate
  rw [restart_valuePairing, matterCoordinateEquiv.symm_apply_apply]

private theorem restart_matterCoordinates_contDiff (point : BasePoint) :
    ContDiff ℝ ∞
      (fun localPoint =>
        matterCoordinateEquiv ((FixedRestart point).matter localPoint)) := by
  unfold FixedRestart profileOperatorRestartAt
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  change ContDiff ℝ ∞
    ((fun candidate => matterCoordinateEquiv (Carry.matter candidate)) ∘
      canonicalSpacetimeContactTranslation point)
  exact actionSelectedCarry_matterCoordinates_contDiff.comp (by
    unfold canonicalSpacetimeContactTranslation
    fun_prop)

private theorem restart_derivativePairing
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual (FixedRestart point) 0 direction =
      fullCanonicalDiracAdjoint
        (matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun localPoint =>
              matterCoordinateEquiv ((FixedRestart point).matter localPoint))
            0 direction)) := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  have functionEq :
      holonomicConjugateMatterCoordinates (FixedRestart point) =
        fun localPoint =>
          fullCanonicalDiracAdjointCoordinate
            (matterCoordinateEquiv ((FixedRestart point).matter localPoint)) := by
    funext localPoint
    exact restart_coordinatePairing point localPoint
  rw [functionEq]
  unfold fieldDirectionalDerivative
  have matterDifferentiable : DifferentiableAt ℝ
      (fun localPoint =>
        matterCoordinateEquiv ((FixedRestart point).matter localPoint)) 0 :=
    (restart_matterCoordinates_contDiff point).differentiable
      (by simp) |>.differentiableAt
  have composed :=
    fullCanonicalDiracAdjointCoordinateRealCLM.hasFDerivAt.comp 0
      matterDifferentiable.hasFDerivAt
  have coordinateDerivative :
      (fderiv ℝ
        (fun localPoint =>
          fullCanonicalDiracAdjointCoordinate
            (matterCoordinateEquiv ((FixedRestart point).matter localPoint))) 0)
          (coordinateDirection direction) =
        fullCanonicalDiracAdjointCoordinate
          ((fderiv ℝ
            (fun localPoint =>
              matterCoordinateEquiv ((FixedRestart point).matter localPoint)) 0)
            (coordinateDirection direction)) := by
    have compositionEq :
        (fun localPoint =>
          fullCanonicalDiracAdjointCoordinate
            (matterCoordinateEquiv ((FixedRestart point).matter localPoint))) =
          fullCanonicalDiracAdjointCoordinateRealCLM ∘
            (fun localPoint =>
              matterCoordinateEquiv ((FixedRestart point).matter localPoint)) := by
      funext localPoint
      rfl
    rw [compositionEq]
    simpa [ContinuousLinearMap.comp_apply,
      fullCanonicalDiracAdjointCoordinateRealCLM_apply] using
      congrArg (fun derivative => derivative (coordinateDirection direction))
        composed.fderiv
  rw [coordinateDerivative,
    matterDualOfCoordinates_fullCanonicalCoordinate]

theorem fixedRestartIdentityResponseResidual_eq_orientationDefect
    (point : BasePoint) :
    fullDiracIdentityResponseResidual (FixedRestart point) 0 =
      (((FixedRestart point).conjugateMatter 0).comp
        (fullDiracInstalledOrientationDefect (FixedRestart point) 0)).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
  apply fullDiracIdentityResponseResidual_eq_orientationDefect
  · exact coframe_eq_one_of_identity_firstJet _ _
      (restart_coframeFirstJet_identity point)
  · exact restart_valuePairing point 0
  · intro direction
    exact restart_derivativePairing point direction.succ

private theorem identityCoframeProfileOperatorResidual_eq_generic
    (point : BasePoint) :
    identityCoframeProfileOperatorResidual point =
      fullDiracIdentityResponseResidual (profileOperatorRestartAt point) 0 := by
  rfl

/-- The existing profile operator residual is the same fixed-Restart
orientation defect, exposed at its established public mouth. -/
theorem identityCoframeProfileOperatorResidual_eq_orientationDefect
    (point : BasePoint) :
    identityCoframeProfileOperatorResidual point =
      (((FixedRestart point).conjugateMatter 0).comp
        (fullDiracInstalledOrientationDefect (FixedRestart point) 0)).comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
  rw [identityCoframeProfileOperatorResidual_eq_generic]
  exact fixedRestartIdentityResponseResidual_eq_orientationDefect point

/-- Exact finite-coordinate consumer for the source-profile mismatch. -/
theorem profileVelocityFormalAdjointResidual_eq_orientationDefectCoordinates
    (point : BasePoint) :
    profileVelocityFormalAdjointResidual point =
      matterDualCoordinates
        ((((FixedRestart point).conjugateMatter 0).comp
          (fullDiracInstalledOrientationDefect (FixedRestart point) 0)).comp
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection)) := by
  rw [profileVelocityFormalAdjointResidual_eq_operatorCoordinates,
    identityCoframeProfileOperatorResidual_eq_orientationDefect]

end

end StageNineFullDiracAdjointLocalOperator
end SaturationMonoid.PhysicsCore
