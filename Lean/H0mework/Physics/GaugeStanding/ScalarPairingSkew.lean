import H0mework.Physics.Exterior.ExteriorMotherLieRepresentation
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Stage-9 P286 linked-active scalar pairing skew law

This module proves directly that the actual degree-four exterior mother Lie
action is skew for the real scalar coordinate pairing.  The proof starts from
the slot-derived exterior action and the skew-adjoint mother matrix, and
computes exterior-basis coefficients through the canonical determinant
pairing.  It does not consume finite-group invariance, a `LieModule` or
isometry receipt, or a supplied pairing-skew certificate.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarPairingSkew

open Matrix
open StageNineDynamicBreakingVacuum
open StageNineExteriorMotherLieRepresentation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

local instance su7MotherIndexLinearOrder : LinearOrder SU7MotherIndex :=
  SU7ExteriorMatterRestriction.instLinearOrderSU7MotherIndex

/-- The determinant derivative computed by replacing columns agrees with the
same derivative computed by replacing rows. -/
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

/-- Conjugating the determinant derivative conjugate-transposes both the
base matrix and its variation. -/
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

/-- Coordinate matrix of the ordered fundamental basis underlying an
exterior-basis input/output pair. -/
private def exteriorBasisCoordinateMatrix
    (output input : ScalarBasisIndex) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun inputPosition outputPosition =>
    (su7FundamentalBasis.repr
      (exteriorBasisInput 4 input inputPosition))
        (exteriorPositionEquiv output outputPosition).1

/-- One row of coordinates obtained by applying the actual mother action in
an input slot. -/
private def exteriorBasisActionCoordinateRow
    (matrix : SU7MotherLieMatrix)
    (output input : ScalarBasisIndex)
    (inputPosition : Fin 4) : Fin 4 → ℂ :=
  fun outputPosition =>
    (su7FundamentalBasis.repr
      (fundamentalMotherLieAction matrix
        (exteriorBasisInput 4 input inputPosition)))
      (exteriorPositionEquiv output outputPosition).1

/-- Coordinate matrix obtained by collecting the four actual action rows. -/
private def exteriorBasisActionCoordinateMatrix
    (matrix : SU7MotherLieMatrix)
    (output input : ScalarBasisIndex) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (exteriorBasisActionCoordinateRow matrix output input)

/-- One exterior action coefficient is the sum of determinant row
replacements produced by the four actual slot writes. -/
private theorem exteriorBasisLieAction_coordinate_eq_sum_det_updateRow
    (matrix : SU7MotherLieMatrix)
    (output input : ScalarBasisIndex) :
    (su7ExteriorBasis 4).repr
        (exteriorBasisLieAction 4 matrix input) output =
      ∑ position : Fin 4,
        ((exteriorBasisCoordinateMatrix output input).updateRow position
          (exteriorBasisActionCoordinateRow matrix output input position)).det := by
  unfold exteriorBasisLieAction
  change
    (su7ExteriorBasis 4).repr
        (∑ position : Fin 4,
          (exteriorPower.ιMulti ℂ 4)
            (exteriorBasisLieActionInput 4 matrix input position)) output = _
  rw [map_sum]
  simp_rw [exteriorBasisLieActionTerm_eq_update]
  change
    (∑ position : Fin 4,
      (su7FundamentalBasis.exteriorPower 4).repr
        ((exteriorPower.ιMulti ℂ 4)
          (Function.update (exteriorBasisInput 4 input) position
            (fundamentalMotherLieAction matrix
              (exteriorBasisInput 4 input position)))) output) = _
  simp_rw [exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro position _
  have outputPositionValue (candidate : Fin 4) :
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
  · simp [exteriorBasisCoordinateMatrix,
      exteriorBasisInput, equality, outputPositionValue]

/-- The fundamental basis coordinate of the actual mother action is the
corresponding mother-matrix entry. -/
private theorem fundamentalMotherLieAction_basis_coordinate
    (matrix : SU7MotherLieMatrix) (output input : SU7MotherIndex) :
    (su7FundamentalBasis.repr
        (fundamentalMotherLieAction matrix (su7FundamentalBasis input))) output =
      (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) output input := by
  simp [fundamentalMotherLieAction, su7FundamentalBasis, Matrix.mulVecLin]

/-- Exchanging the exterior output and input transposes the underlying
zero-one coordinate matrix. -/
private theorem exteriorBasisCoordinateMatrix_conjTranspose
    (output input : ScalarBasisIndex) :
    (exteriorBasisCoordinateMatrix output input)ᴴ =
      exteriorBasisCoordinateMatrix input output := by
  ext row column
  by_cases equality :
      (exteriorPositionEquiv output row).1 =
        (exteriorPositionEquiv input column).1
  · simp [exteriorBasisCoordinateMatrix, exteriorBasisInput, equality]
  · simp [exteriorBasisCoordinateMatrix, exteriorBasisInput, equality,
      Ne.symm equality]

/-- Skew-adjointness of the actual mother matrix exchanges the exterior
action-coordinate input and output matrices with a minus sign. -/
private theorem exteriorBasisActionCoordinateMatrix_conjTranspose
    (matrix : SU7MotherLieMatrix)
    (output input : ScalarBasisIndex) :
    (exteriorBasisActionCoordinateMatrix matrix output input)ᴴ =
      -exteriorBasisActionCoordinateMatrix matrix input output := by
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

/-- Matrix-row form of the determinant coefficient formula. -/
private theorem exteriorBasisLieAction_coordinate_eq_sum_det_updateRow_matrix
    (matrix : SU7MotherLieMatrix)
    (output input : ScalarBasisIndex) :
    (su7ExteriorBasis 4).repr
        (exteriorBasisLieAction 4 matrix input) output =
      ∑ position : Fin 4,
        ((exteriorBasisCoordinateMatrix output input).updateRow position
          ((exteriorBasisActionCoordinateMatrix matrix output input)
            position)).det := by
  rw [exteriorBasisLieAction_coordinate_eq_sum_det_updateRow]
  apply Finset.sum_congr rfl
  intro position _
  apply congrArg Matrix.det
  congr 1

/-- The degree-four exterior action matrix is skew-adjoint in the canonical
exterior basis. -/
private theorem exteriorBasisLieAction_coordinate_star
    (matrix : SU7MotherLieMatrix)
    (output input : ScalarBasisIndex) :
    star ((su7ExteriorBasis 4).repr
      (exteriorBasisLieAction 4 matrix input) output) =
      -((su7ExteriorBasis 4).repr
        (exteriorBasisLieAction 4 matrix output) input) := by
  rw [exteriorBasisLieAction_coordinate_eq_sum_det_updateRow_matrix,
    exteriorBasisLieAction_coordinate_eq_sum_det_updateRow_matrix,
    star_sum_det_updateRow,
    exteriorBasisCoordinateMatrix_conjTranspose]
  have conjugateEntry (row column : Fin 4) :
      (exteriorBasisActionCoordinateMatrix matrix output input)ᴴ row column =
        -(exteriorBasisActionCoordinateMatrix matrix input output row column) :=
    congrArg
      (fun candidate : Matrix (Fin 4) (Fin 4) ℂ => candidate row column)
      (exteriorBasisActionCoordinateMatrix_conjTranspose
        matrix output input)
  calc
    _ = ∑ position : Fin 4,
        ((exteriorBasisCoordinateMatrix input output).updateRow position
          (fun column =>
            -(exteriorBasisActionCoordinateMatrix matrix input output
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
              -(exteriorBasisActionCoordinateMatrix matrix input output
                position column)) =
            (-1 : ℂ) •
              exteriorBasisActionCoordinateMatrix matrix input output
                position := by
        funext column
        simp
      rw [negRow, Matrix.det_updateRow_smul]
      simp

/-- A coordinate unit vector is exactly the matching degree-four exterior
basis vector under the declared scalar chart. -/
private theorem scalarCoordinateEquiv_symm_single
    (index : ScalarBasisIndex) :
    scalarCoordinateEquiv.symm (EuclideanSpace.single index 1) =
      su7ExteriorBasis 4 index := by
  apply (su7ExteriorBasis 4).repr.injective
  ext candidate
  simp [scalarCoordinateEquiv]

/-- On scalar coordinate units, the declared action exposes the actual
degree-four exterior action coefficient. -/
private theorem scalarMotherLieAction_single_apply
    (matrix : SU7MotherLieMatrix)
    (input output : ScalarBasisIndex) :
    scalarMotherLieAction matrix (EuclideanSpace.single input 1) output =
      (su7ExteriorBasis 4).repr
        (exteriorBasisLieAction 4 matrix input) output := by
  unfold scalarMotherLieAction
  rw [scalarCoordinateEquiv_symm_single,
    exteriorMotherLieAction_basis_slot]
  simp [scalarCoordinateEquiv]

/-- The scalar action is packaged as its actual complex-linear coordinate
endomorphism; this adds no new receipt. -/
private def scalarMotherLieLinearAction
    (matrix : SU7MotherLieMatrix) :
    Module.End ℂ ScalarCoordinateCarrier :=
  scalarCoordinateEquiv.toLinearMap.comp
    ((exteriorMotherLieAction 4 matrix).comp
      scalarCoordinateEquiv.symm.toLinearMap)

@[simp]
private theorem scalarMotherLieLinearAction_apply
    (matrix : SU7MotherLieMatrix)
    (coordinates : ScalarCoordinateCarrier) :
    scalarMotherLieLinearAction matrix coordinates =
      scalarMotherLieAction matrix coordinates := by
  rfl

/-- The coordinate-unit matrix coefficient is skew for the canonical
complex Euclidean inner product. -/
private theorem scalarMotherLieAction_single_inner_skew
    (matrix : SU7MotherLieMatrix)
    (input output : ScalarBasisIndex) :
    inner ℂ
        (scalarMotherLieAction matrix (EuclideanSpace.single input 1))
        (EuclideanSpace.single output 1) +
      inner ℂ (EuclideanSpace.single input 1)
        (scalarMotherLieAction matrix (EuclideanSpace.single output 1)) = 0 := by
  rw [EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_left]
  simp only [one_mul, map_one]
  rw [scalarMotherLieAction_single_apply,
    scalarMotherLieAction_single_apply]
  change
    star ((su7ExteriorBasis 4).repr
      (exteriorBasisLieAction 4 matrix input) output) +
      (su7ExteriorBasis 4).repr
        (exteriorBasisLieAction 4 matrix output) input = 0
  rw [exteriorBasisLieAction_coordinate_star]
  simp

/-- Complex-linear extension of the basis coefficient law to arbitrary
degree-four scalar coordinates. -/
private theorem scalarMotherLieLinearAction_inner_skew
    (matrix : SU7MotherLieMatrix)
    (first second : ScalarCoordinateCarrier) :
    inner ℂ (scalarMotherLieLinearAction matrix first) second +
      inner ℂ first (scalarMotherLieLinearAction matrix second) = 0 := by
  classical
  have firstExpansion :
      (∑ index : ScalarBasisIndex,
          first index • EuclideanSpace.single index 1) = first := by
    ext index
    simp [Pi.single_apply]
  have secondExpansion :
      (∑ index : ScalarBasisIndex,
          second index • EuclideanSpace.single index 1) = second := by
    ext index
    simp [Pi.single_apply]
  rw [← firstExpansion, ← secondExpansion]
  simp only [map_sum, map_smul, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro output _
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro input _
  rw [scalarMotherLieLinearAction_apply,
    scalarMotherLieLinearAction_apply]
  have basisSkew :=
    scalarMotherLieAction_single_inner_skew matrix input output
  rw [← mul_add, basisSkew, mul_zero]

/-- The actual degree-four scalar mother Lie action is skew for the real
coordinate pairing.  This is a representation readout of the slot-generated
action and the mother-matrix law `Aᴴ = -A`; no finite-action invariance or
stored skew certificate is consumed. -/
theorem scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (matrix : SU7MotherLieMatrix)
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe (scalarMotherLieAction matrix first) second +
      scalarCoordinatePairingRe first
        (scalarMotherLieAction matrix second) = 0 := by
  have complexSkew :=
    scalarMotherLieLinearAction_inner_skew matrix first second
  simp only [scalarMotherLieLinearAction_apply] at complexSkew
  have realSkew := congrArg Complex.re complexSkew
  simpa [scalarCoordinatePairingRe, PiLp.inner_apply,
    RCLike.inner_apply', mul_comm] using realSkew

end

end SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarPairingSkew
