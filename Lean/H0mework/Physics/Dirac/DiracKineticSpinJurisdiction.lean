import H0mework.Physics.Dirac.CoframeSpinRepresentation

/-!
# Dirac kinetic Spin jurisdiction

The Stage-7 matter carrier already carries the chiral finite-Spin action

`S(g) = diag(g, (g†)⁻¹)`.

Consequently the Lorentz action compatible with its Clifford multiplication
is not an independently chosen convention.  It is the existing Lorentz cover
precomposed with the canonical Weyl-dual involution

`kappa(g) = (g⁻¹)†`.

This file derives that involution from the actual `SL(2,C)` matrices, proves
the finite Clifford slash intertwiner, and exposes the positive mouth needed
by the inverse-coframe kinetic operator.  It does not change the active root
action, add a field/coupling/source slot, or accept a covariance certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracKineticSpinJurisdiction

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeSpinRepresentation
open StageNineGlobalBundle
open StageNineLorentzCoverAndSpinDescent
open StageNinePhysicalBivectorSpinRepresentation
open StageNineSpinMatterBundle
open SU7ExteriorBreakingYukawa

open scoped MatrixGroups ComplexConjugate

noncomputable section

set_option autoImplicit false

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

@[simp] private theorem finSumFinEquiv_symm_zero :
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4).symm (0 : Fin 4) =
      Sum.inl (0 : Fin 2) := by
  rw [show (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) by rfl]
  exact finSumFinEquiv_symm_apply_castAdd 0

@[simp] private theorem finSumFinEquiv_symm_one :
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4).symm (1 : Fin 4) =
      Sum.inl (1 : Fin 2) := by
  rw [show (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) by rfl]
  exact finSumFinEquiv_symm_apply_castAdd 1

@[simp] private theorem finSumFinEquiv_symm_two :
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4).symm (2 : Fin 4) =
      Sum.inr (0 : Fin 2) := by
  rw [show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) by rfl]
  exact finSumFinEquiv_symm_apply_natAdd 0

@[simp] private theorem finSumFinEquiv_symm_three :
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4).symm (3 : Fin 4) =
      Sum.inr (1 : Fin 2) := by
  rw [show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) by rfl]
  exact finSumFinEquiv_symm_apply_natAdd 1

@[simp] private theorem finSumFinEquiv_symm_castAdd_two (index : Fin 2) :
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4).symm
        (Fin.castAdd 2 index) = Sum.inl index :=
  finSumFinEquiv_symm_apply_castAdd index

@[simp] private theorem finSumFinEquiv_symm_addNat_two (index : Fin 2) :
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4).symm
        (Fin.addNat index 2) = Sum.inr index := by
  have indexEquality :
      Fin.addNat index 2 = Fin.natAdd 2 index := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
  rw [indexEquality]
  exact finSumFinEquiv_symm_apply_natAdd index

/-! ## Canonical Weyl-dual Spin involution -/

/-- The Weyl-dual Spin element.  Its matrix is the already generated
right-handed Weyl block `(g⁻¹)†`; determinant one is derived rather than
stored. -/
def spinWeylDualElement (groupElement : SpinPlus13) : SpinPlus13 := by
  let inverseMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
    (groupElement⁻¹ : SpinPlus13)
  refine ⟨Matrix.conjTranspose inverseMatrix, ?_⟩
  calc
    Matrix.det (Matrix.conjTranspose inverseMatrix) =
        star (Matrix.det inverseMatrix) := Matrix.det_conjTranspose inverseMatrix
    _ = star 1 := congrArg star (groupElement⁻¹).property
    _ = 1 := by simp

@[simp] theorem spinWeylDualElement_coe (groupElement : SpinPlus13) :
    ((spinWeylDualElement groupElement : SpinPlus13) :
        Matrix (Fin 2) (Fin 2) ℂ) = rightWeylMatrix groupElement :=
  rfl

theorem spinWeylDualElement_mul (first second : SpinPlus13) :
    spinWeylDualElement (first * second) =
      spinWeylDualElement first * spinWeylDualElement second := by
  apply Subtype.ext
  exact rightWeylMatrix_mul first second

@[simp] theorem spinWeylDualElement_involutive
    (groupElement : SpinPlus13) :
    spinWeylDualElement (spinWeylDualElement groupElement) = groupElement := by
  apply Subtype.ext
  rw [spinWeylDualElement_coe]
  unfold rightWeylMatrix
  simp only [Matrix.SpecialLinearGroup.coe_inv,
    spinWeylDualElement_coe, rightWeylMatrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply]

/-- Canonical, parameter-free involutive automorphism exchanging the two Weyl
blocks. -/
def spinWeylDual : SpinPlus13 ≃* SpinPlus13 where
  toFun := spinWeylDualElement
  invFun := spinWeylDualElement
  left_inv := spinWeylDualElement_involutive
  right_inv := spinWeylDualElement_involutive
  map_mul' := spinWeylDualElement_mul

@[simp] theorem spinWeylDual_apply_apply (groupElement : SpinPlus13) :
    spinWeylDual (spinWeylDual groupElement) = groupElement :=
  spinWeylDualElement_involutive groupElement

@[simp] theorem rightWeylMatrix_spinWeylDual (groupElement : SpinPlus13) :
    rightWeylMatrix (spinWeylDual groupElement) = groupElement := by
  exact congrArg Subtype.val (spinWeylDual_apply_apply groupElement)

/-! ## Finite Clifford slash -/

/-- Clifford multiplication by an actual Lorentz four-vector. -/
def diracSlash (vector : BasePoint) : DiracMatrix :=
  ∑ internal : LorentzianIndex,
    (vector internal : ℂ) • diracGamma internal

/-- Weyl-block normal form of the fixed gamma matrices. -/
theorem diracSlash_weylBlock (vector : BasePoint) :
    diracSlash vector =
      Matrix.reindexRingEquiv ℂ finSumFinEquiv
        (Matrix.fromBlocks 0 (pauliEncode vector)
          (-(Matrix.adjugate (pauliEncode vector))) 0) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [diracSlash, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, pauliEncode,
      Matrix.reindexRingEquiv, Matrix.reindexAddEquiv, Matrix.reindex,
      Matrix.submatrix, Matrix.fromBlocks, Matrix.adjugate_fin_two,
      Fin.sum_univ_four] <;> ring

/-- The lower Weyl block follows functorially from the actual Hermitian
four-vector action; no separate Clifford covariance premise is used. -/
theorem pauliEncode_adjugate_spinHermitianAction
    (groupElement : SpinPlus13) (vector : BasePoint) :
    Matrix.adjugate
        (pauliEncode (spinLorentzCover groupElement vector)) =
      rightWeylMatrix groupElement *
        Matrix.adjugate (pauliEncode vector) *
          ((groupElement⁻¹ : SpinPlus13) :
            Matrix (Fin 2) (Fin 2) ℂ) := by
  change Matrix.adjugate
      (pauliEncode (spinHermitianAction groupElement vector)) = _
  rw [spinHermitianAction_encode, Matrix.adjugate_mul_distrib,
    Matrix.adjugate_mul_distrib]
  have hstar :
      Matrix.adjugate
          (star (groupElement : Matrix (Fin 2) (Fin 2) ℂ)) =
        star (Matrix.adjugate
          (groupElement : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (Matrix.adjugate_conjTranspose
      (groupElement : Matrix (Fin 2) (Fin 2) ℂ)).symm
  have hinverse :
      Matrix.adjugate
          (groupElement : Matrix (Fin 2) (Fin 2) ℂ) =
        ((groupElement⁻¹ : SpinPlus13) :
          Matrix (Fin 2) (Fin 2) ℂ) :=
    (Matrix.SpecialLinearGroup.coe_inv groupElement).symm
  rw [hstar, hinverse]
  simp [rightWeylMatrix, Matrix.mul_assoc]

/-- Finite Clifford multiplication intertwines the actual Stage-7 Dirac
matrix with its generated Lorentz cover. -/
theorem spinDiracMatrix_diracSlash_covariant
    (groupElement : SpinPlus13) (vector : BasePoint) :
    spinDiracMatrix groupElement * diracSlash vector *
        spinDiracMatrix groupElement⁻¹ =
      diracSlash (spinLorentzCover groupElement vector) := by
  rw [diracSlash_weylBlock, diracSlash_weylBlock]
  change
    Matrix.reindexRingEquiv ℂ finSumFinEquiv
          (weylDiracBlockMatrix groupElement) *
        Matrix.reindexRingEquiv ℂ finSumFinEquiv
          (Matrix.fromBlocks 0 (pauliEncode vector)
            (-(Matrix.adjugate (pauliEncode vector))) 0) *
        Matrix.reindexRingEquiv ℂ finSumFinEquiv
          (weylDiracBlockMatrix groupElement⁻¹) =
      Matrix.reindexRingEquiv ℂ finSumFinEquiv
        (Matrix.fromBlocks 0
          (pauliEncode (spinLorentzCover groupElement vector))
          (-(Matrix.adjugate
            (pauliEncode (spinLorentzCover groupElement vector)))) 0)
  rw [← map_mul, ← map_mul]
  apply congrArg (Matrix.reindexRingEquiv ℂ finSumFinEquiv)
  have hrightInverse :
      rightWeylMatrix groupElement⁻¹ =
        star (groupElement : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp [rightWeylMatrix]
  have hcover :
      spinLorentzCover groupElement vector =
        spinHermitianAction groupElement vector := rfl
  ext row column
  rcases row with row | row <;> rcases column with column | column
  · simp [weylDiracBlockMatrix, Matrix.fromBlocks_multiply]
  · simp only [weylDiracBlockMatrix, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_apply₁₂, add_zero,
      Matrix.zero_mul, Matrix.mul_zero, zero_add]
    simpa [Matrix.mul_assoc, hrightInverse, hcover] using congrArg
      (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => matrix row column)
      (spinHermitianAction_encode groupElement vector).symm
  · simp only [weylDiracBlockMatrix, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_apply₂₁, add_zero,
      Matrix.zero_mul, Matrix.mul_zero, zero_add,
      Matrix.neg_mul, Matrix.mul_neg]
    simpa [Matrix.mul_assoc, rightWeylMatrix, hcover,
      Matrix.SpecialLinearGroup.coe_inv] using congrArg
      (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => matrix row column)
      (congrArg Neg.neg
        (pauliEncode_adjugate_spinHermitianAction
          groupElement vector)).symm
  · simp [weylDiracBlockMatrix, Matrix.fromBlocks_multiply]

/-- Matrix inverse of the fixed finite Dirac representation is generated by
the inverse Spin element. -/
theorem spinDiracMatrix_nonsingInv (groupElement : SpinPlus13) :
    (spinDiracMatrix groupElement)⁻¹ =
      spinDiracMatrix groupElement⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← spinDiracMatrix_mul]
  simp

/-- Basis-gamma specialization of finite Clifford covariance. -/
theorem spinDiracMatrix_diracGamma_covariant
    (groupElement : SpinPlus13) (internal : LorentzianIndex) :
    spinDiracMatrix groupElement * diracGamma internal *
        spinDiracMatrix groupElement⁻¹ =
      ∑ output : LorentzianIndex,
        (spinLorentzMatrix groupElement output internal : ℂ) •
          diracGamma output := by
  have covariance :=
    spinDiracMatrix_diracSlash_covariant groupElement
      (EuclideanSpace.single internal 1)
  simpa [diracSlash, EuclideanSpace.single,
    spinLorentzMatrix_apply] using covariance

/-! ## Metric-raise jurisdiction of the existing inverse gamma -/

/-- The inverse metric has the forced coframe factorization on the
nondegenerate branch. -/
theorem lorentzianMetricOfCoframe_inv_factorization
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    (lorentzianMetricOfCoframe coframe)⁻¹ =
      coframe⁻¹ * minkowskiInternalMetric * coframe⁻¹.transpose := by
  apply Matrix.inv_eq_right_inv
  have coframeUnit : IsUnit (Matrix.det coframe) :=
    isUnit_iff_ne_zero.mpr nondegenerate
  have rightInverse := Matrix.mul_nonsing_inv coframe coframeUnit
  have leftInverse := Matrix.nonsing_inv_mul coframe coframeUnit
  have metricSquare :
      minkowskiInternalMetric * minkowskiInternalMetric =
        (1 : LorentzianMetric) := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [minkowskiInternalMetric]
  change
    (coframe.transpose * minkowskiInternalMetric * coframe) *
        (coframe⁻¹ * minkowskiInternalMetric * coframe⁻¹.transpose) = 1
  calc
    (coframe.transpose * minkowskiInternalMetric * coframe) *
          (coframe⁻¹ * minkowskiInternalMetric * coframe⁻¹.transpose) =
        coframe.transpose * minkowskiInternalMetric *
          (coframe * coframe⁻¹) * minkowskiInternalMetric *
            coframe⁻¹.transpose := by noncomm_ring
    _ = coframe.transpose * minkowskiInternalMetric *
          minkowskiInternalMetric * coframe⁻¹.transpose := by
      rw [rightInverse]
      simp
    _ = coframe.transpose *
          (minkowskiInternalMetric * minkowskiInternalMetric) *
            coframe⁻¹.transpose := by
      noncomm_ring
    _ = coframe.transpose * coframe⁻¹.transpose := by
      rw [metricSquare]
      simp
    _ = (coframe⁻¹ * coframe).transpose := by
      rw [Matrix.transpose_mul]
    _ = 1 := by
      rw [leftInverse]
      simp

/-- Raising the spacetime index of the covariant coframe gamma contracts to
the inverse coframe with the internal metric. -/
theorem lorentzianMetricInv_mul_coframeTranspose
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    (lorentzianMetricOfCoframe coframe)⁻¹ * coframe.transpose =
      coframe⁻¹ * minkowskiInternalMetric := by
  rw [lorentzianMetricOfCoframe_inv_factorization coframe nondegenerate]
  have coframeUnit : IsUnit (Matrix.det coframe) :=
    isUnit_iff_ne_zero.mpr nondegenerate
  have rightInverse := Matrix.mul_nonsing_inv coframe coframeUnit
  calc
    (coframe⁻¹ * minkowskiInternalMetric * coframe⁻¹.transpose) *
          coframe.transpose =
        coframe⁻¹ * minkowskiInternalMetric *
          (coframe⁻¹.transpose * coframe.transpose) := by
      noncomm_ring
    _ = coframe⁻¹ * minkowskiInternalMetric *
          (coframe * coframe⁻¹).transpose := by
      rw [Matrix.transpose_mul]
    _ = coframe⁻¹ * minkowskiInternalMetric := by
      rw [rightInverse]
      simp

theorem lorentzianMetricInv_coframe_contraction_complex
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coordinate internal : LorentzianIndex) :
    ∑ sourceCoordinate : LorentzianIndex,
        (((lorentzianMetricOfCoframe coframe)⁻¹
            coordinate sourceCoordinate : ℝ) : ℂ) *
          (coframe internal sourceCoordinate : ℂ) =
      (((coframe⁻¹ * minkowskiInternalMetric)
          coordinate internal : ℝ) : ℂ) := by
  have entryEquality := congrArg
    (fun matrix : LorentzianMetric => matrix coordinate internal)
    (lorentzianMetricInv_mul_coframeTranspose coframe nondegenerate)
  have realEquality :
      ∑ sourceCoordinate : LorentzianIndex,
          (lorentzianMetricOfCoframe coframe)⁻¹
              coordinate sourceCoordinate *
            coframe internal sourceCoordinate =
        (coframe⁻¹ * minkowskiInternalMetric)
          coordinate internal := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using entryEquality
  exact_mod_cast realEquality

/-- The historical upper-gamma inverse-coframe mouth is exactly the metric
raise of the already proved covariantly constant coframe gamma.  This rules
out replacing it by a lowered-gamma lookalike. -/
theorem inverseCoframeDiracGamma_eq_metricRaise_coframeDiracGamma
    (geometry : PointwiseLorentzianCoframeJet)
    (nondegenerate : Matrix.det geometry.coframe ≠ 0)
    (coordinate : LorentzianIndex) :
    inverseCoframeDiracGamma geometry coordinate =
      ∑ sourceCoordinate : LorentzianIndex,
        (((geometry.metric)⁻¹ coordinate sourceCoordinate : ℝ) : ℂ) •
          coframeDiracGamma geometry sourceCoordinate := by
  change inverseCoframeDiracGamma geometry coordinate =
    ∑ sourceCoordinate : LorentzianIndex,
      ((((lorentzianMetricOfCoframe geometry.coframe)⁻¹
          coordinate sourceCoordinate : ℝ) : ℂ)) •
        coframeDiracGamma geometry sourceCoordinate
  unfold inverseCoframeDiracGamma
  symm
  calc
    (∑ sourceCoordinate : LorentzianIndex,
        ((((lorentzianMetricOfCoframe geometry.coframe)⁻¹
            coordinate sourceCoordinate : ℝ) : ℂ)) •
          coframeDiracGamma geometry sourceCoordinate) =
      ∑ internal : LorentzianIndex,
        (∑ sourceCoordinate : LorentzianIndex,
          ((((lorentzianMetricOfCoframe geometry.coframe)⁻¹
              coordinate sourceCoordinate : ℝ) : ℂ)) *
            (geometry.coframe internal sourceCoordinate : ℂ)) •
          loweredDiracGamma internal := by
      simp only [coframeDiracGamma, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro internal _
      rw [← Finset.sum_smul]
    _ = ∑ internal : LorentzianIndex,
        ((((geometry.coframe⁻¹ * minkowskiInternalMetric)
            coordinate internal : ℝ) : ℂ)) •
          loweredDiracGamma internal := by
      apply Finset.sum_congr rfl
      intro internal _
      rw [lorentzianMetricInv_coframe_contraction_complex
        geometry.coframe nondegenerate coordinate internal]
    _ = ∑ internal : LorentzianIndex,
        (geometry.coframe⁻¹ coordinate internal : ℂ) •
          diracGamma internal := by
      apply Finset.sum_congr rfl
      intro internal _
      fin_cases internal <;>
        simp [minkowskiInternalMetric, Matrix.mul_apply,
          Matrix.diagonal_apply,
          loweredDiracGamma, minkowskiInternalSign]

/-! ## Clifford-compatible coframe transport -/

/-- Euclidean coordinate pairing used only to identify the transpose of the
Lorentz matrix.  It is a representation-theoretic proof device, not the
physical Minkowski metric. -/
def basePointCoordinatePairing (first second : BasePoint) : ℝ :=
  ∑ index : LorentzianIndex, first index * second index

theorem basePointCoordinatePairing_single_right
    (vector : BasePoint) (index : LorentzianIndex) :
    basePointCoordinatePairing vector (EuclideanSpace.single index 1) =
      vector index := by
  simp [basePointCoordinatePairing, EuclideanSpace.single]

theorem basePointCoordinatePairing_single_left
    (index : LorentzianIndex) (vector : BasePoint) :
    basePointCoordinatePairing (EuclideanSpace.single index 1) vector =
      vector index := by
  simp [basePointCoordinatePairing, EuclideanSpace.single]

/-- The Pauli encoding identifies the coordinate pairing with half the
matrix trace. -/
theorem pauliEncode_trace_mul
    (first second : BasePoint) :
    Matrix.trace (pauliEncode first * pauliEncode second) =
      (2 : ℂ) * (basePointCoordinatePairing first second : ℂ) := by
  simp [Matrix.trace, pauliEncode,
    basePointCoordinatePairing, Fin.sum_univ_two, Fin.sum_univ_four]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `kappa` is the coordinate adjoint forced by the same Pauli/Clifford
action. -/
theorem spinWeylDual_coordinatePairing_adjoint
    (groupElement : SpinPlus13) (first second : BasePoint) :
    basePointCoordinatePairing
        (spinLorentzCover (spinWeylDual groupElement) first) second =
      basePointCoordinatePairing first
        (spinLorentzCover groupElement⁻¹ second) := by
  let dualMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
    rightWeylMatrix groupElement
  let inverseMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
    ((groupElement⁻¹ : SpinPlus13) : Matrix (Fin 2) (Fin 2) ℂ)
  have dualEncode :=
    spinHermitianAction_encode (spinWeylDual groupElement) first
  have inverseEncode :=
    spinHermitianAction_encode groupElement⁻¹ second
  have dualStar :
      star ((spinWeylDual groupElement : SpinPlus13) :
          Matrix (Fin 2) (Fin 2) ℂ) =
        ((groupElement⁻¹ : SpinPlus13) :
          Matrix (Fin 2) (Fin 2) ℂ) := by
    change star (rightWeylMatrix groupElement) = _
    simp [rightWeylMatrix]
  have inverseStar :
      star (((groupElement⁻¹ : SpinPlus13) :
          Matrix (Fin 2) (Fin 2) ℂ)) =
        rightWeylMatrix groupElement :=
    rfl
  have traceEquality :
      Matrix.trace
          (pauliEncode
            (spinLorentzCover (spinWeylDual groupElement) first) *
              pauliEncode second) =
        Matrix.trace
          (pauliEncode first *
            pauliEncode (spinLorentzCover groupElement⁻¹ second)) := by
    change Matrix.trace
        (pauliEncode
          (spinHermitianAction (spinWeylDual groupElement) first) *
            pauliEncode second) =
      Matrix.trace
        (pauliEncode first *
          pauliEncode (spinHermitianAction groupElement⁻¹ second))
    rw [dualEncode, inverseEncode, dualStar, inverseStar]
    change Matrix.trace
        ((dualMatrix * pauliEncode first * inverseMatrix) *
          pauliEncode second) =
      Matrix.trace
        (pauliEncode first *
          (inverseMatrix * pauliEncode second * dualMatrix))
    calc
      Matrix.trace
          ((dualMatrix * pauliEncode first * inverseMatrix) *
            pauliEncode second) =
        Matrix.trace
          (dualMatrix *
            (pauliEncode first * inverseMatrix * pauliEncode second)) := by
          congr 1
          noncomm_ring
      _ = Matrix.trace
          ((pauliEncode first * inverseMatrix * pauliEncode second) *
            dualMatrix) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace
          (pauliEncode first *
            (inverseMatrix * pauliEncode second * dualMatrix)) := by
          congr 1
          noncomm_ring
  rw [pauliEncode_trace_mul, pauliEncode_trace_mul] at traceEquality
  have complexEquality :
      (basePointCoordinatePairing
          (spinLorentzCover (spinWeylDual groupElement) first) second : ℂ) =
        (basePointCoordinatePairing first
          (spinLorentzCover groupElement⁻¹ second) : ℂ) := by
    apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
    exact traceEquality
  exact_mod_cast complexEquality

/-- The Weyl-dual Spin involution forces the contragredient Lorentz matrix.
This is the exact seam between the fixed Stage-7 chiral action and the
gravity/coframe representation. -/
theorem spinLorentzMatrix_spinWeylDual
    (groupElement : SpinPlus13) :
    spinLorentzMatrix (spinWeylDual groupElement) =
      (spinLorentzMatrix groupElement⁻¹).transpose := by
  ext row column
  rw [spinLorentzMatrix_apply, Matrix.transpose_apply,
    spinLorentzMatrix_apply]
  calc
    spinLorentzCover (spinWeylDual groupElement)
          (EuclideanSpace.single column 1) row =
        basePointCoordinatePairing
          (spinLorentzCover (spinWeylDual groupElement)
            (EuclideanSpace.single column 1))
          (EuclideanSpace.single row 1) :=
      (basePointCoordinatePairing_single_right _ row).symm
    _ = basePointCoordinatePairing
          (EuclideanSpace.single column 1)
          (spinLorentzCover groupElement⁻¹
            (EuclideanSpace.single row 1)) :=
      spinWeylDual_coordinatePairing_adjoint groupElement
        (EuclideanSpace.single column 1) (EuclideanSpace.single row 1)
    _ = spinLorentzCover groupElement⁻¹
          (EuclideanSpace.single row 1) column :=
      basePointCoordinatePairing_single_left column _

/-- Matrix inverse of the generated Lorentz representation is generated by
the inverse Spin element. -/
theorem spinLorentzMatrix_nonsingInv (groupElement : SpinPlus13) :
    (spinLorentzMatrix groupElement)⁻¹ =
      spinLorentzMatrix groupElement⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← map_mul]
  simp

set_option maxHeartbeats 2000000 in
/-- The generated Lorentz matrix preserves the fixed internal Minkowski
metric.  This is polarized from the already proved quadratic-form theorem;
no Lorentz certificate is supplied with the group element. -/
theorem spinLorentzMatrix_preserves_minkowskiMetric
    (groupElement : SpinPlus13) :
    (spinLorentzMatrix groupElement).transpose *
          minkowskiInternalMetric * spinLorentzMatrix groupElement =
      minkowskiInternalMetric := by
  ext first second
  have firstQuadratic :=
    spinLorentzCover_preserves_minkowski groupElement
      (EuclideanSpace.single first 1)
  have secondQuadratic :=
    spinLorentzCover_preserves_minkowski groupElement
      (EuclideanSpace.single second 1)
  have sumQuadratic :=
    spinLorentzCover_preserves_minkowski groupElement
      (EuclideanSpace.single first 1 + EuclideanSpace.single second 1)
  rw [map_add] at sumQuadratic
  fin_cases first <;> fin_cases second
  all_goals
    simp [Matrix.mul_apply, Matrix.transpose_apply,
      spinLorentzMatrix_apply, minkowskiInternalMetric,
      minkowskiQuadratic, EuclideanSpace.single,
      Fin.sum_univ_four] at firstQuadratic secondQuadratic sumQuadratic ⊢
  all_goals nlinarith

/-- Minkowski-adjoint formula for the inverse generated Lorentz matrix. -/
theorem spinLorentzMatrix_nonsingInv_minkowski
    (groupElement : SpinPlus13) :
    (spinLorentzMatrix groupElement)⁻¹ =
      minkowskiInternalMetric *
        (spinLorentzMatrix groupElement).transpose *
          minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  have metricSquare :
      minkowskiInternalMetric * minkowskiInternalMetric =
        (1 : LorentzianMetric) := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [minkowskiInternalMetric]
  calc
    (minkowskiInternalMetric *
          (spinLorentzMatrix groupElement).transpose *
            minkowskiInternalMetric) *
        spinLorentzMatrix groupElement =
      minkowskiInternalMetric *
        ((spinLorentzMatrix groupElement).transpose *
          minkowskiInternalMetric * spinLorentzMatrix groupElement) := by
        noncomm_ring
    _ = minkowskiInternalMetric * minkowskiInternalMetric := by
      rw [spinLorentzMatrix_preserves_minkowskiMetric]
    _ = 1 := metricSquare

/-- The inverse of the Weyl-dual transformed coframe has the transpose row
transport forced by the Stage-7 Dirac action. -/
theorem spinWeylDualCoframe_inverse
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe) :
    (spinLorentzCoframeRepresentation (spinWeylDual groupElement) coframe)⁻¹ =
      coframe⁻¹ * (spinLorentzMatrix groupElement).transpose := by
  change
    (spinLorentzMatrix (spinWeylDual groupElement) * coframe)⁻¹ = _
  rw [Matrix.mul_inv_rev,
    spinLorentzMatrix_nonsingInv,
    show (spinWeylDual groupElement)⁻¹ =
        spinWeylDual groupElement⁻¹ by simp,
    spinLorentzMatrix_spinWeylDual]
  simp

/-- The coordinate row of the inverse coframe, placed in the already fixed
four-vector carrier. -/
def inverseCoframeRow
    (coframe : LorentzianCoframe) (coordinate : LorentzianIndex) : BasePoint :=
  WithLp.toLp 2 fun internal => coframe⁻¹ coordinate internal

@[simp] theorem inverseCoframeRow_apply
    (coframe : LorentzianCoframe) (coordinate internal : LorentzianIndex) :
    inverseCoframeRow coframe coordinate internal =
      coframe⁻¹ coordinate internal :=
  rfl

/-- Coordinate matrix multiplication agrees with the actual Lorentz linear
equivalence on the generated base carrier. -/
theorem spinLorentzMatrix_mulVec
    (groupElement : SpinPlus13) (vector : BasePoint) :
    Matrix.mulVec (spinLorentzMatrix groupElement)
        (fun internal => vector internal) =
      fun internal => spinLorentzCover groupElement vector internal := by
  have matrixEquality :
      spinLorentzMatrix groupElement =
        LinearMap.toMatrix basePointCoordinateBasis basePointCoordinateBasis
          (spinLorentzCover groupElement).toLinearMap := by
    change
      (LinearMap.toMatrixAlgEquiv basePointCoordinateBasis)
          (spinLorentzCover groupElement).toLinearMap = _
    ext row column
    rw [LinearMap.toMatrixAlgEquiv_apply]
    exact (LinearMap.toMatrix_apply basePointCoordinateBasis
      basePointCoordinateBasis (spinLorentzCover groupElement).toLinearMap
      row column).symm
  have reprEquality (value : BasePoint) :
      basePointCoordinateBasis.repr value = fun internal => value internal := by
    funext internal
    simp [basePointCoordinateBasis, EuclideanSpace.basisFun_repr]
  have coordinateAction :=
    LinearMap.toMatrix_mulVec_repr basePointCoordinateBasis
      basePointCoordinateBasis (spinLorentzCover groupElement).toLinearMap vector
  rw [matrixEquality, ← reprEquality vector,
    ← reprEquality (spinLorentzCover groupElement vector)]
  exact coordinateAction

/-- Every inverse-coframe row follows the same actual Lorentz vector action
when the coframe consumes the Weyl-dual Spin transporter. -/
theorem inverseCoframeRow_spinWeylDual
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (coordinate : LorentzianIndex) :
    inverseCoframeRow
        (spinLorentzCoframeRepresentation (spinWeylDual groupElement) coframe)
        coordinate =
      spinLorentzCover groupElement (inverseCoframeRow coframe coordinate) := by
  apply PiLp.ext
  intro internal
  rw [inverseCoframeRow_apply, spinWeylDualCoframe_inverse,
    Matrix.mul_apply]
  change
    (∑ middle,
      coframe⁻¹ coordinate middle *
        spinLorentzMatrix groupElement internal middle) = _
  have coordinateAction := congrFun
    (spinLorentzMatrix_mulVec groupElement
      (inverseCoframeRow coframe coordinate)) internal
  simpa [Matrix.mulVec, dotProduct, mul_comm] using coordinateAction

theorem inverseCoframeDiracGamma_eq_diracSlash
    (geometry : PointwiseLorentzianCoframeJet)
    (coordinate : LorentzianIndex) :
    inverseCoframeDiracGamma geometry coordinate =
      diracSlash (inverseCoframeRow geometry.coframe coordinate) := by
  rfl

/-- Positive finite-Spin kinetic mouth: the upper inverse-coframe gamma from
the active action intertwines the fixed Stage-7 matter matrix once gravity
uses the uniquely forced Weyl-dual transporter. -/
theorem inverseCoframeDiracGamma_spinWeylDual_intertwine
    (groupElement : SpinPlus13)
    (geometry : PointwiseLorentzianCoframeJet)
    (coordinate : LorentzianIndex) :
    inverseCoframeDiracGamma
          { geometry with
              coframe := spinLorentzCoframeRepresentation
                (spinWeylDual groupElement) geometry.coframe }
          coordinate * spinDiracMatrix groupElement =
      spinDiracMatrix groupElement *
        inverseCoframeDiracGamma geometry coordinate := by
  rw [inverseCoframeDiracGamma_eq_diracSlash,
    inverseCoframeDiracGamma_eq_diracSlash]
  change
    diracSlash
          (inverseCoframeRow
            (spinLorentzCoframeRepresentation
              (spinWeylDual groupElement) geometry.coframe) coordinate) *
        spinDiracMatrix groupElement =
      spinDiracMatrix groupElement *
        diracSlash (inverseCoframeRow geometry.coframe coordinate)
  rw [inverseCoframeRow_spinWeylDual]
  have slashCovariance := spinDiracMatrix_diracSlash_covariant
    groupElement (inverseCoframeRow geometry.coframe coordinate)
  calc
    diracSlash
          (spinLorentzCover groupElement
            (inverseCoframeRow geometry.coframe coordinate)) *
        spinDiracMatrix groupElement =
      (spinDiracMatrix groupElement *
          diracSlash (inverseCoframeRow geometry.coframe coordinate) *
            spinDiracMatrix groupElement⁻¹) *
        spinDiracMatrix groupElement := by rw [slashCovariance]
    _ = spinDiracMatrix groupElement *
        diracSlash (inverseCoframeRow geometry.coframe coordinate) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc,
        ← spinDiracMatrix_mul]
      simp

/-- Action-facing version on the actual Dirac-exterior carrier. -/
theorem inverseCoframeDiracGamma_matterAction_spinWeylDual_equivariant
    (groupElement : SpinPlus13)
    (geometry : PointwiseLorentzianCoframeJet)
    (coordinate : LorentzianIndex)
    (field : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction
        (inverseCoframeDiracGamma
          { geometry with
              coframe := spinLorentzCoframeRepresentation
                (spinWeylDual groupElement) geometry.coframe }
          coordinate)
        (spinDiracMatterRepresentation groupElement field) =
      spinDiracMatterRepresentation groupElement
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma geometry coordinate) field) := by
  change
    diracMatrixMatterAction
        (inverseCoframeDiracGamma
          { geometry with
              coframe := spinLorentzCoframeRepresentation
                (spinWeylDual groupElement) geometry.coframe }
          coordinate)
        (diracMatrixMatterAction (spinDiracMatrix groupElement) field) =
      diracMatrixMatterAction (spinDiracMatrix groupElement)
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma geometry coordinate) field)
  rw [diracMatrixMatterAction_apply_apply,
    diracMatrixMatterAction_apply_apply,
    inverseCoframeDiracGamma_spinWeylDual_intertwine]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracKineticSpinJurisdiction
