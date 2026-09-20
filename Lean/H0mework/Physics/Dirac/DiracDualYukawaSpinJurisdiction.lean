import H0mework.Physics.Dirac.SpinMatterBundle

/-!
# Dirac-dual Yukawa Spin jurisdiction

`StageNineContinuumPointField.conjugateMatter` is an independent complex
linear dual and every existing gauge/frame transporter acts on it by inverse
precomposition.  It therefore already has the transformation law of the
Dirac dual `bar psi`, rather than that of an unconverted Hermitian row
`psi dagger`.  In this jurisdiction a second `gamma^0` inside the Yukawa
operator is not a harmless convention: it destroys finite Spin covariance.

This module derives the positive repair directly from the existing chiral
and internal representation structure.  The right projector selects the
matter input, while the contragredient dual supplies the physical barred-left
pairing.  The internal Yukawa map then needs no extra Clifford matrix:

`Y_dual(phi) = Y_internal(phi) ∘ P_R`.

The repaired map is nonzero on the actual Stage-8 Yukawa witness and commutes
with every generated finite Spin action.  A concrete `spinDilation` matrix
regression proves that the historical `P_L gamma^0 P_R` Dirac factor does not
commute.  No replacement coupling, field, normalization, covariance receipt,
or target solution is introduced.  This is the action-jurisdiction core for
the next form-native action epoch; it does not itself modify that action.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualYukawaSpinJurisdiction

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineGlobalBundle
open StageNineSpinMatterBundle
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation

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

/-! ## Finite Spin preservation of chirality -/

theorem spinDiracMatrix_leftChiralityProjector_commute
    (groupElement : SpinPlus13) :
    spinDiracMatrix groupElement * leftChiralityProjector =
      leftChiralityProjector * spinDiracMatrix groupElement := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spinDiracMatrix, Matrix.reindexRingEquiv,
      Matrix.reindexAddEquiv, Matrix.reindex, Matrix.submatrix,
      weylDiracBlockMatrix, Matrix.fromBlocks,
      leftChiralityProjector, diracGammaFive,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;> ring

theorem spinDiracMatrix_rightChiralityProjector_commute
    (groupElement : SpinPlus13) :
    spinDiracMatrix groupElement * rightChiralityProjector =
      rightChiralityProjector * spinDiracMatrix groupElement := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spinDiracMatrix, Matrix.reindexRingEquiv,
      Matrix.reindexAddEquiv, Matrix.reindex, Matrix.submatrix,
      weylDiracBlockMatrix, Matrix.fromBlocks,
      rightChiralityProjector, diracGammaFive,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;> ring

theorem rightChiralityMatterAction_spin_commute
    (groupElement : SpinPlus13) (field : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction rightChiralityProjector
        (spinDiracMatterRepresentation groupElement field) =
      spinDiracMatterRepresentation groupElement
        (diracMatrixMatterAction rightChiralityProjector field) := by
  change
    diracMatrixMatterAction rightChiralityProjector
        (diracMatrixMatterAction (spinDiracMatrix groupElement) field) =
      diracMatrixMatterAction (spinDiracMatrix groupElement)
        (diracMatrixMatterAction rightChiralityProjector field)
  rw [diracMatrixMatterAction_apply_apply,
    diracMatrixMatterAction_apply_apply,
    ← spinDiracMatrix_rightChiralityProjector_commute]

/-! ## Positive Dirac-dual Yukawa operator -/

/-- Right-chiral Yukawa operator appropriate for the existing independent
Dirac-dual carrier.  The barred-left interpretation is carried by the dual,
not by inserting another `gamma^0` into this vector operator. -/
def diracDualRightChiralYukawaAction
    (scalar : ExteriorBreakingScalarCarrier) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  (diracExteriorYukawaInternalAction scalar).comp
    (diracMatrixMatterAction rightChiralityProjector)

theorem diracDualRightChiralYukawaAction_consumes_right
    (scalar : ExteriorBreakingScalarCarrier)
    (field : DiracExteriorMatterCarrier) :
    diracDualRightChiralYukawaAction scalar
        (diracMatrixMatterAction rightChiralityProjector field) =
      diracDualRightChiralYukawaAction scalar field := by
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  rw [diracMatrixMatterAction_apply_apply,
    rightChiralityProjector_sq]

theorem diracDualRightChiralYukawaAction_output_right
    (scalar : ExteriorBreakingScalarCarrier)
    (field : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction rightChiralityProjector
        (diracDualRightChiralYukawaAction scalar field) =
      diracDualRightChiralYukawaAction scalar field := by
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  have commute := LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal rightChiralityProjector
      (exteriorYukawaInternalAction scalar))
    (diracMatrixMatterAction rightChiralityProjector field)
  calc
    diracMatrixMatterAction rightChiralityProjector
        (diracExteriorYukawaInternalAction scalar
          (diracMatrixMatterAction rightChiralityProjector field)) =
      diracExteriorYukawaInternalAction scalar
        (diracMatrixMatterAction rightChiralityProjector
          (diracMatrixMatterAction rightChiralityProjector field)) := by
            exact commute
    _ = diracExteriorYukawaInternalAction scalar
        (diracMatrixMatterAction rightChiralityProjector field) := by
      rw [diracMatrixMatterAction_apply_apply,
        rightChiralityProjector_sq]

/-- The repaired operator commutes with every finite Spin action generated by
the actual chiral Dirac representation. -/
theorem diracDualRightChiralYukawaAction_spin_equivariant
    (groupElement : SpinPlus13)
    (scalar : ExteriorBreakingScalarCarrier) :
    (diracDualRightChiralYukawaAction scalar).comp
        (spinDiracMatterRepresentation groupElement) =
      (spinDiracMatterRepresentation groupElement).comp
        (diracDualRightChiralYukawaAction scalar) := by
  apply LinearMap.ext
  intro field
  change
    diracExteriorYukawaInternalAction scalar
        (diracMatrixMatterAction rightChiralityProjector
          (spinDiracMatterRepresentation groupElement field)) =
      spinDiracMatterRepresentation groupElement
        (diracExteriorYukawaInternalAction scalar
          (diracMatrixMatterAction rightChiralityProjector field))
  rw [rightChiralityMatterAction_spin_commute]
  have commute := LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal
      (spinDiracMatrix groupElement)
      (exteriorYukawaInternalAction scalar))
    (diracMatrixMatterAction rightChiralityProjector field)
  exact commute.symm

/-- Actual right-handed Dirac probe carrying the existing nonzero
degree-two Yukawa witness. -/
def diracRightYukawaProbe : DiracExteriorMatterCarrier :=
  fun spinIndex =>
    if spinIndex = 2 then
      (0, (exteriorYukawaDegreeTwoProbe, 0))
    else 0

theorem rightChiralityProjector_diracRightYukawaProbe :
    diracMatrixMatterAction rightChiralityProjector
        diracRightYukawaProbe =
      diracRightYukawaProbe := by
  funext spinIndex
  fin_cases spinIndex <;>
    simp [diracMatrixMatterAction, diracRightYukawaProbe,
      rightChiralityProjector, diracGammaFive,
      Matrix.diagonal_apply, Fin.sum_univ_four]
  all_goals norm_num

theorem diracDualRightChiralYukawaAction_probe_component :
    (diracDualRightChiralYukawaAction exteriorBreakingScalar
        diracRightYukawaProbe 2).1 =
      exteriorYukawaMassMap exteriorBreakingScalar
        exteriorYukawaDegreeTwoProbe := by
  rw [diracDualRightChiralYukawaAction,
    LinearMap.comp_apply,
    rightChiralityProjector_diracRightYukawaProbe]
  rfl

theorem diracDualRightChiralYukawaAction_nonzero :
    diracDualRightChiralYukawaAction exteriorBreakingScalar ≠ 0 := by
  intro operatorZero
  have probeZero := LinearMap.congr_fun operatorZero diracRightYukawaProbe
  have componentZero := congrArg
    (fun field : DiracExteriorMatterCarrier => (field 2).1) probeZero
  rw [diracDualRightChiralYukawaAction_probe_component] at componentZero
  simp only [LinearMap.zero_apply, Pi.zero_apply, Prod.fst_zero] at componentZero
  exact exteriorYukawaProbe_massMap_ne_zero componentZero

/-! ## Historical gamma-zero placement regression -/

theorem rightWeylMatrix_spinDilation :
    rightWeylMatrix spinDilation =
      Matrix.diagonal ![(1 / 2 : ℂ), (2 : ℂ)] := by
  unfold rightWeylMatrix
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  change
    star (Matrix.adjugate (Matrix.diagonal ![(2 : ℂ), (1 / 2 : ℂ)])) =
      Matrix.diagonal ![(1 / 2 : ℂ), (2 : ℂ)]
  rw [Matrix.adjugate_fin_two]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.diagonal_apply]

theorem spinDiracMatrix_spinDilation_left_left
    (row column : Fin 2) :
    spinDiracMatrix spinDilation
        (Fin.castAdd 2 row) (Fin.castAdd 2 column) =
      spinDilation row column := by
  unfold spinDiracMatrix weylDiracBlockMatrix
  rw [rightWeylMatrix_spinDilation]
  simp [Matrix.reindexRingEquiv, Matrix.reindexAddEquiv,
    Matrix.reindex, Matrix.submatrix, Matrix.fromBlocks,
    finSumFinEquiv_symm_castAdd_two]

theorem spinDiracMatrix_spinDilation_left_right
    (row column : Fin 2) :
    spinDiracMatrix spinDilation
        (Fin.castAdd 2 row) (Fin.natAdd 2 column) = 0 := by
  unfold spinDiracMatrix weylDiracBlockMatrix
  rw [rightWeylMatrix_spinDilation]
  simp [Matrix.reindexRingEquiv, Matrix.reindexAddEquiv,
    Matrix.reindex, Matrix.submatrix, Matrix.fromBlocks,
    finSumFinEquiv_symm_castAdd_two,
    finSumFinEquiv_symm_addNat_two]

theorem spinDiracMatrix_spinDilation_right_right
    (row column : Fin 2) :
    spinDiracMatrix spinDilation
        (Fin.natAdd 2 row) (Fin.natAdd 2 column) =
      Matrix.diagonal ![(1 / 2 : ℂ), (2 : ℂ)] row column := by
  unfold spinDiracMatrix weylDiracBlockMatrix
  rw [rightWeylMatrix_spinDilation]
  simp [Matrix.reindexRingEquiv, Matrix.reindexAddEquiv,
    Matrix.reindex, Matrix.submatrix, Matrix.fromBlocks,
    finSumFinEquiv_symm_addNat_two]

theorem spinDiracMatrix_spinDilation_column_two (row : Fin 4) :
    spinDiracMatrix spinDilation row 2 =
      if row = 2 then 1 / 2 else 0 := by
  fin_cases row
  · simpa using spinDiracMatrix_spinDilation_left_right 0 0
  · simpa using spinDiracMatrix_spinDilation_left_right 1 0
  · simpa [Matrix.diagonal_apply] using
      spinDiracMatrix_spinDilation_right_right 0 0
  · simpa [Matrix.diagonal_apply] using
      spinDiracMatrix_spinDilation_right_right 1 0

theorem spinDiracMatrix_spinDilation_row_zero (column : Fin 4) :
    spinDiracMatrix spinDilation 0 column =
      if column = 0 then 2 else 0 := by
  fin_cases column
  · simpa [spinDilation, Matrix.diagonal_apply] using
      spinDiracMatrix_spinDilation_left_left 0 0
  · simpa [spinDilation, Matrix.diagonal_apply] using
      spinDiracMatrix_spinDilation_left_left 0 1
  · simpa using spinDiracMatrix_spinDilation_left_right 0 0
  · simpa using spinDiracMatrix_spinDilation_left_right 0 1

/-- Dirac-index factor of the historical cross-chiral Yukawa operator. -/
def historicalChiralYukawaDiracFactor : DiracMatrix :=
  leftChiralityProjector * diracGamma 0 * rightChiralityProjector

theorem chiralExteriorYukawaAction_eq_historicalDiracFactor
    (scalar : ExteriorBreakingScalarCarrier)
    (field : DiracExteriorMatterCarrier) :
    chiralExteriorYukawaAction scalar field =
      diracExteriorYukawaInternalAction scalar
        (diracMatrixMatterAction historicalChiralYukawaDiracFactor field) := by
  unfold chiralExteriorYukawaAction
  simp only [LinearMap.comp_apply]
  have gammaCommute := LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal (diracGamma 0)
      (exteriorYukawaInternalAction scalar))
    (diracMatrixMatterAction rightChiralityProjector field)
  have gammaCommute' :
      diracMatrixMatterAction (diracGamma 0)
          (diracExteriorYukawaInternalAction scalar
            (diracMatrixMatterAction rightChiralityProjector field)) =
        diracExteriorYukawaInternalAction scalar
          (diracMatrixMatterAction (diracGamma 0)
            (diracMatrixMatterAction rightChiralityProjector field)) := by
    simpa [diracExteriorYukawaInternalAction] using gammaCommute
  rw [gammaCommute']
  have leftCommute := LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal leftChiralityProjector
      (exteriorYukawaInternalAction scalar))
    (diracMatrixMatterAction (diracGamma 0)
      (diracMatrixMatterAction rightChiralityProjector field))
  have leftCommute' :
      diracMatrixMatterAction leftChiralityProjector
          (diracExteriorYukawaInternalAction scalar
            (diracMatrixMatterAction (diracGamma 0)
              (diracMatrixMatterAction rightChiralityProjector field))) =
        diracExteriorYukawaInternalAction scalar
          (diracMatrixMatterAction leftChiralityProjector
            (diracMatrixMatterAction (diracGamma 0)
              (diracMatrixMatterAction rightChiralityProjector field))) := by
    simpa [diracExteriorYukawaInternalAction] using leftCommute
  rw [leftCommute',
    diracMatrixMatterAction_apply_apply,
    diracMatrixMatterAction_apply_apply]
  rfl

theorem historicalChiralYukawaDiracFactor_row_zero (column : Fin 4) :
    historicalChiralYukawaDiracFactor 0 column =
      if column = 2 then 1 else 0 := by
  fin_cases column <;>
    simp [historicalChiralYukawaDiracFactor,
      leftChiralityProjector, rightChiralityProjector,
      diracGammaFive, diracGamma, diracGammaZero,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.sum_univ_four]
  all_goals ring

theorem historicalChiralYukawaDiracFactor_column_two (row : Fin 4) :
    historicalChiralYukawaDiracFactor row 2 =
      if row = 0 then 1 else 0 := by
  fin_cases row <;>
    simp [historicalChiralYukawaDiracFactor,
      leftChiralityProjector, rightChiralityProjector,
      diracGammaFive, diracGamma, diracGammaZero,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.sum_univ_four]
  all_goals ring

theorem historicalChiralYukawaDiracFactor_spinDilation_left_component :
    (historicalChiralYukawaDiracFactor * spinDiracMatrix spinDilation)
        0 2 = 1 / 2 := by
  simp [Matrix.mul_apply,
    historicalChiralYukawaDiracFactor_row_zero,
    spinDiracMatrix_spinDilation_column_two]

theorem historicalChiralYukawaDiracFactor_spinDilation_right_component :
    (spinDiracMatrix spinDilation * historicalChiralYukawaDiracFactor)
        0 2 = 2 := by
  simp [Matrix.mul_apply,
    spinDiracMatrix_spinDilation_row_zero,
    historicalChiralYukawaDiracFactor_column_two]

/-- The historical `P_L gamma^0 P_R` factor fails finite Spin covariance on
an actual nontrivial group element.  Together with the nonzero internal
Yukawa witness above, this rules out a zero-operator escape. -/
theorem historicalChiralYukawaDiracFactor_spinDilation_not_commute :
    historicalChiralYukawaDiracFactor * spinDiracMatrix spinDilation ≠
      spinDiracMatrix spinDilation * historicalChiralYukawaDiracFactor := by
  intro equality
  have componentEquality := congrArg
    (fun matrix : DiracMatrix => matrix 0 2) equality
  rw [historicalChiralYukawaDiracFactor_spinDilation_left_component,
    historicalChiralYukawaDiracFactor_spinDilation_right_component]
    at componentEquality
  norm_num at componentEquality

/-- Jurisdiction checkpoint: the generated replacement is both nonzero and
Spin equivariant, while the historical Dirac factor is not. -/
theorem diracDualYukawaSpinJurisdiction :
    diracDualRightChiralYukawaAction exteriorBreakingScalar ≠ 0 ∧
      (∀ groupElement : SpinPlus13,
        (diracDualRightChiralYukawaAction exteriorBreakingScalar).comp
            (spinDiracMatterRepresentation groupElement) =
          (spinDiracMatterRepresentation groupElement).comp
            (diracDualRightChiralYukawaAction exteriorBreakingScalar)) ∧
      historicalChiralYukawaDiracFactor *
          spinDiracMatrix spinDilation ≠
        spinDiracMatrix spinDilation * historicalChiralYukawaDiracFactor := by
  exact ⟨diracDualRightChiralYukawaAction_nonzero,
    fun groupElement =>
      diracDualRightChiralYukawaAction_spin_equivariant groupElement
        exteriorBreakingScalar,
    historicalChiralYukawaDiracFactor_spinDilation_not_commute⟩

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualYukawaSpinJurisdiction
