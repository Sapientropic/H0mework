import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert
import H0mework.Physics.Exterior.ExteriorMotherLieRepresentation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceQuantumNativeDimensions

open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SourceQuantumScalarChart
open scoped ComplexConjugate

private theorem entry_re {n : ℕ} (A : SpecialUnitaryLieMatrix (Fin n)) (i j : Fin n) :
    (A.val j i).re = -(A.val i j).re := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).re) A.property.1
  simpa [Matrix.star_apply] using h

private theorem entry_im {n : ℕ} (A : SpecialUnitaryLieMatrix (Fin n)) (i j : Fin n) :
    (A.val j i).im = (A.val i j).im := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).im) A.property.1
  simpa [Matrix.star_apply] using neg_inj.mp h

private def colorMatrix (x : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![x 6 * Complex.I, x 0 + x 1 * Complex.I, x 2 + x 3 * Complex.I;
     -x 0 + x 1 * Complex.I, (-x 6 + x 7) * Complex.I, x 4 + x 5 * Complex.I;
     -x 2 + x 3 * Complex.I, -x 4 + x 5 * Complex.I, -x 7 * Complex.I]

private def colorBuild (x : Fin 8 → ℝ) : SU3BlockLieMatrix :=
  ⟨colorMatrix x, by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [colorMatrix, Matrix.star_apply] <;> ring
    · simp [Matrix.trace, Fin.sum_univ_succ, colorMatrix]; ring⟩

private def colorRead (A : SU3BlockLieMatrix) : Fin 8 → ℝ :=
  ![(A.val 0 1).re, (A.val 0 1).im, (A.val 0 2).re, (A.val 0 2).im,
    (A.val 1 2).re, (A.val 1 2).im, (A.val 0 0).im, -(A.val 2 2).im]

private theorem color_build_read (A : SU3BlockLieMatrix) : colorBuild (colorRead A) = A := by
  have h00 := entry_re A 0 0
  have h11 := entry_re A 1 1
  have h22 := entry_re A 2 2
  have h01 := entry_re A 0 1
  have h02 := entry_re A 0 2
  have h12 := entry_re A 1 2
  have h01i := entry_im A 0 1
  have h02i := entry_im A 0 2
  have h12i := entry_im A 1 2
  have ht := congrArg Complex.im A.property.2
  simp [Matrix.trace, Fin.sum_univ_succ] at ht
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [colorBuild, colorMatrix, colorRead] <;> linarith

private def colorEquiv : SU3BlockLieMatrix ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := colorRead
  invFun := colorBuild
  left_inv := color_build_read
  right_inv x := by ext i; fin_cases i <;> simp [colorRead, colorBuild, colorMatrix]
  map_add' A B := by ext i; fin_cases i <;> simp [colorRead, add_comm]
  map_smul' r A := by ext i; fin_cases i <;> simp [colorRead, mul_neg]

private def weakMatrix (x : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x 2 * Complex.I, x 0 + x 1 * Complex.I;
    -x 0 + x 1 * Complex.I, -x 2 * Complex.I]

private def weakBuild (x : Fin 3 → ℝ) : SU2BlockLieMatrix :=
  ⟨weakMatrix x, by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [weakMatrix, Matrix.star_apply] <;> ring
    · simp [Matrix.trace, Fin.sum_univ_succ, weakMatrix]⟩

private def weakRead (A : SU2BlockLieMatrix) : Fin 3 → ℝ :=
  ![(A.val 0 1).re, (A.val 0 1).im, (A.val 0 0).im]

private theorem weak_build_read (A : SU2BlockLieMatrix) : weakBuild (weakRead A) = A := by
  have h00 := entry_re A 0 0
  have h11 := entry_re A 1 1
  have h01 := entry_re A 0 1
  have h01i := entry_im A 0 1
  have ht := congrArg Complex.im A.property.2
  simp [Matrix.trace, Fin.sum_univ_succ] at ht
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [weakBuild, weakMatrix, weakRead] <;> linarith

private def weakEquiv : SU2BlockLieMatrix ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := weakRead
  invFun := weakBuild
  left_inv := weak_build_read
  right_inv x := by ext i; fin_cases i <;> simp [weakRead, weakBuild, weakMatrix]
  map_add' A B := by ext i; fin_cases i <;> simp [weakRead]
  map_smul' r A := by ext i; fin_cases i <;> simp [weakRead]

private def hyperBuild (r : ℝ) : HyperchargeLieScalar :=
  ⟨r * Complex.I, by
    change star ((r : ℂ) * Complex.I) = -((r : ℂ) * Complex.I)
    simp⟩

private def hyperEquiv : HyperchargeLieScalar ≃ₗ[ℝ] ℝ where
  toFun z := z.val.im
  invFun := hyperBuild
  left_inv z := by
    have hr := congrArg Complex.re z.property
    change (star (z : ℂ)).re = (-(z : ℂ)).re at hr
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
    apply Subtype.ext
    apply Complex.ext <;> simp [hyperBuild]; linarith
  right_inv r := by simp [hyperBuild]
  map_add' a b := by simp
  map_smul' r z := by simp

/-- Coordinates are read from the original special-unitary blocks. -/
def nativeCoordinates : NativeLie ≃ₗ[ℝ] ((Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ) :=
  p286CoordinateEquiv.symm.trans (colorEquiv.prodCongr (weakEquiv.prodCongr hyperEquiv))

theorem nativeCoordinates_apply (a : P286LieBlockData) :
    nativeCoordinates (p286CoordinateEquiv a) =
      (![(a.1.val 0 1).re,(a.1.val 0 1).im,(a.1.val 0 2).re,(a.1.val 0 2).im,
        (a.1.val 1 2).re,(a.1.val 1 2).im,(a.1.val 0 0).im,-(a.1.val 2 2).im],
       ![(a.2.1.val 0 1).re,(a.2.1.val 0 1).im,(a.2.1.val 0 0).im],a.2.2.val.im) := by
  change (colorEquiv.prodCongr (weakEquiv.prodCongr hyperEquiv))
    (p286CoordinateEquiv.symm (p286CoordinateEquiv a)) = _
  rw [p286CoordinateEquiv.symm_apply_apply]
  rfl

theorem nativeLie_finrank : Module.finrank ℝ NativeLie = 12 := by
  rw [nativeCoordinates.finrank_eq]
  simp [Module.finrank_prod]

theorem scalar_finrank : Module.finrank ℝ Scalar = 70 := by
  have hc : Module.finrank ℂ Scalar = 35 := by
    rw [← scalarCoordinateEquiv.finrank_eq]
    exact SU7ExteriorBreakingYukawa.exteriorBreakingScalarCarrier_finrank
  rw [← Module.finrank_mul_finrank ℝ ℂ Scalar, hc]
  norm_num

theorem gauge_finrank : Module.finrank ℝ SourceQuantumConfigurationHilbert.Gauge = 36 := by
  rw [SourceQuantumConfigurationHilbert.gauge_finrank, nativeLie_finrank]



open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineCoframeScalarMatterRegularity StageNineExteriorMotherLieRepresentation
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal

local instance motherOrder : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective
local instance : Preorder SU7MotherIndex := motherOrder.toPreorder
local instance : LT SU7MotherIndex := motherOrder.toLT
local instance : LE SU7MotherIndex := motherOrder.toLE

private theorem position_value (output : ScalarBasisIndex) (col : Fin 4) :
    Set.powersetCard.ofFinEmbEquiv.symm output col = (exteriorPositionEquiv output col).val := rfl

private def slotMatrix (M : Matrix SU7MotherIndex SU7MotherIndex ℂ) (output input : ScalarBasisIndex)
    (slot : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun row col =>
  if row = slot then M (exteriorPositionEquiv output col).val (exteriorPositionEquiv input row).val
  else if (exteriorPositionEquiv input row).val = (exteriorPositionEquiv output col).val then 1 else 0

private theorem exterior_coordinate (M : SU7MotherLieMatrix) (output input : ScalarBasisIndex) :
    (su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output =
      ∑ slot : Fin 4, (slotMatrix (M : Matrix SU7MotherIndex SU7MotherIndex ℂ) output input slot).det := by
  unfold exteriorBasisLieAction
  rw [map_sum]
  change (∑ slot : Fin 4, (su7ExteriorBasis 4).repr
    ((exteriorPower.ιMulti ℂ 4) (exteriorBasisLieActionInput 4 M input slot)) output) = _
  apply Finset.sum_congr rfl
  intro slot _
  rw [su7ExteriorBasis, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  apply congrArg Matrix.det
  ext row col
  by_cases h : row = slot
  · subst row
    simp [slotMatrix, exteriorBasisLieActionInput, fundamentalMotherLieAction,
      su7FundamentalBasis, Matrix.mulVecLin, position_value]
  · simp [slotMatrix, exteriorBasisLieActionInput, h, Ne.symm h, position_value, Finsupp.single_apply, eq_comm]

private theorem orbit_coordinate (a : NativeLie) (output : ScalarBasisIndex) :
    orbit a output = ∑ i : Fin 2, ∑ j : Fin 2, ∑ slot : Fin 4,
      (slotMatrix (rawP286LieBlock (p286CoordinateEquiv.symm a)) output
        (finiteGenerationScalarIndex i j) slot).det := by
  change scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))
    (sourceGeneratedVacuumCoordinates StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource) output = _
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  rw [scalarCoordinateEquiv.symm_apply_apply, positive_sourceGeneratedVacuumBase]
  simp only [finiteGenerationJointBreakingScalar, map_sum, finiteGenerationBreakingTensor,
    exteriorMotherLieAction_basis_slot]
  simp only [scalarCoordinateEquiv, LinearEquiv.trans_apply, WithLp.linearEquiv_symm_apply]
  change (∑ i : Fin 2, ∑ j : Fin 2,
    (su7ExteriorBasis 4).repr (exteriorBasisLieAction 4
      (p286LieBlockEmbed (p286CoordinateEquiv.symm a)) (finiteGenerationScalarIndex i j)) output) = _
  simp_rw [exterior_coordinate]
  rfl

private def motherIndex (i : Fin 7) : SU7MotherIndex := smBlockIndexEquivFin7.symm i

def sourceOrbitReadIndex : Fin 6 → ScalarBasisIndex
  | 0 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 3}, by change Finset.card _ = 4; decide⟩
  | 1 => ⟨{motherIndex 0,motherIndex 2,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 2 => ⟨{motherIndex 1,motherIndex 2,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 3 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 4}, by change Finset.card _ = 4; decide⟩
  | 4 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 5 => ⟨{motherIndex 0,motherIndex 1,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩

private def readOrder : Fin 6 → Fin 4 → Fin 7 :=
  ![![0,1,2,3],![0,2,4,5],![1,2,4,5],![0,1,2,4],![0,1,2,6],![0,1,4,5]]

private def vacuumOrder : Fin 2 → Fin 2 → Fin 4 → Fin 7 :=
  ![![![0,1,2,6],![0,1,2,4]],![![0,1,5,6],![0,1,4,5]]]

private theorem mother_lt (i j : Fin 7) : motherIndex i < motherIndex j ↔ i < j := by
  change smBlockIndexEquivFin7 (motherIndex i) < smBlockIndexEquivFin7 (motherIndex j) ↔ _
  simp [motherIndex]

private theorem read_position (i : Fin 6) (j : Fin 4) :
    (exteriorPositionEquiv (sourceOrbitReadIndex i) j).val = motherIndex (readOrder i j) := by
  have hm : StrictMono (fun k => motherIndex (readOrder i k)) := by
    simp only [StrictMono, mother_lt]
    fin_cases i <;> decide
  have he := Finset.orderEmbOfFin_unique (sourceOrbitReadIndex i).property
    (fun k => show motherIndex (readOrder i k) ∈ (sourceOrbitReadIndex i).val from by
      fin_cases i <;> fin_cases k <;> decide) hm
  exact (congrFun he j).symm

private theorem vacuum_position (i j : Fin 2) (k : Fin 4) :
    (exteriorPositionEquiv (finiteGenerationScalarIndex i j) k).val =
      motherIndex (vacuumOrder i j k) := by
  have hm : StrictMono (fun t => motherIndex (vacuumOrder i j t)) := by
    simp only [StrictMono, mother_lt]
    fin_cases i <;> fin_cases j <;> decide
  have he := Finset.orderEmbOfFin_unique (finiteGenerationScalarIndex i j).property
    (fun t => show motherIndex (vacuumOrder i j t) ∈ (finiteGenerationScalarIndex i j).val from by
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide) hm
  exact (congrFun he k).symm


private theorem native_symm (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    p286CoordinateEquiv.symm (nativeCoordinates.symm (c,w,h)) =
      (colorBuild c,weakBuild w,hyperBuild h) := by
  exact p286CoordinateEquiv.symm_apply_apply _

private def fullMatrix (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) : Matrix (Fin 7) (Fin 7) ℂ :=
  !![c 6 * Complex.I, c 0 + c 1 * Complex.I, c 2 + c 3 * Complex.I, 0, 0, 0, 0;
     -c 0 + c 1 * Complex.I, (-c 6 + c 7) * Complex.I, c 4 + c 5 * Complex.I, 0, 0, 0, 0;
     -c 2 + c 3 * Complex.I, -c 4 + c 5 * Complex.I, -c 7 * Complex.I, 0, 0, 0, 0;
     0, 0, 0, w 2 * Complex.I, w 0 + w 1 * Complex.I, 0, 0;
     0, 0, 0, -w 0 + w 1 * Complex.I, -w 2 * Complex.I, 0, 0;
     0, 0, 0, 0, 0, h * Complex.I, 0;
     0, 0, 0, 0, 0, 0, -(h * Complex.I)]

private theorem native_entry (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) (i j : Fin 7) :
    rawP286LieBlock (colorBuild c,weakBuild w,hyperBuild h) (motherIndex i) (motherIndex j) =
      fullMatrix c w h i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem mother_eq (i j : Fin 7) : motherIndex i = motherIndex j ↔ i = j :=
  smBlockIndexEquivFin7.symm.injective.eq_iff


private def numericSlot (M : Matrix (Fin 7) (Fin 7) ℂ) (output input : Fin 4 → Fin 7)
    (slot : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun row col =>
  if row = slot then M (output col) (input row)
  else if input row = output col then 1 else 0

private theorem numericSlot_row (M : Matrix (Fin 7) (Fin 7) ℂ)
    (output input : Fin 4 → Fin 7) (slot : Fin 4) :
    (numericSlot M output input slot).det = ∑ j : Fin 4,
      (-1 : ℂ) ^ ((slot : ℕ) + (j : ℕ)) * M (output j) (input slot) *
        Matrix.det (fun r c : Fin 3 => if input (slot.succAbove r) = output (j.succAbove c)
          then (1 : ℂ) else 0) := by
  rw [Matrix.det_succ_row _ slot]
  apply Finset.sum_congr rfl
  intro j _
  have hm : (numericSlot M output input slot).submatrix slot.succAbove j.succAbove =
      (fun r c : Fin 3 => if input (slot.succAbove r) = output (j.succAbove c)
        then (1 : ℂ) else 0) := by
    ext r c
    simp [Matrix.submatrix_apply, numericSlot, Fin.succAbove_ne]
  rw [hm]
  simp [numericSlot]

private theorem native_slot (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ)
    (i : Fin 6) (j k : Fin 2) (slot : Fin 4) :
    slotMatrix (rawP286LieBlock (colorBuild c,weakBuild w,hyperBuild h))
      (sourceOrbitReadIndex i) (finiteGenerationScalarIndex j k) slot =
      numericSlot (fullMatrix c w h) (readOrder i) (vacuumOrder j k) slot := by
  ext row col
  simp [slotMatrix, numericSlot, read_position, vacuum_position, native_entry, mother_eq]

private def numericRead (M : Matrix (Fin 7) (Fin 7) ℂ) : Fin 6 → ℂ :=
  ![M 3 4 + M 3 6, M 2 1 + M 5 1, -M 2 0 - M 5 0,
    M 0 0 + M 1 1 + M 2 2 + M 4 4 + M 4 6 - M 2 5,
    M 0 0 + M 1 1 + M 2 2 + M 6 6 + M 6 4 + M 2 5,
    M 0 0 + M 1 1 + M 4 4 + M 5 5 - M 5 2 - M 4 6]

private theorem det_four (A : Matrix (Fin 4) (Fin 4) ℂ) :
    A.det = ∑ j : Fin 4, (-1 : ℂ) ^ (j : ℕ) * A 0 j *
      (A.submatrix Fin.succ j.succAbove).det := Matrix.det_succ_row_zero A

set_option maxRecDepth 8192 in
private theorem numeric_orbit_0 (M : Matrix (Fin 7) (Fin 7) ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder 0) (vacuumOrder j k) slot).det) = numericRead M 0 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot M ![0,1,2,3] (vacuumOrder j k) slot).det) = M 3 4 + M 3 6
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four, Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ, Matrix.submatrix_apply]
  norm_num [numericSlot, vacuumOrder, Fin.ext_iff, Fin.succ, Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

set_option maxRecDepth 8192 in
private theorem numeric_orbit_1 (M : Matrix (Fin 7) (Fin 7) ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder 1) (vacuumOrder j k) slot).det) = numericRead M 1 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot M ![0,2,4,5] (vacuumOrder j k) slot).det) = M 2 1 + M 5 1
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four, Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ, Matrix.submatrix_apply]
  norm_num [numericSlot, vacuumOrder, Fin.ext_iff, Fin.succ, Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

set_option maxRecDepth 8192 in
private theorem numeric_orbit_2 (M : Matrix (Fin 7) (Fin 7) ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder 2) (vacuumOrder j k) slot).det) = numericRead M 2 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot M ![1,2,4,5] (vacuumOrder j k) slot).det) = -M 2 0 - M 5 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four, Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ, Matrix.submatrix_apply]
  norm_num [numericSlot, vacuumOrder, Fin.ext_iff, Fin.succ, Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

set_option maxRecDepth 8192 in
private theorem numeric_orbit_3 (M : Matrix (Fin 7) (Fin 7) ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder 3) (vacuumOrder j k) slot).det) = numericRead M 3 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot M ![0,1,2,4] (vacuumOrder j k) slot).det) = M 0 0 + M 1 1 + M 2 2 + M 4 4 + M 4 6 - M 2 5
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four, Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ, Matrix.submatrix_apply]
  norm_num [numericSlot, vacuumOrder, Fin.ext_iff, Fin.succ, Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

set_option maxRecDepth 8192 in
private theorem numeric_orbit_4 (M : Matrix (Fin 7) (Fin 7) ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder 4) (vacuumOrder j k) slot).det) = numericRead M 4 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot M ![0,1,2,6] (vacuumOrder j k) slot).det) = M 0 0 + M 1 1 + M 2 2 + M 6 6 + M 6 4 + M 2 5
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four, Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ, Matrix.submatrix_apply]
  norm_num [numericSlot, vacuumOrder, Fin.ext_iff, Fin.succ, Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

set_option maxRecDepth 8192 in
private theorem numeric_orbit_5 (M : Matrix (Fin 7) (Fin 7) ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder 5) (vacuumOrder j k) slot).det) = numericRead M 5 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot M ![0,1,4,5] (vacuumOrder j k) slot).det) = M 0 0 + M 1 1 + M 4 4 + M 5 5 - M 5 2 - M 4 6
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four, Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ, Matrix.submatrix_apply]
  norm_num [numericSlot, vacuumOrder, Fin.ext_iff, Fin.succ, Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

private theorem numeric_orbit (M : Matrix (Fin 7) (Fin 7) ℂ) (i : Fin 6) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot M (readOrder i) (vacuumOrder j k) slot).det) = numericRead M i := by
  fin_cases i
  · exact numeric_orbit_0 M
  · exact numeric_orbit_1 M
  · exact numeric_orbit_2 M
  · exact numeric_orbit_3 M
  · exact numeric_orbit_4 M
  · exact numeric_orbit_5 M

set_option backward.isDefEq.respectTransparency false in
theorem sourceOrbit_read (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) (i : Fin 6) :
    orbit (nativeCoordinates.symm (c,w,h)) (sourceOrbitReadIndex i) =
      ![(w 0 : ℂ) + w 1 * Complex.I, -c 4 + c 5 * Complex.I,
        c 2 - c 3 * Complex.I, -w 2 * Complex.I, -h * Complex.I,
        (c 7 - w 2 + h) * Complex.I] i := by
  rw [orbit_coordinate, native_symm]
  simp_rw [native_slot]
  rw [numeric_orbit]
  fin_cases i
  · change (w 0 : ℂ) + w 1 * Complex.I + 0 = _
    change (w 0 : ℂ) + w 1 * Complex.I + 0 = (w 0 : ℂ) + w 1 * Complex.I
    ring
  · change -(c 4 : ℂ) + c 5 * Complex.I + 0 = -(c 4 : ℂ) + c 5 * Complex.I
    ring
  · change -(-(c 2 : ℂ) + c 3 * Complex.I) - 0 = (c 2 : ℂ) - c 3 * Complex.I
    ring
  · change (c 6 : ℂ)*Complex.I + (-(c 6 : ℂ)+c 7)*Complex.I +
      (-(c 7 : ℂ)*Complex.I) + (-(w 2 : ℂ)*Complex.I) + 0 - 0 = -(w 2 : ℂ)*Complex.I
    ring
  · change (c 6 : ℂ)*Complex.I + (-(c 6 : ℂ)+c 7)*Complex.I +
      (-(c 7 : ℂ)*Complex.I) + (-((h : ℂ)*Complex.I)) + 0 + 0 = -(h : ℂ)*Complex.I
    ring
  · change (c 6 : ℂ)*Complex.I + (-(c 6 : ℂ)+c 7)*Complex.I +
      (-(w 2 : ℂ)*Complex.I) + (h : ℂ)*Complex.I - 0 - 0 =
        ((c 7 : ℂ) - w 2 + h)*Complex.I
    ring


end LowEnergy.SourceQuantumNativeDimensions
