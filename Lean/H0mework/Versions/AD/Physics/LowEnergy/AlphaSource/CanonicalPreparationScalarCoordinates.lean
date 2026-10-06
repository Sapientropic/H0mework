import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceQuantumScalarOrbitDimensions

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationScalarCoordinates
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineCoframeScalarMatterRegularity StageNineExteriorMotherLieRepresentation
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open scoped RealInnerProductSpace

private def motherIndex (i : Fin 7) : SU7MotherIndex := smBlockIndexEquivFin7.symm i

def lexIndex : Fin 35 → ScalarBasisIndex
  | 0 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 3}, by change Finset.card _ = 4; decide⟩
  | 1 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 4}, by change Finset.card _ = 4; decide⟩
  | 2 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 3 => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 4 => ⟨{motherIndex 0,motherIndex 1,motherIndex 3,motherIndex 4}, by change Finset.card _ = 4; decide⟩
  | 5 => ⟨{motherIndex 0,motherIndex 1,motherIndex 3,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 6 => ⟨{motherIndex 0,motherIndex 1,motherIndex 3,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 7 => ⟨{motherIndex 0,motherIndex 1,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 8 => ⟨{motherIndex 0,motherIndex 1,motherIndex 4,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 9 => ⟨{motherIndex 0,motherIndex 1,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 10 => ⟨{motherIndex 0,motherIndex 2,motherIndex 3,motherIndex 4}, by change Finset.card _ = 4; decide⟩
  | 11 => ⟨{motherIndex 0,motherIndex 2,motherIndex 3,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 12 => ⟨{motherIndex 0,motherIndex 2,motherIndex 3,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 13 => ⟨{motherIndex 0,motherIndex 2,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 14 => ⟨{motherIndex 0,motherIndex 2,motherIndex 4,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 15 => ⟨{motherIndex 0,motherIndex 2,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 16 => ⟨{motherIndex 0,motherIndex 3,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 17 => ⟨{motherIndex 0,motherIndex 3,motherIndex 4,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 18 => ⟨{motherIndex 0,motherIndex 3,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 19 => ⟨{motherIndex 0,motherIndex 4,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 20 => ⟨{motherIndex 1,motherIndex 2,motherIndex 3,motherIndex 4}, by change Finset.card _ = 4; decide⟩
  | 21 => ⟨{motherIndex 1,motherIndex 2,motherIndex 3,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 22 => ⟨{motherIndex 1,motherIndex 2,motherIndex 3,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 23 => ⟨{motherIndex 1,motherIndex 2,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 24 => ⟨{motherIndex 1,motherIndex 2,motherIndex 4,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 25 => ⟨{motherIndex 1,motherIndex 2,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 26 => ⟨{motherIndex 1,motherIndex 3,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 27 => ⟨{motherIndex 1,motherIndex 3,motherIndex 4,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 28 => ⟨{motherIndex 1,motherIndex 3,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 29 => ⟨{motherIndex 1,motherIndex 4,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 30 => ⟨{motherIndex 2,motherIndex 3,motherIndex 4,motherIndex 5}, by change Finset.card _ = 4; decide⟩
  | 31 => ⟨{motherIndex 2,motherIndex 3,motherIndex 4,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 32 => ⟨{motherIndex 2,motherIndex 3,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 33 => ⟨{motherIndex 2,motherIndex 4,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | 34 => ⟨{motherIndex 3,motherIndex 4,motherIndex 5,motherIndex 6}, by change Finset.card _ = 4; decide⟩
  | _ => ⟨{motherIndex 0,motherIndex 1,motherIndex 2,motherIndex 3}, by change Finset.card _ = 4; decide⟩

def lexOrder : Fin 35 → Fin 4 → Fin 7 :=
  ![![0,1,2,3],![0,1,2,4],![0,1,2,5],![0,1,2,6],![0,1,3,4],![0,1,3,5],![0,1,3,6],![0,1,4,5],![0,1,4,6],![0,1,5,6],![0,2,3,4],![0,2,3,5],![0,2,3,6],![0,2,4,5],![0,2,4,6],![0,2,5,6],![0,3,4,5],![0,3,4,6],![0,3,5,6],![0,4,5,6],![1,2,3,4],![1,2,3,5],![1,2,3,6],![1,2,4,5],![1,2,4,6],![1,2,5,6],![1,3,4,5],![1,3,4,6],![1,3,5,6],![1,4,5,6],![2,3,4,5],![2,3,4,6],![2,3,5,6],![2,4,5,6],![3,4,5,6]]

theorem lex_bijective : Function.Bijective lexIndex := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · change ∀ i j, lexIndex i = lexIndex j → i=j
    decide
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    change 35 = Nat.card (Set.powersetCard SU7MotherIndex 4)
    rw [Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_congr smBlockIndexEquivFin7]
    decide

def lexEquiv : Fin 35 ≃ ScalarBasisIndex := Equiv.ofBijective lexIndex lex_bijective

def realSlot (i : Fin 35) : Fin 70 := ⟨i.val, by omega⟩
def imagSlot (i : Fin 35) : Fin 70 := ⟨35+i.val, by omega⟩

def scalarRead (phi : Scalar) (i : Fin 70) : ℝ :=
  if h : i.val < 35 then (phi (lexIndex ⟨i.val,h⟩)).re
  else (phi (lexIndex ⟨i.val-35,by omega⟩)).im

def scalarBuild (x : Fin 70 → ℝ) : Scalar :=
  WithLp.toLp 2 fun i => (x (realSlot (lexEquiv.symm i)) : ℂ) +
    (x (imagSlot (lexEquiv.symm i)) : ℂ)*Complex.I

theorem scalar_read_real (phi : Scalar) (i : Fin 35) :
    scalarRead phi (realSlot i)=(phi (lexIndex i)).re := by
  simp [scalarRead,realSlot]

theorem scalar_read_imag (phi : Scalar) (i : Fin 35) :
    scalarRead phi (imagSlot i)=(phi (lexIndex i)).im := by
  simp [scalarRead,imagSlot]

def scalarRealify : Scalar ≃ₗ[ℝ] (Fin 70 → ℝ) where
  toFun := scalarRead
  invFun := scalarBuild
  left_inv phi := by
    ext i
    apply Complex.ext <;> simp [scalarBuild,scalar_read_real,scalar_read_imag,
      show lexIndex (lexEquiv.symm i)=i from lexEquiv.apply_symm_apply i]
  right_inv x := by
    ext i
    by_cases hi : i.val<35
    · simp [scalarRead,scalarBuild,hi,lexEquiv,realSlot,imagSlot]
    · simp [scalarRead,scalarBuild,hi,lexEquiv,realSlot,imagSlot]
      congr 1
      apply Fin.ext
      change 35+(i.val-35)=i.val
      omega
  map_add' phi psi := by
    ext i
    by_cases hi : i.val<35 <;> simp [scalarRead,hi]
  map_smul' r phi := by
    ext i
    by_cases hi : i.val<35 <;> simp [scalarRead,hi]


local instance motherOrder : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective
local instance : Preorder SU7MotherIndex := motherOrder.toPreorder
local instance : LT SU7MotherIndex := motherOrder.toLT
local instance : LE SU7MotherIndex := motherOrder.toLE

private theorem mother_lt (i j : Fin 7) : motherIndex i < motherIndex j ↔ i < j := by
  change smBlockIndexEquivFin7 (motherIndex i) < smBlockIndexEquivFin7 (motherIndex j) ↔ _
  simp [motherIndex]

private theorem lex_position (i : Fin 35) (j : Fin 4) :
    (exteriorPositionEquiv (lexIndex i) j).val = motherIndex (lexOrder i j) := by
  have hm : StrictMono (fun k => motherIndex (lexOrder i k)) := by
    change ∀ a b, a < b → smBlockIndexEquivFin7 (motherIndex (lexOrder i a)) <
      smBlockIndexEquivFin7 (motherIndex (lexOrder i b))
    simp only [motherIndex,Equiv.apply_symm_apply]
    fin_cases i <;> decide
  have he := Finset.orderEmbOfFin_unique (lexIndex i).property
    (fun k => show motherIndex (lexOrder i k) ∈ (lexIndex i).val from by
      fin_cases i <;> fin_cases k <;> decide) hm
  exact (congrFun he j).symm
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

private def vacuumOrder : Fin 2 → Fin 2 → Fin 4 → Fin 7 :=
  ![![![0,1,2,6],![0,1,2,4]],![![0,1,5,6],![0,1,4,5]]]

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

private def hyperBuild (r : ℝ) : HyperchargeLieScalar :=
  ⟨r * Complex.I, by
    change star ((r : ℂ) * Complex.I) = -((r : ℂ) * Complex.I)
    simp⟩


private theorem native_symm (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    p286CoordinateEquiv.symm (nativeCoordinates.symm (c,w,h)) =
      (colorBuild c,weakBuild w,hyperBuild h) := by
  apply p286CoordinateEquiv.injective
  apply nativeCoordinates.injective
  rw [p286CoordinateEquiv.apply_symm_apply,nativeCoordinates.apply_symm_apply,nativeCoordinates_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [colorBuild,colorMatrix]
  · apply Prod.ext
    · ext i; fin_cases i <;> simp [weakBuild,weakMatrix]
    · simp [hyperBuild]
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


private theorem native_slot_all (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ)
    (i : Fin 35) (j k : Fin 2) (slot : Fin 4) :
    slotMatrix (rawP286LieBlock (colorBuild c,weakBuild w,hyperBuild h))
      (lexIndex i) (finiteGenerationScalarIndex j k) slot =
      numericSlot (fullMatrix c w h) (lexOrder i) (vacuumOrder j k) slot := by
  ext row col
  simp [slotMatrix, numericSlot, lex_position, vacuum_position, native_entry, mother_eq]

private theorem det_four (A : Matrix (Fin 4) (Fin 4) ℂ) :
    A.det = ∑ j : Fin 4, (-1 : ℂ) ^ (j : ℕ) * A 0 j *
      (A.submatrix Fin.succ j.succAbove).det := Matrix.det_succ_row_zero A

-- All 35 slots are in the original exterior-four lex order.
def sourceOrbit35 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) : Fin 35 → ℂ :=
  ![(w 0 : ℂ)+w 1*Complex.I,-w 2*Complex.I,0,-h*Complex.I,0,
    (w 0 : ℂ)+w 1*Complex.I,0,(c 7-w 2+h)*Complex.I,0,c 7*Complex.I,
    0,0,0,-c 4+c 5*Complex.I,0,-c 4+c 5*Complex.I,0,0,0,0,0,0,0,
    (c 2 : ℂ)-c 3*Complex.I,0,(c 2 : ℂ)-c 3*Complex.I,0,0,0,0,0,0,0,0,0]

private theorem numeric_orbit_0 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 0) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 0 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,2,3] (vacuumOrder j k) slot).det) = (w 0 : ℂ)+w 1*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_1 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 1) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 1 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,2,4] (vacuumOrder j k) slot).det) = -w 2*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_2 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 2) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 2 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,2,5] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_3 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 3) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 3 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,2,6] (vacuumOrder j k) slot).det) = -h*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_4 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 4) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 4 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,3,4] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]

private theorem numeric_orbit_5 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 5) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 5 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,3,5] (vacuumOrder j k) slot).det) = (w 0 : ℂ)+w 1*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_6 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 6) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 6 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,3,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]

private theorem numeric_orbit_7 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 7) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 7 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,4,5] (vacuumOrder j k) slot).det) = (c 7-w 2+h)*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_8 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 8) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 8 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,4,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_9 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 9) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 9 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,1,5,6] (vacuumOrder j k) slot).det) = c 7*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_10 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 10) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 10 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,2,3,4] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_11 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 11) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 11 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,2,3,5] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_12 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 12) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 12 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,2,3,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_13 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 13) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 13 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,2,4,5] (vacuumOrder j k) slot).det) = -c 4+c 5*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]

private theorem numeric_orbit_14 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 14) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 14 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,2,4,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_15 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 15) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 15 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,2,5,6] (vacuumOrder j k) slot).det) = -c 4+c 5*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]

private theorem numeric_orbit_16 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 16) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 16 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,3,4,5] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_17 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 17) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 17 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,3,4,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_18 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 18) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 18 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,3,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_19 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 19) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 19 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![0,4,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_20 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 20) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 20 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,2,3,4] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_21 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 21) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 21 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,2,3,5] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_22 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 22) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 22 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,2,3,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_23 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 23) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 23 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,2,4,5] (vacuumOrder j k) slot).det) = (c 2 : ℂ)-c 3*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_24 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 24) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 24 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,2,4,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_25 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 25) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 25 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,2,5,6] (vacuumOrder j k) slot).det) = (c 2 : ℂ)-c 3*Complex.I
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_26 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 26) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 26 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,3,4,5] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_27 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 27) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 27 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,3,4,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_28 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 28) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 28 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,3,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_29 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 29) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 29 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![1,4,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

private theorem numeric_orbit_30 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 30) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 30 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![2,3,4,5] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_31 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 31) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 31 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![2,3,4,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_32 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 32) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 32 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![2,3,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_33 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 33) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 33 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![2,4,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_34 (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder 34) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h 34 := by
  change (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
    (numericSlot (fullMatrix c w h) ![3,4,5,6] (vacuumOrder j k) slot).det) = 0
  simp only [Fin.sum_univ_succ]
  simp_rw [det_four,Matrix.det_fin_three]
  simp only [Fin.sum_univ_succ,Matrix.submatrix_apply]
  norm_num [numericSlot,vacuumOrder,fullMatrix,Fin.ext_iff,
    Fin.succ,Fin.succAbove,Fin.lt_def,Fin.castSucc,Fin.castAdd,Fin.castLE,
    Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem numeric_orbit_all (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) (i : Fin 35) :
    (∑ j : Fin 2, ∑ k : Fin 2, ∑ slot : Fin 4,
      (numericSlot (fullMatrix c w h) (lexOrder i) (vacuumOrder j k) slot).det) =
        sourceOrbit35 c w h i := by
  fin_cases i
  · exact numeric_orbit_0 c w h
  · exact numeric_orbit_1 c w h
  · exact numeric_orbit_2 c w h
  · exact numeric_orbit_3 c w h
  · exact numeric_orbit_4 c w h
  · exact numeric_orbit_5 c w h
  · exact numeric_orbit_6 c w h
  · exact numeric_orbit_7 c w h
  · exact numeric_orbit_8 c w h
  · exact numeric_orbit_9 c w h
  · exact numeric_orbit_10 c w h
  · exact numeric_orbit_11 c w h
  · exact numeric_orbit_12 c w h
  · exact numeric_orbit_13 c w h
  · exact numeric_orbit_14 c w h
  · exact numeric_orbit_15 c w h
  · exact numeric_orbit_16 c w h
  · exact numeric_orbit_17 c w h
  · exact numeric_orbit_18 c w h
  · exact numeric_orbit_19 c w h
  · exact numeric_orbit_20 c w h
  · exact numeric_orbit_21 c w h
  · exact numeric_orbit_22 c w h
  · exact numeric_orbit_23 c w h
  · exact numeric_orbit_24 c w h
  · exact numeric_orbit_25 c w h
  · exact numeric_orbit_26 c w h
  · exact numeric_orbit_27 c w h
  · exact numeric_orbit_28 c w h
  · exact numeric_orbit_29 c w h
  · exact numeric_orbit_30 c w h
  · exact numeric_orbit_31 c w h
  · exact numeric_orbit_32 c w h
  · exact numeric_orbit_33 c w h
  · exact numeric_orbit_34 c w h

theorem sourceOrbit_all (c : Fin 8 → ℝ) (w : Fin 3 → ℝ) (h : ℝ) (i : Fin 35) :
    orbit (nativeCoordinates.symm (c,w,h)) (lexIndex i)=sourceOrbit35 c w h i := by
  rw [orbit_coordinate,native_symm]
  simp_rw [native_slot_all]
  exact numeric_orbit_all c w h i


end LowEnergy.PreparationScalarCoordinates
