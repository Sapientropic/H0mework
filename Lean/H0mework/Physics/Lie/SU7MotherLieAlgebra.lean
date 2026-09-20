import H0mework.Physics.Lie.P286
import H0mework.Physics.Holonomic.AnholonomicSource
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The finite SU(7) mother Lie algebra and source-generated breaking operator

The mother carrier is one seven-dimensional special-unitary Lie matrix.  It
does not store color, weak, or hypercharge fields.  The P286-shaped block data
appears only as the codomain of a derived readout.

A proof-free source generates a traceless self-adjoint spectral order
parameter with multiplicities `3+2+1+1`.  Commutation with this operator alone
would leave two extra central `U(1)` directions.  The exact breaking predicate
therefore also imposes the infinitesimal volume normalizations on the color,
weak, and hyper-pair spectral blocks.  Those are operational trace equations,
not a stored P286 certificate or nominal breaking tag.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherLieAlgebra

open ProofFreeRicherAnholonomicSource
open GaugeProjection.ConcreteBlockDiagonal
open Matrix
open scoped ComplexConjugate

noncomputable section

/-- P286's concrete `3+2+1+1` carrier, used as a seven-element SU(7) index. -/
abbrev SU7MotherIndex := SMBlockIndex

theorem su7MotherIndex_card : Fintype.card SU7MotherIndex = 7 := by
  norm_num [SU7MotherIndex, SMBlockIndex]

/-- Real special-unitary Lie matrices: skew-adjoint complex matrices with
zero complex trace. -/
def specialUnitaryLieSubmodule (n : Type*) [Fintype n] [DecidableEq n] :
    Submodule ℝ (Matrix n n ℂ) where
  carrier := { matrix | star matrix = -matrix ∧ Matrix.trace matrix = 0 }
  zero_mem' := by simp
  add_mem' := by
    rintro first second ⟨hfirstStar, hfirstTrace⟩
      ⟨hsecondStar, hsecondTrace⟩
    constructor
    · rw [star_add, hfirstStar, hsecondStar]
      abel
    · simp [Matrix.trace_add, hfirstTrace, hsecondTrace]
  smul_mem' := by
    intro scalar matrix hmatrix
    constructor
    · have hstar : star (scalar • matrix) = scalar • star matrix := by
        ext row column
        simp [star_eq_conjTranspose]
      rw [hstar, hmatrix.1]
      simp
    · simp [Matrix.trace_smul, hmatrix.2]

abbrev SpecialUnitaryLieMatrix (n : Type*) [Fintype n] [DecidableEq n] :=
  specialUnitaryLieSubmodule n

abbrev SU7MotherLieMatrix := SpecialUnitaryLieMatrix SU7MotherIndex
abbrev SU3BlockLieMatrix := SpecialUnitaryLieMatrix (Fin 3)
abbrev SU2BlockLieMatrix := SpecialUnitaryLieMatrix (Fin 2)
abbrev HyperchargeLieScalar := skewAdjoint ℂ

@[simp] theorem specialUnitaryLieMatrix_star
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    star (matrix : Matrix n n ℂ) = -(matrix : Matrix n n ℂ) :=
  matrix.property.1

@[simp] theorem specialUnitaryLieMatrix_trace
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    Matrix.trace (matrix : Matrix n n ℂ) = 0 :=
  matrix.property.2

/-- The infinitesimal P286 block target.  It is a derived readout type, not
the storage type of the mother connection. -/
abbrev P286LieBlockData :=
  SU3BlockLieMatrix × SU2BlockLieMatrix × HyperchargeLieScalar

def scalarLieBlock (value : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => value

def hyperchargeLieBlock (value : HyperchargeLieScalar) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (scalarLieBlock value) 0 0 (scalarLieBlock (-value))

def weakHyperchargeLieBlock
    (weak : SU2BlockLieMatrix) (hypercharge : HyperchargeLieScalar) :
    Matrix (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))
      (Fin 2 ⊕ (Fin 1 ⊕ Fin 1)) ℂ :=
  Matrix.fromBlocks weak 0 0 (hyperchargeLieBlock hypercharge)

/-- The tangent-level `diag(C,W,y,-y)` pattern on P286's exact block carrier.
-/
def rawP286LieBlock (data : P286LieBlockData) :
    Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  Matrix.fromBlocks data.1 0 0
    (weakHyperchargeLieBlock data.2.1 data.2.2)

private theorem trace_fromBlocks_zero
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (first : Matrix m m ℂ) (second : Matrix n n ℂ) :
    Matrix.trace (Matrix.fromBlocks first 0 0 second) =
      Matrix.trace first + Matrix.trace second := by
  simp [Matrix.trace]

theorem rawP286LieBlock_star (data : P286LieBlockData) :
    star (rawP286LieBlock data) = -rawP286LieBlock data := by
  rw [star_eq_conjTranspose, rawP286LieBlock,
    Matrix.fromBlocks_conjTranspose, weakHyperchargeLieBlock,
    Matrix.fromBlocks_conjTranspose, hyperchargeLieBlock,
    Matrix.fromBlocks_conjTranspose]
  ext index row
  rcases index with colorIndex | restIndex
  · rcases row with colorRow | restRow
    · simpa [star_eq_conjTranspose] using congrArg
        (fun matrix : Matrix (Fin 3) (Fin 3) ℂ =>
          matrix colorIndex colorRow)
        (specialUnitaryLieMatrix_star data.1)
    · simp
  · rcases restIndex with weakIndex | hyperIndex
    · rcases row with colorRow | restRow
      · simp
      · rcases restRow with weakRow | hyperRow
        · simpa [star_eq_conjTranspose] using congrArg
            (fun matrix : Matrix (Fin 2) (Fin 2) ℂ =>
              matrix weakIndex weakRow)
            (specialUnitaryLieMatrix_star data.2.1)
        · simp
    · rcases row with colorRow | restRow
      · simp
      · rcases restRow with weakRow | hyperRow
        · simp
        · rcases hyperIndex with plusIndex | minusIndex
          · rcases hyperRow with plusRow | minusRow
            · fin_cases plusIndex
              fin_cases plusRow
              simp [scalarLieBlock]
            · fin_cases plusIndex
              fin_cases minusRow
              simp [scalarLieBlock]
          · rcases hyperRow with plusRow | minusRow
            · fin_cases minusIndex
              fin_cases plusRow
              simp [scalarLieBlock]
            · fin_cases minusIndex
              fin_cases minusRow
              simp [scalarLieBlock]

theorem rawP286LieBlock_trace (data : P286LieBlockData) :
    Matrix.trace (rawP286LieBlock data) = 0 := by
  rw [rawP286LieBlock, trace_fromBlocks_zero,
    weakHyperchargeLieBlock, trace_fromBlocks_zero,
    hyperchargeLieBlock, trace_fromBlocks_zero]
  simp [scalarLieBlock]

/-- Lie-block inclusion into the single SU(7) mother carrier. -/
def p286LieBlockEmbed (data : P286LieBlockData) : SU7MotherLieMatrix :=
  ⟨rawP286LieBlock data,
    rawP286LieBlock_star data, rawP286LieBlock_trace data⟩

def colorBlockOfMother (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun row column => matrix (Sum.inl row) (Sum.inl column)

def weakBlockOfMother (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun row column => matrix (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inl column))

def hyperPlusIndex : SU7MotherIndex :=
  Sum.inr (Sum.inr (Sum.inl 0))

def hyperMinusIndex : SU7MotherIndex :=
  Sum.inr (Sum.inr (Sum.inr 0))

def hyperPlusOfMother (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) : ℂ :=
  matrix hyperPlusIndex hyperPlusIndex

def hyperMinusOfMother (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) : ℂ :=
  matrix hyperMinusIndex hyperMinusIndex

/-- Four distinct source-scaled spectral levels with multiplicities
`3+2+1+1`; the weighted trace is `-3+0+1+2=0`. -/
def breakingLevel : SU7MotherIndex → ℝ
  | Sum.inl _ => -1
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 2

/-- The actual source-generated adjoint order parameter. -/
def sourceBreakingOrderParameter (source : Source) :
    Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  Matrix.diagonal fun index => (source.sigma * breakingLevel index : ℝ)

theorem sourceBreakingOrderParameter_trace_zero (source : Source) :
    Matrix.trace (sourceBreakingOrderParameter source) = 0 := by
  simp [sourceBreakingOrderParameter, Matrix.trace, breakingLevel]
  ring

theorem sourceBreakingOrderParameter_selfAdjoint (source : Source) :
    star (sourceBreakingOrderParameter source) =
      sourceBreakingOrderParameter source := by
  unfold sourceBreakingOrderParameter
  rw [star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext index
  simp

private theorem mul_diagonal_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : Matrix n n ℂ) (diagonalValue : n → ℂ)
    (row column : n) :
    (matrix * Matrix.diagonal diagonalValue) row column =
      matrix row column * diagonalValue column := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

private theorem diagonal_mul_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : Matrix n n ℂ) (diagonalValue : n → ℂ)
    (row column : n) :
    (Matrix.diagonal diagonalValue * matrix) row column =
      diagonalValue row * matrix row column := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- Actual breaking data contains only the generated order operator.  It does
not store P286 or P523 receipts. -/
structure SU7SourceBreakingDatum where
  orderParameter : Matrix SU7MotherIndex SU7MotherIndex ℂ

def sourceBreakingDatum (source : Source) : SU7SourceBreakingDatum where
  orderParameter := sourceBreakingOrderParameter source

/-- Operational selection of the exact infinitesimal P286 image.  Commutation
selects the spectral blocks; the three trace equations remove the two extra
central directions left by the raw centralizer. -/
def SelectedBySourceBreaking
    (source : Source) (matrix : SU7MotherLieMatrix) : Prop :=
  (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
      (sourceBreakingDatum source).orderParameter =
    (sourceBreakingDatum source).orderParameter * matrix ∧
  Matrix.trace (colorBlockOfMother matrix) = 0 ∧
  Matrix.trace (weakBlockOfMother matrix) = 0 ∧
  hyperPlusOfMother matrix + hyperMinusOfMother matrix = 0

theorem p286LieBlockEmbed_selected
    (source : Source) (data : P286LieBlockData) :
    SelectedBySourceBreaking source (p286LieBlockEmbed data) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change
      (p286LieBlockEmbed data : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          sourceBreakingOrderParameter source =
        sourceBreakingOrderParameter source *
          (p286LieBlockEmbed data : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    unfold sourceBreakingOrderParameter
    ext row column
    rw [mul_diagonal_apply, diagonal_mul_apply]
    rcases row with colorRow | restRow
    · rcases column with colorColumn | restColumn
      · simp [p286LieBlockEmbed, rawP286LieBlock,
          breakingLevel]
        ring
      · rcases restColumn with weakColumn | hyperColumn <;>
          simp [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock,
            breakingLevel]
    · rcases restRow with weakRow | hyperRow
      · rcases column with colorColumn | restColumn
        · simp [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock,
            breakingLevel]
        · rcases restColumn with weakColumn | hyperColumn <;>
            simp [p286LieBlockEmbed, rawP286LieBlock,
              weakHyperchargeLieBlock, hyperchargeLieBlock,
              breakingLevel]
      · rcases column with colorColumn | restColumn
        · simp [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock,
            breakingLevel]
        · rcases restColumn with weakColumn | hyperColumn
          · simp [p286LieBlockEmbed, rawP286LieBlock,
              weakHyperchargeLieBlock, hyperchargeLieBlock,
              breakingLevel]
          · rcases hyperRow with plusRow | minusRow
            · rcases hyperColumn with plusColumn | minusColumn
              · fin_cases plusRow
                fin_cases plusColumn
                simp [p286LieBlockEmbed, rawP286LieBlock,
                  weakHyperchargeLieBlock, hyperchargeLieBlock,
                  scalarLieBlock, breakingLevel]
                ring
              · fin_cases plusRow
                fin_cases minusColumn
                simp [p286LieBlockEmbed, rawP286LieBlock,
                  weakHyperchargeLieBlock, hyperchargeLieBlock,
                  scalarLieBlock, breakingLevel]
            · rcases hyperColumn with plusColumn | minusColumn
              · fin_cases minusRow
                fin_cases plusColumn
                simp [p286LieBlockEmbed, rawP286LieBlock,
                  weakHyperchargeLieBlock, hyperchargeLieBlock,
                  scalarLieBlock, breakingLevel]
              · fin_cases minusRow
                fin_cases minusColumn
                simp [p286LieBlockEmbed, rawP286LieBlock,
                  weakHyperchargeLieBlock, hyperchargeLieBlock,
                  scalarLieBlock, breakingLevel]
                ring
  · exact specialUnitaryLieMatrix_trace data.1
  · exact specialUnitaryLieMatrix_trace data.2.1
  · simp [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperPlusOfMother,
      hyperMinusOfMother, hyperPlusIndex, hyperMinusIndex]

/-- Distinct source-generated spectral levels force every cross-block matrix
entry to vanish.  Positivity of the source scale is essential here: a zero
scale would make the order operator unable to select any block structure. -/
theorem selected_entry_zero_of_breakingLevel_ne
    (source : Source) (matrix : SU7MotherLieMatrix)
    (selected : SelectedBySourceBreaking source matrix)
    (row column : SU7MotherIndex)
    (levels_ne : breakingLevel row ≠ breakingLevel column) :
    (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column = 0 := by
  have commutation :
      (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          Matrix.diagonal (fun index =>
            ((source.sigma * breakingLevel index : ℝ) : ℂ)) =
        Matrix.diagonal (fun index =>
            ((source.sigma * breakingLevel index : ℝ) : ℂ)) *
          (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
    simpa [sourceBreakingDatum, sourceBreakingOrderParameter] using selected.1
  have entryEquation := congrArg
    (fun value : Matrix SU7MotherIndex SU7MotherIndex ℂ => value row column)
    commutation
  rw [mul_diagonal_apply, diagonal_mul_apply] at entryEquation
  have spectral_ne :
      ((source.sigma * breakingLevel column : ℝ) : ℂ) ≠
        ((source.sigma * breakingLevel row : ℝ) : ℂ) := by
    intro spectral_eq
    have real_eq :
        source.sigma * breakingLevel column =
          source.sigma * breakingLevel row := by
      exact_mod_cast spectral_eq
    apply levels_ne
    exact (mul_left_cancel₀ (ne_of_gt source.sigma_pos)) real_eq.symm
  by_contra entry_ne
  apply spectral_ne
  apply mul_left_cancel₀ entry_ne
  calc
    (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column *
          ((source.sigma * breakingLevel column : ℝ) : ℂ) =
        ((source.sigma * breakingLevel row : ℝ) : ℂ) *
          (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column :=
      entryEquation
    _ = (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column *
          ((source.sigma * breakingLevel row : ℝ) : ℂ) := by
      ring

/-- The color block is read from the mother matrix and proved special-unitary
from the mother skew-adjoint law plus the operational color trace equation. -/
def selectedColorReadout
    (matrix : SU7MotherLieMatrix)
    (colorTrace : Matrix.trace (colorBlockOfMother matrix) = 0) :
    SU3BlockLieMatrix := by
  refine ⟨colorBlockOfMother matrix, ?_, colorTrace⟩
  ext row column
  simpa [star_eq_conjTranspose, colorBlockOfMother] using congrArg
    (fun value : Matrix SU7MotherIndex SU7MotherIndex ℂ =>
      value (Sum.inl row) (Sum.inl column))
    matrix.property.1

/-- The weak block is a derived readout, never a field stored alongside the
mother matrix. -/
def selectedWeakReadout
    (matrix : SU7MotherLieMatrix)
    (weakTrace : Matrix.trace (weakBlockOfMother matrix) = 0) :
    SU2BlockLieMatrix := by
  refine ⟨weakBlockOfMother matrix, ?_, weakTrace⟩
  ext row column
  simpa [star_eq_conjTranspose, weakBlockOfMother] using congrArg
    (fun value : Matrix SU7MotherIndex SU7MotherIndex ℂ =>
      value (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inl column)))
    matrix.property.1

/-- Hypercharge is read from the positive one-dimensional spectral block;
the mother skew-adjoint law supplies its Lie-algebra membership. -/
def selectedHyperchargeReadout
    (matrix : SU7MotherLieMatrix) : HyperchargeLieScalar := by
  refine ⟨hyperPlusOfMother matrix, ?_⟩
  change star (hyperPlusOfMother matrix) = -hyperPlusOfMother matrix
  simpa [star_eq_conjTranspose, hyperPlusOfMother, hyperPlusIndex] using
    congrArg
      (fun value : Matrix SU7MotherIndex SU7MotherIndex ℂ =>
        value hyperPlusIndex hyperPlusIndex)
      matrix.property.1

/-- The exact P286 tangent block datum reconstructed from an operationally
selected mother matrix. -/
def selectedP286LieBlockReadout
    (source : Source) (matrix : SU7MotherLieMatrix)
    (selected : SelectedBySourceBreaking source matrix) : P286LieBlockData :=
  (selectedColorReadout matrix selected.2.1,
    selectedWeakReadout matrix selected.2.2.1,
    selectedHyperchargeReadout matrix)

theorem p286LieBlockEmbed_selectedReadout
    (source : Source) (matrix : SU7MotherLieMatrix)
    (selected : SelectedBySourceBreaking source matrix) :
    p286LieBlockEmbed
        (selectedP286LieBlockReadout source matrix selected) = matrix := by
  apply Subtype.ext
  ext row column
  have offBlock := selected_entry_zero_of_breakingLevel_ne
    source matrix selected
  rcases row with colorRow | restRow
  · rcases column with colorColumn | restColumn
    · simp [p286LieBlockEmbed, rawP286LieBlock,
        selectedP286LieBlockReadout, selectedColorReadout,
        colorBlockOfMother]
    · rcases restColumn with weakColumn | hyperColumn
      · simpa [p286LieBlockEmbed, rawP286LieBlock,
          weakHyperchargeLieBlock] using
          (offBlock (Sum.inl colorRow) (Sum.inr (Sum.inl weakColumn))
            (by norm_num [breakingLevel])).symm
      · rcases hyperColumn with plusColumn | minusColumn
        · simpa [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock] using
            (offBlock (Sum.inl colorRow)
              (Sum.inr (Sum.inr (Sum.inl plusColumn)))
              (by norm_num [breakingLevel])).symm
        · simpa [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock] using
            (offBlock (Sum.inl colorRow)
              (Sum.inr (Sum.inr (Sum.inr minusColumn)))
              (by norm_num [breakingLevel])).symm
  · rcases restRow with weakRow | hyperRow
    · rcases column with colorColumn | restColumn
      · simpa [p286LieBlockEmbed, rawP286LieBlock,
          weakHyperchargeLieBlock] using
          (offBlock (Sum.inr (Sum.inl weakRow)) (Sum.inl colorColumn)
            (by norm_num [breakingLevel])).symm
      · rcases restColumn with weakColumn | hyperColumn
        · simp [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, selectedP286LieBlockReadout,
            selectedWeakReadout, weakBlockOfMother]
        · rcases hyperColumn with plusColumn | minusColumn
          · simpa [p286LieBlockEmbed, rawP286LieBlock,
              weakHyperchargeLieBlock, hyperchargeLieBlock] using
              (offBlock (Sum.inr (Sum.inl weakRow))
                (Sum.inr (Sum.inr (Sum.inl plusColumn)))
                (by norm_num [breakingLevel])).symm
          · simpa [p286LieBlockEmbed, rawP286LieBlock,
              weakHyperchargeLieBlock, hyperchargeLieBlock] using
              (offBlock (Sum.inr (Sum.inl weakRow))
                (Sum.inr (Sum.inr (Sum.inr minusColumn)))
                (by norm_num [breakingLevel])).symm
    · rcases hyperRow with plusRow | minusRow
      · rcases column with colorColumn | restColumn
        · simpa [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock] using
            (offBlock (Sum.inr (Sum.inr (Sum.inl plusRow)))
              (Sum.inl colorColumn) (by norm_num [breakingLevel])).symm
        · rcases restColumn with weakColumn | hyperColumn
          · simpa [p286LieBlockEmbed, rawP286LieBlock,
              weakHyperchargeLieBlock, hyperchargeLieBlock] using
              (offBlock (Sum.inr (Sum.inr (Sum.inl plusRow)))
                (Sum.inr (Sum.inl weakColumn))
                (by norm_num [breakingLevel])).symm
          · rcases hyperColumn with plusColumn | minusColumn
            · fin_cases plusRow
              fin_cases plusColumn
              simp [p286LieBlockEmbed, rawP286LieBlock,
                weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
                selectedP286LieBlockReadout,
                selectedHyperchargeReadout, hyperPlusOfMother,
                hyperPlusIndex]
            · simpa [p286LieBlockEmbed, rawP286LieBlock,
                weakHyperchargeLieBlock, hyperchargeLieBlock,
                scalarLieBlock] using
                (offBlock (Sum.inr (Sum.inr (Sum.inl plusRow)))
                  (Sum.inr (Sum.inr (Sum.inr minusColumn)))
                  (by norm_num [breakingLevel])).symm
      · rcases column with colorColumn | restColumn
        · simpa [p286LieBlockEmbed, rawP286LieBlock,
            weakHyperchargeLieBlock, hyperchargeLieBlock] using
            (offBlock (Sum.inr (Sum.inr (Sum.inr minusRow)))
              (Sum.inl colorColumn) (by norm_num [breakingLevel])).symm
        · rcases restColumn with weakColumn | hyperColumn
          · simpa [p286LieBlockEmbed, rawP286LieBlock,
              weakHyperchargeLieBlock, hyperchargeLieBlock] using
              (offBlock (Sum.inr (Sum.inr (Sum.inr minusRow)))
                (Sum.inr (Sum.inl weakColumn))
                (by norm_num [breakingLevel])).symm
          · rcases hyperColumn with plusColumn | minusColumn
            · simpa [p286LieBlockEmbed, rawP286LieBlock,
                weakHyperchargeLieBlock, hyperchargeLieBlock,
                scalarLieBlock] using
                (offBlock (Sum.inr (Sum.inr (Sum.inr minusRow)))
                  (Sum.inr (Sum.inr (Sum.inl plusColumn)))
                  (by norm_num [breakingLevel])).symm
            · fin_cases minusRow
              fin_cases minusColumn
              have hyperTrace := selected.2.2.2
              have reordered :
                  hyperMinusOfMother matrix + hyperPlusOfMother matrix = 0 := by
                simpa [add_comm] using hyperTrace
              have hyperEquation :
                  -hyperPlusOfMother matrix = hyperMinusOfMother matrix :=
                neg_eq_of_add_eq_zero_left reordered
              simpa [p286LieBlockEmbed, rawP286LieBlock,
                weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
                selectedP286LieBlockReadout,
                selectedHyperchargeReadout, hyperPlusOfMother,
                hyperMinusOfMother, hyperPlusIndex, hyperMinusIndex] using
                hyperEquation

/-- The operational source-breaking predicate is exactly the image of the
P286 tangent block embedding.  This is the Stage 6A anti-tagging theorem: the
block chain is selected by equations, not asserted by a stored certificate. -/
theorem selectedBySourceBreaking_iff_p286LieBlockImage
    (source : Source) (matrix : SU7MotherLieMatrix) :
    SelectedBySourceBreaking source matrix ↔
      ∃ data : P286LieBlockData, p286LieBlockEmbed data = matrix := by
  constructor
  · intro selected
    exact ⟨selectedP286LieBlockReadout source matrix selected,
      p286LieBlockEmbed_selectedReadout source matrix selected⟩
  · rintro ⟨data, rfl⟩
    exact p286LieBlockEmbed_selected source data

end
end SaturationMonoid.PhysicsCore.SU7MotherLieAlgebra
