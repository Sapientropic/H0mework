import H0mework.NavierStokes.Accumulation.ConcreteTwoScaleLiftSource

set_option autoImplicit false

open scoped BigOperators Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

/-! ## Executable Gaussian-rational rows -/

/-- A Gaussian rational kept separate from `Complex` so finite Fourier
evaluation reduces entirely in `ℚ`. -/
@[ext]
structure GaussianRat where
  re : ℚ
  im : ℚ
deriving DecidableEq, Repr

namespace GaussianRat

def zero : GaussianRat := ⟨0, 0⟩

def add (left right : GaussianRat) : GaussianRat :=
  ⟨left.re + right.re, left.im + right.im⟩

def neg (value : GaussianRat) : GaussianRat :=
  ⟨-value.re, -value.im⟩

def sub (left right : GaussianRat) : GaussianRat :=
  add left (neg right)

def mul (left right : GaussianRat) : GaussianRat :=
  ⟨left.re * right.re - left.im * right.im,
    left.re * right.im + left.im * right.re⟩

def ratScale (scalar : ℚ) (value : GaussianRat) : GaussianRat :=
  ⟨scalar * value.re, scalar * value.im⟩

def intScale (scalar : ℤ) (value : GaussianRat) : GaussianRat :=
  ratScale (scalar : ℚ) value

def ratDiv (value : GaussianRat) (denominator : ℚ) : GaussianRat :=
  ratScale denominator⁻¹ value

def toComplex (value : GaussianRat) : Complex :=
  (value.re : ℝ) + (value.im : ℝ) * Complex.I

instance instZeroGaussianRat : Zero GaussianRat := ⟨zero⟩

instance instAddGaussianRat : Add GaussianRat := ⟨add⟩

instance : AddCommMonoid GaussianRat where
  add_assoc := by
    intro left middle right
    ext <;> exact add_assoc _ _ _
  zero_add := by
    intro value
    ext <;> exact zero_add _
  add_zero := by
    intro value
    ext <;> exact add_zero _
  add_comm := by
    intro left right
    ext <;> exact add_comm _ _
  nsmul := nsmulRec
  nsmul_zero := by intro value; rfl
  nsmul_succ := by intro n value; rfl

@[simp] theorem zero_re : (0 : GaussianRat).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussianRat).im = 0 := rfl
@[simp] theorem add_re (left right : GaussianRat) :
    (left + right).re = left.re + right.re := rfl
@[simp] theorem add_im (left right : GaussianRat) :
    (left + right).im = left.im + right.im := rfl

@[simp] theorem toComplex_zero : toComplex zero = 0 := by
  simp [toComplex, zero]

@[simp] theorem toComplex_add (left right : GaussianRat) :
    toComplex (add left right) = toComplex left + toComplex right := by
  apply Complex.ext <;>
    simp [toComplex, add, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem toComplex_neg (value : GaussianRat) :
    toComplex (neg value) = -toComplex value := by
  apply Complex.ext <;>
    simp [toComplex, neg, Complex.mul_re, Complex.mul_im]

@[simp] theorem toComplex_sub (left right : GaussianRat) :
    toComplex (sub left right) = toComplex left - toComplex right := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem toComplex_mul (left right : GaussianRat) :
    toComplex (mul left right) = toComplex left * toComplex right := by
  apply Complex.ext <;>
    simp [toComplex, mul, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem toComplex_ratScale (scalar : ℚ) (value : GaussianRat) :
    toComplex (ratScale scalar value) =
      ((scalar : ℝ) : ℂ) * toComplex value := by
  apply Complex.ext <;>
    simp [toComplex, ratScale, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem toComplex_intScale (scalar : ℤ) (value : GaussianRat) :
    toComplex (intScale scalar value) =
      ((scalar : ℝ) : ℂ) * toComplex value := by
  simp [intScale]

@[simp] theorem toComplex_ratDiv
    (value : GaussianRat) (denominator : ℚ) :
    toComplex (ratDiv value denominator) =
      (((denominator : ℝ)⁻¹ : ℝ) : ℂ) * toComplex value := by
  simp [ratDiv, Rat.cast_inv]

end GaussianRat

abbrev GaussianRatVector := Fin 3 → GaussianRat

namespace GaussianRatVector

def zero : GaussianRatVector := fun _ => GaussianRat.zero

def add (left right : GaussianRatVector) : GaussianRatVector :=
  fun coordinate => GaussianRat.add (left coordinate) (right coordinate)

def sub (left right : GaussianRatVector) : GaussianRatVector :=
  fun coordinate => GaussianRat.sub (left coordinate) (right coordinate)

def complexScale
    (scalar : GaussianRat) (vector : GaussianRatVector) :
    GaussianRatVector :=
  fun coordinate => GaussianRat.mul scalar (vector coordinate)

def ratScale (scalar : ℚ) (vector : GaussianRatVector) :
    GaussianRatVector :=
  fun coordinate => GaussianRat.ratScale scalar (vector coordinate)

def toComplex (vector : GaussianRatVector) : ComplexCoordinateVector :=
  fun coordinate => GaussianRat.toComplex (vector coordinate)

def waveDot
    (wave : IntegerWavevector) (vector : GaussianRatVector) : GaussianRat :=
  GaussianRat.add
    (GaussianRat.intScale (wave 0) (vector 0))
    (GaussianRat.add
      (GaussianRat.intScale (wave 1) (vector 1))
      (GaussianRat.intScale (wave 2) (vector 2)))

def waveCross
    (wave : IntegerWavevector) (vector : GaussianRatVector) :
    GaussianRatVector :=
  ![GaussianRat.sub
      (GaussianRat.intScale (wave 1) (vector 2))
      (GaussianRat.intScale (wave 2) (vector 1)),
    GaussianRat.sub
      (GaussianRat.intScale (wave 2) (vector 0))
      (GaussianRat.intScale (wave 0) (vector 2)),
    GaussianRat.sub
      (GaussianRat.intScale (wave 0) (vector 1))
      (GaussianRat.intScale (wave 1) (vector 0))]

def tripleWaveCrossDot
    (left right : IntegerWavevector)
    (vector : GaussianRatVector) : GaussianRat :=
  waveDot left (waveCross right vector)

@[simp] theorem toComplex_zero : toComplex zero = 0 := by
  funext coordinate
  fin_cases coordinate <;> simp [toComplex, zero]

@[simp] theorem toComplex_zero_instance :
    toComplex (0 : GaussianRatVector) = 0 := by
  funext coordinate
  change GaussianRat.toComplex GaussianRat.zero = 0
  exact GaussianRat.toComplex_zero

@[simp] theorem toComplex_add
    (left right : GaussianRatVector) :
    toComplex (add left right) = toComplex left + toComplex right := by
  funext coordinate
  simp [toComplex, add]

@[simp] theorem toComplex_add_instance
    (left right : GaussianRatVector) :
    toComplex (left + right) = toComplex left + toComplex right := by
  exact toComplex_add left right

@[simp] theorem toComplex_sub
    (left right : GaussianRatVector) :
    toComplex (sub left right) = toComplex left - toComplex right := by
  funext coordinate
  simp [toComplex, sub]

@[simp] theorem toComplex_complexScale
    (scalar : GaussianRat) (vector : GaussianRatVector) :
    toComplex (complexScale scalar vector) =
      GaussianRat.toComplex scalar • toComplex vector := by
  funext coordinate
  simp [toComplex, complexScale, smul_eq_mul]

@[simp] theorem toComplex_ratScale
    (scalar : ℚ) (vector : GaussianRatVector) :
    toComplex (ratScale scalar vector) =
      (((scalar : ℝ) : ℂ)) • toComplex vector := by
  funext coordinate
  simp [toComplex, ratScale, smul_eq_mul]

theorem toComplex_waveDot
    (wave : IntegerWavevector) (vector : GaussianRatVector) :
    GaussianRat.toComplex (waveDot wave vector) =
      complexWavevector wave ⬝ᵥ toComplex vector := by
  simp [waveDot, dotProduct, Fin.sum_univ_succ, toComplex,
    complexWavevector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

theorem toComplex_waveCross
    (wave : IntegerWavevector) (vector : GaussianRatVector) :
    toComplex (waveCross wave vector) =
      complexWavevector wave ⨯₃ toComplex vector := by
  funext coordinate
  fin_cases coordinate <;>
    simp [toComplex, waveCross, complexWavevector, cross_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem toComplex_tripleWaveCrossDot
    (left right : IntegerWavevector) (vector : GaussianRatVector) :
    GaussianRat.toComplex (tripleWaveCrossDot left right vector) =
      complexWavevector left ⬝ᵥ
        (complexWavevector right ⨯₃ toComplex vector) := by
  rw [tripleWaveCrossDot, toComplex_waveDot, toComplex_waveCross]

end GaussianRatVector

def rationalIntegerWaveNormSq (wave : IntegerWavevector) : ℚ :=
  (wave 0 : ℚ) ^ 2 + (wave 1 : ℚ) ^ 2 + (wave 2 : ℚ) ^ 2

theorem rationalIntegerWaveNormSq_cast (wave : IntegerWavevector) :
    (rationalIntegerWaveNormSq wave : ℝ) = integerWaveNormSq wave := by
  simp [rationalIntegerWaveNormSq, integerWaveNormSq,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  ring

/-! ## The π-free pair evaluator and its physical interpretation -/

/-- Exact ordered interaction after the Fourier `2π` in the derivative has
cancelled the `2π` in Biot--Savart. -/
def rationalVorticityPairContribution
    (first second : IntegerWavevector)
    (firstRow secondRow : GaussianRatVector) : GaussianRatVector :=
  GaussianRatVector.add
    (GaussianRatVector.complexScale
      (GaussianRat.ratDiv
        (GaussianRat.neg
          (GaussianRatVector.waveDot second firstRow))
        (rationalIntegerWaveNormSq second))
      (GaussianRatVector.waveCross second secondRow))
    (GaussianRatVector.complexScale
      (GaussianRat.ratDiv
        (GaussianRatVector.tripleWaveCrossDot second first firstRow)
        (rationalIntegerWaveNormSq first))
      secondRow)

/-! ## Exact integer dilation of one physical pair -/

/-- Integer Fourier dilation.  Vorticity rows use the corresponding
parabolic amplitude factor in the theorem below. -/
def integerWavevectorScale
    (scale : ℤ) (wave : IntegerWavevector) : IntegerWavevector :=
  fun coordinate => scale * wave coordinate

@[simp] theorem integerWavevectorScale_apply
    (scale : ℤ) (wave : IntegerWavevector) (coordinate : Fin 3) :
    integerWavevectorScale scale wave coordinate = scale * wave coordinate :=
  rfl

theorem rationalIntegerWaveNormSq_integerWavevectorScale
    (scale : ℤ) (wave : IntegerWavevector) :
    rationalIntegerWaveNormSq (integerWavevectorScale scale wave) =
      (scale : ℚ) ^ 2 * rationalIntegerWaveNormSq wave := by
  unfold rationalIntegerWaveNormSq integerWavevectorScale
  push_cast
  ring

/-- Full ordered-pair incidence is parabolically homogeneous: spatial
frequency dilation by `scale` and vorticity-amplitude dilation by `scale²`
produce exactly `scale⁴` times the original row. -/
theorem rationalVorticityPairContribution_integerWavevectorScale
    (scale : ℤ)
    (scaleNe : scale ≠ 0)
    (first second : IntegerWavevector)
    (firstRow secondRow : GaussianRatVector) :
    rationalVorticityPairContribution
        (integerWavevectorScale scale first)
        (integerWavevectorScale scale second)
        (GaussianRatVector.ratScale ((scale : ℚ) ^ 2) firstRow)
        (GaussianRatVector.ratScale ((scale : ℚ) ^ 2) secondRow) =
      GaussianRatVector.ratScale ((scale : ℚ) ^ 4)
        (rationalVorticityPairContribution
          first second firstRow secondRow) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [rationalVorticityPairContribution,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.ratScale, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, rationalIntegerWaveNormSq,
      integerWavevectorScale,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [scaleNe] <;>
    simp

/-- Pair-level commuting square.  This is the only analytic normalization
lemma needed by the executable rational convolution. -/
theorem rationalVorticityPairContribution_toComplex
    (leftState rightState : ComplexVorticityHilbertState)
    (first second : IntegerWavevector)
    (firstRow secondRow : GaussianRatVector)
    (firstNonzero : first ≠ 0)
    (secondNonzero : second ≠ 0)
    (firstFaithful :
      GaussianRatVector.toComplex firstRow = leftState first)
    (secondFaithful :
      GaussianRatVector.toComplex secondRow = rightState second) :
    GaussianRatVector.toComplex
        (rationalVorticityPairContribution
          first second firstRow secondRow) =
      finiteStateVorticityBilinearPairContribution
        leftState rightState (first, second) := by
  rw [rationalVorticityPairContribution,
    GaussianRatVector.toComplex_add,
    GaussianRatVector.toComplex_complexScale,
    GaussianRatVector.toComplex_complexScale,
    GaussianRat.toComplex_ratDiv,
    GaussianRat.toComplex_ratDiv,
    GaussianRat.toComplex_neg,
    GaussianRatVector.toComplex_waveDot,
    GaussianRatVector.toComplex_waveCross,
    GaussianRatVector.toComplex_tripleWaveCrossDot,
    firstFaithful, secondFaithful]
  unfold finiteStateVorticityBilinearPairContribution
    finiteStateVelocityCoefficient biotSavartVelocityCoefficient
  rw [if_neg secondNonzero, if_neg firstNonzero]
  rw [← rationalIntegerWaveNormSq_cast first,
    ← rationalIntegerWaveNormSq_cast second]
  have firstNormNonzero : rationalIntegerWaveNormSq first ≠ 0 := by
    intro normZero
    apply integerWaveNormSq_ne_zero firstNonzero
    rw [← rationalIntegerWaveNormSq_cast first, normZero]
    norm_num
  have secondNormNonzero : rationalIntegerWaveNormSq second ≠ 0 := by
    intro normZero
    apply integerWaveNormSq_ne_zero secondNonzero
    rw [← rationalIntegerWaveNormSq_cast second, normZero]
    norm_num
  have firstNormCastNonzero :
      (rationalIntegerWaveNormSq first : ℝ) ≠ 0 := by exact_mod_cast firstNormNonzero
  have secondNormCastNonzero :
      (rationalIntegerWaveNormSq second : ℝ) ≠ 0 := by exact_mod_cast secondNormNonzero
  have piNonzero : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  funext coordinate
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    dotProduct_smul, smul_smul, smul_eq_mul]
  push_cast
  field_simp [firstNormCastNonzero, secondNormCastNonzero,
    Real.pi_ne_zero, piNonzero]
  all_goals simp [Complex.I_sq] <;> ring

theorem rationalVorticityPairContribution_toComplex_self
    (state : ComplexVorticityHilbertState)
    (first second : IntegerWavevector)
    (firstRow secondRow : GaussianRatVector)
    (firstNonzero : first ≠ 0)
    (secondNonzero : second ≠ 0)
    (firstFaithful : GaussianRatVector.toComplex firstRow = state first)
    (secondFaithful : GaussianRatVector.toComplex secondRow = state second) :
    GaussianRatVector.toComplex
        (rationalVorticityPairContribution
          first second firstRow secondRow) =
      finiteStateVorticityNonlinearPairContribution state (first, second) := by
  simpa only [finiteStateVorticityBilinearPairContribution,
    finiteStateVorticityNonlinearPairContribution] using
    rationalVorticityPairContribution_toComplex
      state state first second firstRow secondRow
      firstNonzero secondNonzero firstFaithful secondFaithful

/-! ## Finite convolution and generator commuting -/

abbrev GaussianRatState := IntegerWavevector → GaussianRatVector

def rationalVorticityBilinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (left right : GaussianRatState)
    (output : IntegerWavevector) : GaussianRatVector :=
  ∑ first ∈ modes,
    ∑ second ∈ modes,
      if first + second = output then
        rationalVorticityPairContribution
          first second (left first) (right second)
      else 0

@[simp] theorem rationalVorticityPairContribution_zero_right
    (first second : IntegerWavevector)
    (firstRow : GaussianRatVector) :
    rationalVorticityPairContribution first second firstRow 0 = 0 := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [rationalVorticityPairContribution,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveCross,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.mul, GaussianRat.ratScale,
      GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

@[simp] theorem rationalVorticityPairContribution_zero_left
    (first second : IntegerWavevector)
    (secondRow : GaussianRatVector) :
    rationalVorticityPairContribution first second 0 secondRow = 0 := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [rationalVorticityPairContribution,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.mul, GaussianRat.ratScale,
      GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- If the right input is supported on a source inventory, the complete
finite bilinear row is the single incidence sum over that source. -/
theorem rationalVorticityBilinearCoefficientAt_eq_source_right
    (sourceModes actionModes : Finset IntegerWavevector)
    (sourceSubset : sourceModes ⊆ actionModes)
    (left right : GaussianRatState)
    (rightSupported : ∀ wave, wave ∉ sourceModes → right wave = 0)
    (output : IntegerWavevector) :
    rationalVorticityBilinearCoefficientAt
        actionModes left right output =
      ∑ sourceWave ∈ sourceModes,
        if output - sourceWave ∈ actionModes then
          rationalVorticityPairContribution
            (output - sourceWave) sourceWave
            (left (output - sourceWave)) (right sourceWave)
        else 0 := by
  classical
  unfold rationalVorticityBilinearCoefficientAt
  rw [Finset.sum_comm]
  have restrictSource :
      (∑ sourceWave ∈ actionModes,
          ∑ first ∈ actionModes,
            if first + sourceWave = output then
              rationalVorticityPairContribution
                first sourceWave (left first) (right sourceWave)
            else 0) =
        ∑ sourceWave ∈ sourceModes,
          ∑ first ∈ actionModes,
            if first + sourceWave = output then
              rationalVorticityPairContribution
                first sourceWave (left first) (right sourceWave)
            else 0 := by
    symm
    apply Finset.sum_subset_zero_on_sdiff sourceSubset
    · intro sourceWave sourceDifference
      have sourceNotMem := (Finset.mem_sdiff.mp sourceDifference).2
      apply Finset.sum_eq_zero
      intro first firstMem
      by_cases incidence : first + sourceWave = output
      · rw [if_pos incidence, rightSupported sourceWave sourceNotMem]
        exact rationalVorticityPairContribution_zero_right
          first sourceWave (left first)
      · simp [incidence]
    · intro sourceWave sourceMem
      rfl
  rw [restrictSource]
  apply Finset.sum_congr rfl
  intro sourceWave sourceMem
  have incidence : ∀ first : IntegerWavevector,
      first + sourceWave = output ↔ first = output - sourceWave := by
    intro first
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [incidence]
  by_cases firstMem : output - sourceWave ∈ actionModes
  · simp [firstMem]
  · simp [firstMem]

/-- Left-supported counterpart of
`rationalVorticityBilinearCoefficientAt_eq_source_right`. -/
theorem rationalVorticityBilinearCoefficientAt_eq_source_left
    (sourceModes actionModes : Finset IntegerWavevector)
    (sourceSubset : sourceModes ⊆ actionModes)
    (left right : GaussianRatState)
    (leftSupported : ∀ wave, wave ∉ sourceModes → left wave = 0)
    (output : IntegerWavevector) :
    rationalVorticityBilinearCoefficientAt
        actionModes left right output =
      ∑ sourceWave ∈ sourceModes,
        if output - sourceWave ∈ actionModes then
          rationalVorticityPairContribution
            sourceWave (output - sourceWave)
            (left sourceWave) (right (output - sourceWave))
        else 0 := by
  classical
  unfold rationalVorticityBilinearCoefficientAt
  have restrictSource :
      (∑ sourceWave ∈ actionModes,
          ∑ second ∈ actionModes,
            if sourceWave + second = output then
              rationalVorticityPairContribution
                sourceWave second (left sourceWave) (right second)
            else 0) =
        ∑ sourceWave ∈ sourceModes,
          ∑ second ∈ actionModes,
            if sourceWave + second = output then
              rationalVorticityPairContribution
                sourceWave second (left sourceWave) (right second)
            else 0 := by
    symm
    apply Finset.sum_subset_zero_on_sdiff sourceSubset
    · intro sourceWave sourceDifference
      have sourceNotMem := (Finset.mem_sdiff.mp sourceDifference).2
      apply Finset.sum_eq_zero
      intro second secondMem
      by_cases incidence : sourceWave + second = output
      · rw [if_pos incidence, leftSupported sourceWave sourceNotMem]
        exact rationalVorticityPairContribution_zero_left
          sourceWave second (right second)
      · simp [incidence]
    · intro sourceWave sourceMem
      rfl
  rw [restrictSource]
  apply Finset.sum_congr rfl
  intro sourceWave sourceMem
  have incidence : ∀ second : IntegerWavevector,
      sourceWave + second = output ↔ second = output - sourceWave := by
    intro second
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [incidence]
  by_cases secondMem : output - sourceWave ∈ actionModes
  · simp [secondMem]
  · simp [secondMem]

def rationalVorticityNonlinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (state : GaussianRatState)
    (output : IntegerWavevector) : GaussianRatVector :=
  rationalVorticityBilinearCoefficientAt modes state state output

theorem GaussianRatVector.toComplex_finsetSum
    {Index : Type*}
    (items : Finset Index)
    (row : Index → GaussianRatVector) :
    GaussianRatVector.toComplex (∑ item ∈ items, row item) =
      ∑ item ∈ items, GaussianRatVector.toComplex (row item) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items itemNotMem induction =>
      simp [itemNotMem, induction]

theorem rationalVorticityBilinearCoefficientAt_toComplex
    (modes : Finset IntegerWavevector)
    (left right : GaussianRatState)
    (leftState rightState : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (leftFaithful : ∀ wave ∈ modes,
      GaussianRatVector.toComplex (left wave) = leftState wave)
    (rightFaithful : ∀ wave ∈ modes,
      GaussianRatVector.toComplex (right wave) = rightState wave) :
    GaussianRatVector.toComplex
        (rationalVorticityBilinearCoefficientAt
          modes left right output) =
      finiteStateVorticityBilinearCoefficientAt
        modes leftState rightState output := by
  classical
  unfold rationalVorticityBilinearCoefficientAt
    finiteStateVorticityBilinearCoefficientAt
  rw [GaussianRatVector.toComplex_finsetSum]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [GaussianRatVector.toComplex_finsetSum]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases incidence : first + second = output
  · rw [if_pos incidence, if_pos incidence]
    exact rationalVorticityPairContribution_toComplex
      leftState rightState first second (left first) (right second)
      (fun firstZero => zeroNotMem (firstZero ▸ firstMem))
      (fun secondZero => zeroNotMem (secondZero ▸ secondMem))
      (leftFaithful first firstMem) (rightFaithful second secondMem)
  · simp [incidence]

theorem rationalVorticityNonlinearCoefficientAt_toComplex
    (modes : Finset IntegerWavevector)
    (state : GaussianRatState)
    (complexState : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (faithful : ∀ wave ∈ modes,
      GaussianRatVector.toComplex (state wave) = complexState wave) :
    GaussianRatVector.toComplex
        (rationalVorticityNonlinearCoefficientAt modes state output) =
      finiteStateVorticityNonlinearCoefficientAt
        modes complexState output := by
  simpa only [rationalVorticityNonlinearCoefficientAt,
    finiteStateVorticityBilinearCoefficientAt,
    finiteStateVorticityNonlinearCoefficientAt,
    finiteStateVorticityBilinearPairContribution,
    finiteStateVorticityNonlinearPairContribution] using
    rationalVorticityBilinearCoefficientAt_toComplex
      modes state state complexState complexState output zeroNotMem
      faithful faithful

def rationalVorticityGeneratorCoefficientAt
    (modes : Finset IntegerWavevector)
    (scaledViscosity : ℚ)
    (state : GaussianRatState)
    (output : IntegerWavevector) : GaussianRatVector :=
  GaussianRatVector.sub
    (rationalVorticityNonlinearCoefficientAt modes state output)
    (GaussianRatVector.ratScale
      (scaledViscosity * rationalIntegerWaveNormSq output)
      (state output))

theorem rationalVorticityGeneratorCoefficientAt_toComplex
    (modes : Finset IntegerWavevector)
    (scaledViscosity : ℚ)
    (state : GaussianRatState)
    (complexState : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (viscosity : ℝ)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (faithful : ∀ wave ∈ modes,
      GaussianRatVector.toComplex (state wave) = complexState wave)
    (outputFaithful :
      GaussianRatVector.toComplex (state output) = complexState output)
    (scaledViscosity_eq :
      viscosity * (2 * Real.pi) ^ 2 = (scaledViscosity : ℝ)) :
    GaussianRatVector.toComplex
        (rationalVorticityGeneratorCoefficientAt
          modes scaledViscosity state output) =
      finiteStateVorticityNonlinearCoefficientAt
          modes complexState output -
        (viscosity * integerWaveViscousMultiplier output) •
          complexState output := by
  rw [rationalVorticityGeneratorCoefficientAt,
    GaussianRatVector.toComplex_sub,
    GaussianRatVector.toComplex_ratScale,
    rationalVorticityNonlinearCoefficientAt_toComplex
      modes state complexState output zeroNotMem faithful,
    outputFaithful]
  congr 1
  have scalarEq :
      (((scaledViscosity * rationalIntegerWaveNormSq output : ℚ) : ℝ) : ℂ) =
        ((viscosity * integerWaveViscousMultiplier output : ℝ) : ℂ) := by
    congr 1
    rw [Rat.cast_mul, rationalIntegerWaveNormSq_cast,
      integerWaveViscousMultiplier]
    calc
      (scaledViscosity : ℝ) * integerWaveNormSq output =
          (viscosity * (2 * Real.pi) ^ 2) *
            integerWaveNormSq output := by rw [scaledViscosity_eq]
      _ = viscosity * ((2 * Real.pi) ^ 2 *
            integerWaveNormSq output) := by ring
  rw [scalarEq]
  rfl

end

end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
