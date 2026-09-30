import H0mework.NavierStokes.Accumulation.RationalVorticityEvaluator

/-!
# Exact alternating butterfly subcell recurrence

Two transverse sidebands around an axis mode generate the next doubled-axis
receiver through the complete swapped ordered-pair fibre.  Alternating the
two coordinate pumps gives a finite rational template whose output remains
nonzero for every integer axis frequency `m ≥ 2` and every nonzero amplitude.

This file is the exact Fourier-operator material for the actual-current
advance.  It does not identify an action iterate with a PDE endpoint or
store a future contact sequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator

open Matrix
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter

def realGaussian (value : ℚ) : GaussianRat := ⟨value, 0⟩

def realRow (x y z : ℚ) : GaussianRatVector :=
  ![realGaussian x, realGaussian y, realGaussian z]

def axisWave (m : ℤ) : IntegerWavevector := ![m, 0, 0]
def pumpY : IntegerWavevector := ![0, 1, 0]
def pumpZ : IntegerWavevector := ![0, 0, 1]

def symPair
    (first second : IntegerWavevector)
    (firstRow secondRow : GaussianRatVector) : GaussianRatVector :=
  rationalVorticityPairContribution first second firstRow secondRow +
    rationalVorticityPairContribution second first secondRow firstRow

def butterflyCoefficient (m : ℤ) : ℚ :=
  8 * ((m : ℚ) ^ 2 - 1) / ((m : ℚ) ^ 2 + 1)

theorem butterflyCoefficient_pos
    (m : ℤ) (mTwo : 2 ≤ m) :
    0 < butterflyCoefficient m := by
  unfold butterflyCoefficient
  have mTwoRat : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast mTwo
  apply div_pos <;> nlinarith [sq_nonneg (m : ℚ)]

def sidebandPlusZ (m : ℤ) (a : ℚ) : GaussianRatVector :=
  symPair (axisWave m) pumpZ (realRow 0 a 0) (realRow 1 1 0)

def sidebandMinusZ (m : ℤ) (a : ℚ) : GaussianRatVector :=
  symPair (axisWave m) (-pumpZ) (realRow 0 a 0) (realRow 1 1 0)

theorem sidebandPlusZ_eq
    (m : ℤ) (mNe : m ≠ 0) (a : ℚ) :
    sidebandPlusZ m a =
      realRow (a / (m : ℚ)) (a * (1 / (m : ℚ) - m)) (-a) := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [sidebandPlusZ, symPair, axisWave, pumpZ, realRow,
      realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

theorem sidebandMinusZ_eq
    (m : ℤ) (mNe : m ≠ 0) (a : ℚ) :
    sidebandMinusZ m a =
      realRow (-a / (m : ℚ)) (a * ((m : ℚ) - 1 / m)) (-a) := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [sidebandMinusZ, symPair, axisWave, pumpZ, realRow,
      realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

def butterflyStepZ (m : ℤ) (a : ℚ) : GaussianRatVector :=
  symPair (axisWave m + pumpZ) (axisWave m - pumpZ)
    (sidebandPlusZ m a) (sidebandMinusZ m a)

theorem butterflyStepZ_eq
    (m : ℤ) (mNe : m ≠ 0) (a : ℚ) :
    butterflyStepZ m a =
      realRow 0 0 (-(butterflyCoefficient m * a ^ 2)) := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [butterflyStepZ, sidebandPlusZ_eq m mNe,
      sidebandMinusZ_eq m mNe,
      butterflyCoefficient, symPair, axisWave, pumpZ, realRow,
      realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;>
    ring

theorem butterflyStepZ_ne_zero
    (m : ℤ) (mTwo : 2 ≤ m) (a : ℚ) (aNe : a ≠ 0) :
    butterflyStepZ m a ≠ 0 := by
  rw [butterflyStepZ_eq m (by omega) a]
  intro rowZero
  have coordinate := congrArg (fun row : GaussianRatVector => (row 2).re)
    rowZero
  change -(butterflyCoefficient m * a ^ 2) = 0 at coordinate
  have coefficientPos := butterflyCoefficient_pos m mTwo
  have aSquarePos : 0 < a ^ 2 := sq_pos_of_ne_zero aNe
  nlinarith

def sidebandPlusY (m : ℤ) (a : ℚ) : GaussianRatVector :=
  symPair (axisWave m) pumpY (realRow 0 0 a) (realRow 1 0 1)

def sidebandMinusY (m : ℤ) (a : ℚ) : GaussianRatVector :=
  symPair (axisWave m) (-pumpY) (realRow 0 0 a) (realRow 1 0 1)

theorem sidebandPlusY_eq
    (m : ℤ) (mNe : m ≠ 0) (a : ℚ) :
    sidebandPlusY m a =
      realRow (-a / (m : ℚ)) a (a * ((m : ℚ) - 1 / m)) := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [sidebandPlusY, symPair, axisWave, pumpY, realRow,
      realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

theorem sidebandMinusY_eq
    (m : ℤ) (mNe : m ≠ 0) (a : ℚ) :
    sidebandMinusY m a =
      realRow (a / (m : ℚ)) a (a * (1 / (m : ℚ) - m)) := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [sidebandMinusY, symPair, axisWave, pumpY, realRow,
      realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

def butterflyStepY (m : ℤ) (a : ℚ) : GaussianRatVector :=
  symPair (axisWave m + pumpY) (axisWave m - pumpY)
    (sidebandPlusY m a) (sidebandMinusY m a)

theorem butterflyStepY_eq
    (m : ℤ) (mNe : m ≠ 0) (a : ℚ) :
    butterflyStepY m a =
      realRow 0 (butterflyCoefficient m * a ^ 2) 0 := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [butterflyStepY, sidebandPlusY_eq m mNe,
      sidebandMinusY_eq m mNe,
      butterflyCoefficient, symPair, axisWave, pumpY, realRow,
      realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;>
    ring

theorem butterflyStepY_ne_zero
    (m : ℤ) (mTwo : 2 ≤ m) (a : ℚ) (aNe : a ≠ 0) :
    butterflyStepY m a ≠ 0 := by
  rw [butterflyStepY_eq m (by omega) a]
  intro rowZero
  have coordinate := congrArg (fun row : GaussianRatVector => (row 1).re)
    rowZero
  change butterflyCoefficient m * a ^ 2 = 0 at coordinate
  have coefficientPos := butterflyCoefficient_pos m mTwo
  have aSquarePos : 0 < a ^ 2 := sq_pos_of_ne_zero aNe
  nlinarith

/-! ## Complete first target fibre -/

/-- Reality-closed first butterfly carrier at axis frequency `m = 2`. -/
def butterflyZTwoModes : Finset IntegerWavevector :=
  {axisWave 2, -axisWave 2, pumpZ, -pumpZ,
    axisWave 2 + pumpZ, axisWave 2 - pumpZ,
    -(axisWave 2 + pumpZ), -(axisWave 2 - pumpZ)}

def butterflyZTwoRow (a : ℚ)
    (wave : IntegerWavevector) : GaussianRatVector :=
  if wave = axisWave 2 ∨ wave = -axisWave 2 then realRow 0 a 0
  else if wave = pumpZ ∨ wave = -pumpZ then realRow 1 1 0
  else if wave = axisWave 2 + pumpZ ∨
      wave = -(axisWave 2 + pumpZ) then sidebandPlusZ 2 a
  else if wave = axisWave 2 - pumpZ ∨
      wave = -(axisWave 2 - pumpZ) then sidebandMinusZ 2 a
  else 0

/-- Complete ordered-pair row at the first doubled-axis target. -/
def butterflyZTwoFullFibre (a : ℚ) : GaussianRatVector :=
  ∑ first ∈ butterflyZTwoModes,
    let second := axisWave 4 - first
    if second ∈ butterflyZTwoModes then
      rationalVorticityPairContribution first second
        (butterflyZTwoRow a first) (butterflyZTwoRow a second)
    else 0

/-- At the target `2k`, the complete finite fibre contains no hidden pump,
negative-mode, or self-interaction correction: it is exactly the two
sideband butterfly row. -/
theorem butterflyZTwoFullFibre_eq_step (a : ℚ) :
    butterflyZTwoFullFibre a = butterflyStepZ 2 a := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [butterflyZTwoFullFibre, butterflyZTwoModes,
      butterflyZTwoRow, butterflyStepZ, sidebandPlusZ_eq,
      sidebandMinusZ_eq, symPair, axisWave, pumpZ,
      realRow, realGaussian, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    norm_num

theorem butterflyZTwoFullFibre_eq (a : ℚ) :
    butterflyZTwoFullFibre a =
      realRow 0 0 (-(24 / 5 * a ^ 2)) := by
  rw [butterflyZTwoFullFibre_eq_step,
    butterflyStepZ_eq 2 (by norm_num)]
  norm_num [butterflyCoefficient]

/-! ## Source carrier with the next alternating pump -/

/-- The first physical butterfly carrier also retains the `Y` pump needed
by the next local advance.  It is still a finite source occurrence, not a
future table. -/
def butterflySeedModes : Finset IntegerWavevector :=
  butterflyZTwoModes ∪ {pumpY, -pumpY}

/-- Exact rational rows on the finite two-pump source carrier. -/
def butterflySeedRow (a : ℚ)
    (wave : IntegerWavevector) : GaussianRatVector :=
  if wave = pumpY ∨ wave = -pumpY then realRow 1 0 1
  else butterflyZTwoRow a wave

/-- Complete first doubled-axis fibre on the two-pump source carrier. -/
def butterflySeedFullFibre (a : ℚ) : GaussianRatVector :=
  ∑ first ∈ butterflySeedModes,
    let second := axisWave 4 - first
    if second ∈ butterflySeedModes then
      rationalVorticityPairContribution first second
        (butterflySeedRow a first) (butterflySeedRow a second)
    else 0

/-- Retaining the next `Y` pump introduces no hidden contribution at the
first doubled-axis target. -/
theorem butterflySeedFullFibre_eq (a : ℚ) :
    butterflySeedFullFibre a = butterflyZTwoFullFibre a := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [butterflySeedFullFibre, butterflySeedModes,
      butterflySeedRow, butterflyZTwoFullFibre, butterflyZTwoModes,
      butterflyZTwoRow, sidebandPlusZ_eq, sidebandMinusZ_eq,
      axisWave, pumpY, pumpZ, realRow, realGaussian,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
