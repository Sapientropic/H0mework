import H0mework.NavierStokes.NativeWorkButterfly.SidebandOrthantInward

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace SaturationMonoid.NavierStokes.RationalVorticityEvaluator
namespace ButterflyParametricOrientedCell

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget

noncomputable section

def yCellPlusWave (m : Int) : IntegerWavevector := axisWave m + pumpY
def yCellMinusWave (m : Int) : IntegerWavevector := axisWave m - pumpY

def yCellPlusRow (m : Int) (x z : Rat) : GaussianRatVector :=
  realRow x (-(m : Rat) * x) z

def yCellMinusRow (m : Int) (y w : Rat) : GaussianRatVector :=
  realRow y ((m : Rat) * y) w

inductive YCellSlot
  | axisPos | axisNeg | pumpPos | pumpNeg
  | plusPos | plusNeg | minusPos | minusNeg
  deriving DecidableEq

def yCellSlots : Finset YCellSlot :=
  {.axisPos, .axisNeg, .pumpPos, .pumpNeg,
    .plusPos, .plusNeg, .minusPos, .minusNeg}

example (f : YCellSlot → Nat) :
    (∑ slot ∈ yCellSlots, f slot) =
      f .axisPos + f .axisNeg + f .pumpPos + f .pumpNeg +
        f .plusPos + f .plusNeg + f .minusPos + f .minusNeg := by
  simp [yCellSlots]
  omega

def YCellSlot.wave (m : Int) : YCellSlot → IntegerWavevector
  | .axisPos => axisWave m
  | .axisNeg => -axisWave m
  | .pumpPos => pumpY
  | .pumpNeg => -pumpY
  | .plusPos => yCellPlusWave m
  | .plusNeg => -yCellPlusWave m
  | .minusPos => yCellMinusWave m
  | .minusNeg => -yCellMinusWave m

theorem YCellSlot.wave_injective
    (m : Int) (mTwo : 2 ≤ m) : Function.Injective (YCellSlot.wave m) := by
  intro left right equality
  cases left <;> cases right <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      axisWave, pumpY] at equality ⊢ <;>
    omega

theorem integerWave_eq_iff_coordinates
    (left right : IntegerWavevector) :
    left = right ↔
      left 0 = right 0 ∧ left 1 = right 1 ∧ left 2 = right 2 := by
  constructor
  · intro equality
    subst right
    simp
  · rintro ⟨zero, one, two⟩
    funext coordinate
    fin_cases coordinate
    · exact zero
    · exact one
    · exact two

def YCellSlot.row (m : Int) (a x z y w : Rat) : YCellSlot → GaussianRatVector
  | .axisPos | .axisNeg => realRow 0 0 a
  | .pumpPos | .pumpNeg => realRow 1 0 1
  | .plusPos | .plusNeg => yCellPlusRow m x z
  | .minusPos | .minusNeg => yCellMinusRow m y w

theorem YCellSlot.add_eq_plus_iff
    (m : Int) (mTwo : 2 ≤ m) (first second : YCellSlot) :
    YCellSlot.wave m first + YCellSlot.wave m second = yCellPlusWave m ↔
      (first = .axisPos ∧ second = .pumpPos) ∨
      (first = .pumpPos ∧ second = .axisPos) := by
  cases first <;> cases second <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      integerWave_eq_iff_coordinates,
      axisWave, pumpY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    omega

theorem YCellSlot.add_eq_minus_iff
    (m : Int) (mTwo : 2 ≤ m) (first second : YCellSlot) :
    YCellSlot.wave m first + YCellSlot.wave m second = yCellMinusWave m ↔
      (first = .axisPos ∧ second = .pumpNeg) ∨
      (first = .pumpNeg ∧ second = .axisPos) := by
  cases first <;> cases second <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      integerWave_eq_iff_coordinates,
      axisWave, pumpY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    omega

theorem YCellSlot.add_eq_childAxis_iff
    (m : Int) (mTwo : 2 ≤ m) (first second : YCellSlot) :
    YCellSlot.wave m first + YCellSlot.wave m second = axisWave (2 * m) ↔
      (first = .axisPos ∧ second = .axisPos) ∨
      (first = .plusPos ∧ second = .minusPos) ∨
      (first = .minusPos ∧ second = .plusPos) := by
  cases first <;> cases second <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      integerWave_eq_iff_coordinates,
      axisWave, pumpY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    omega

theorem YCellSlot.add_eq_childPlus_iff
    (m : Int) (mTwo : 2 ≤ m) (first second : YCellSlot) :
    YCellSlot.wave m first + YCellSlot.wave m second =
        axisWave (2 * m) + pumpY ↔
      (first = .axisPos ∧ second = .plusPos) ∨
      (first = .plusPos ∧ second = .axisPos) := by
  cases first <;> cases second <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      integerWave_eq_iff_coordinates,
      axisWave, pumpY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    omega

theorem YCellSlot.add_eq_childMinus_iff
    (m : Int) (mTwo : 2 ≤ m) (first second : YCellSlot) :
    YCellSlot.wave m first + YCellSlot.wave m second =
        axisWave (2 * m) - pumpY ↔
      (first = .axisPos ∧ second = .minusPos) ∨
      (first = .minusPos ∧ second = .axisPos) := by
  cases first <;> cases second <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      integerWave_eq_iff_coordinates,
      axisWave, pumpY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    omega

def yCellModes (m : Int) : Finset IntegerWavevector :=
  yCellSlots.image (YCellSlot.wave m)

def yCellState (m : Int) (a x z y w : Rat) : GaussianRatState := fun wave =>
  ∑ slot ∈ yCellSlots,
    if YCellSlot.wave m slot = wave then YCellSlot.row m a x z y w slot
    else 0

theorem yCellState_slot
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) (slot : YCellSlot) :
    yCellState m a x z y w (YCellSlot.wave m slot) =
      YCellSlot.row m a x z y w slot := by
  classical
  unfold yCellState
  have injective := YCellSlot.wave_injective m mTwo
  cases slot <;>
    simp [yCellSlots, YCellSlot.row, injective.eq_iff]

theorem yCellState_axisPos
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    yCellState m a x z y w (axisWave m) = realRow 0 0 a := by
  simpa only [YCellSlot.wave, YCellSlot.row] using
    yCellState_slot m mTwo a x z y w YCellSlot.axisPos

theorem yCellState_pumpPos
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    yCellState m a x z y w pumpY = realRow 1 0 1 := by
  simpa only [YCellSlot.wave, YCellSlot.row] using
    yCellState_slot m mTwo a x z y w YCellSlot.pumpPos

theorem yCellState_pumpNeg
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    yCellState m a x z y w (-pumpY) = realRow 1 0 1 := by
  simpa only [YCellSlot.wave, YCellSlot.row] using
    yCellState_slot m mTwo a x z y w YCellSlot.pumpNeg

theorem yCellState_plusPos
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    yCellState m a x z y w (yCellPlusWave m) =
      yCellPlusRow m x z := by
  simpa only [YCellSlot.wave, YCellSlot.row] using
    yCellState_slot m mTwo a x z y w YCellSlot.plusPos

theorem yCellState_minusPos
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    yCellState m a x z y w (yCellMinusWave m) =
      yCellMinusRow m y w := by
  simpa only [YCellSlot.wave, YCellSlot.row] using
    yCellState_slot m mTwo a x z y w YCellSlot.minusPos

theorem yCellState_supported
    (m : Int) (a x z y w : Rat) (wave : IntegerWavevector)
    (waveNotMem : wave ∉ yCellModes m) :
    yCellState m a x z y w wave = 0 := by
  unfold yCellState
  apply Finset.sum_eq_zero
  intro slot slotMem
  rw [if_neg]
  intro equality
  exact waveNotMem (Finset.mem_image.mpr ⟨slot, slotMem, equality⟩)

/-! ## Faithful complex restriction -/

def yCellPhysicalState
    (m : Int) (a x z y w : Rat) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState (yCellModes m) fun wave =>
    GaussianRatVector.toComplex (yCellState m a x z y w wave)

theorem yCellModes_zeroNotMem
    (m : Int) (mTwo : 2 ≤ m) :
    (0 : IntegerWavevector) ∉ yCellModes m := by
  intro zeroMem
  rw [yCellModes, Finset.mem_image] at zeroMem
  obtain ⟨slot, _slotMem, slotZero⟩ := zeroMem
  cases slot <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      axisWave, pumpY, integerWave_eq_iff_coordinates,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at slotZero <;>
    omega

theorem yCellPhysicalState_apply_of_mem
    (m : Int) (a x z y w : Rat)
    (wave : IntegerWavevector) (waveMem : wave ∈ yCellModes m) :
    yCellPhysicalState m a x z y w wave =
      GaussianRatVector.toComplex (yCellState m a x z y w wave) := by
  unfold yCellPhysicalState
  rw [finiteComplexVorticityState_apply, if_pos waveMem]

theorem yCellPhysicalState_supported
    (m : Int) (a x z y w : Rat)
    (wave : IntegerWavevector) (waveNotMem : wave ∉ yCellModes m) :
    yCellPhysicalState m a x z y w wave = 0 := by
  unfold yCellPhysicalState
  rw [finiteComplexVorticityState_apply, if_neg waveNotMem]

theorem YCellSlot.waveDot_row_zero
    (m : Int) (a x z y w : Rat) (slot : YCellSlot) :
    GaussianRatVector.waveDot (YCellSlot.wave m slot)
      (YCellSlot.row m a x z y w slot) = 0 := by
  cases slot <;>
    apply GaussianRat.ext <;>
    simp [YCellSlot.wave, YCellSlot.row, yCellPlusWave,
      yCellMinusWave, yCellPlusRow, yCellMinusRow,
      axisWave, pumpY, realRow, realGaussian,
      GaussianRatVector.waveDot, GaussianRat.add,
      GaussianRat.ratScale, GaussianRat.intScale,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    ring

theorem yCellPhysicalState_transverse
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    WholeStateTransverse (yCellPhysicalState m a x z y w) := by
  intro wave
  by_cases waveMem : wave ∈ yCellModes m
  · rw [yCellModes, Finset.mem_image] at waveMem
    obtain ⟨slot, slotMem, rfl⟩ := waveMem
    rw [yCellPhysicalState_apply_of_mem]
    · rw [← GaussianRatVector.toComplex_waveDot,
        yCellState_slot m mTwo,
        YCellSlot.waveDot_row_zero]
      exact GaussianRat.toComplex_zero
    · exact Finset.mem_image.mpr ⟨slot, slotMem, rfl⟩
  · rw [yCellPhysicalState_supported m a x z y w wave waveMem,
      dotProduct_zero]

def yCellAction (m : Int) (a q x z y w : Rat) : GaussianRatState :=
  rationalVorticityGeneratorCoefficientAt (yCellModes m) q
    (yCellState m a x z y w)

theorem yCellAction_toComplex
    (nu : Viscosity)
    (m : Int) (mTwo : 2 ≤ m) (a q x z y w : Rat)
    (scaledViscosity_eq :
      nu.coeff * (2 * Real.pi) ^ 2 = (q : Real))
    (output : IntegerWavevector) :
    GaussianRatVector.toComplex (yCellAction m a q x z y w output) =
      wholeLatticeVorticityFourierTangentAt nu.coeff
        (yCellPhysicalState m a x z y w) output := by
  have bridge := rationalVorticityGeneratorCoefficientAt_toComplex
    (yCellModes m) q (yCellState m a x z y w)
    (yCellPhysicalState m a x z y w) output nu.coeff
    (yCellModes_zeroNotMem m mTwo)
    (by
      intro wave waveMem
      exact (yCellPhysicalState_apply_of_mem
        m a x z y w wave waveMem).symm)
    (by
      by_cases outputMem : output ∈ yCellModes m
      · exact (yCellPhysicalState_apply_of_mem
          m a x z y w output outputMem).symm
      · rw [yCellState_supported m a x z y w output outputMem,
          yCellPhysicalState_supported m a x z y w output outputMem]
        exact GaussianRatVector.toComplex_zero_instance)
    scaledViscosity_eq
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    (yCellModes m) (yCellPhysicalState m a x z y w)
    (yCellPhysicalState_supported m a x z y w) output]
  exact bridge

def yCellPlusActionRow (m : Int) (a q x z : Rat) : GaussianRatVector :=
  GaussianRatVector.sub (sidebandPlusY m a)
    (GaussianRatVector.ratScale
      (q * ((m : Rat) ^ 2 + 1)) (yCellPlusRow m x z))

def yCellMinusActionRow (m : Int) (a q y w : Rat) : GaussianRatVector :=
  GaussianRatVector.sub (sidebandMinusY m a)
    (GaussianRatVector.ratScale
      (q * ((m : Rat) ^ 2 + 1)) (yCellMinusRow m y w))

theorem yCellBilinear_eq_slotSum
    (m : Int) (mTwo : 2 ≤ m)
    (state : GaussianRatState) (output : IntegerWavevector) :
    rationalVorticityBilinearCoefficientAt (yCellModes m)
        state state output =
      ∑ first ∈ yCellSlots, ∑ second ∈ yCellSlots,
        if YCellSlot.wave m first + YCellSlot.wave m second = output then
          rationalVorticityPairContribution
            (YCellSlot.wave m first) (YCellSlot.wave m second)
            (state (YCellSlot.wave m first))
            (state (YCellSlot.wave m second))
        else 0 := by
  classical
  unfold rationalVorticityBilinearCoefficientAt yCellModes
  rw [Finset.sum_image (YCellSlot.wave_injective m mTwo).injOn]
  apply Finset.sum_congr rfl
  intro first _firstMem
  rw [Finset.sum_image (YCellSlot.wave_injective m mTwo).injOn]

theorem yCellNonlinear_plus_eq
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    rationalVorticityNonlinearCoefficientAt (yCellModes m)
        (yCellState m a x z y w) (yCellPlusWave m) =
      sidebandPlusY m a := by
  unfold rationalVorticityNonlinearCoefficientAt
  rw [yCellBilinear_eq_slotSum m mTwo]
  simp_rw [YCellSlot.add_eq_plus_iff m mTwo]
  simp [yCellSlots, YCellSlot.wave, yCellState_axisPos m mTwo,
    yCellState_pumpPos m mTwo, sidebandPlusY, symPair]

theorem yCellNonlinear_minus_eq
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    rationalVorticityNonlinearCoefficientAt (yCellModes m)
        (yCellState m a x z y w) (yCellMinusWave m) =
      sidebandMinusY m a := by
  unfold rationalVorticityNonlinearCoefficientAt
  rw [yCellBilinear_eq_slotSum m mTwo]
  simp_rw [YCellSlot.add_eq_minus_iff m mTwo]
  simp [yCellSlots, YCellSlot.wave, yCellState_axisPos m mTwo,
    yCellState_pumpNeg m mTwo, sidebandMinusY, symPair]

/-- The same parent occurrence emits the complete child axis row.  The
coefficient is strictly oriented on the parent orthant; it is not a
postulated next packet. -/
theorem yCellNonlinear_childAxis_eq
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    rationalVorticityNonlinearCoefficientAt (yCellModes m)
        (yCellState m a x z y w) (axisWave (2 * m)) =
      realRow 0
        ((4 * (m : Rat) ^ 2 / ((m : Rat) ^ 2 + 1)) *
          (x * w + z * y)) 0 := by
  unfold rationalVorticityNonlinearCoefficientAt
  rw [yCellBilinear_eq_slotSum m mTwo]
  simp_rw [YCellSlot.add_eq_childAxis_iff m mTwo]
  simp_rw [yCellState_slot m mTwo a x z y w]
  have mNe : m ≠ 0 := by omega
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
  simp (config := { maxSteps := 5000000 })
    [yCellSlots, YCellSlot.wave, YCellSlot.row,
      yCellPlusWave, yCellMinusWave,
      yCellPlusRow, yCellMinusRow, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq, axisWave, pumpY, realRow, realGaussian,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

theorem yCellState_childAxis_zero
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    yCellState m a x z y w (axisWave (2 * m)) = 0 := by
  apply yCellState_supported
  intro childMem
  rw [yCellModes, Finset.mem_image] at childMem
  obtain ⟨slot, _slotMem, slotEq⟩ := childMem
  have xEq := congrArg (fun wave : IntegerWavevector => wave 0) slotEq
  cases slot <;>
    simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
      axisWave, pumpY] at xEq <;>
    omega

theorem yCellAction_childAxis_eq
    (m : Int) (mTwo : 2 ≤ m) (a q x z y w : Rat) :
    yCellAction m a q x z y w (axisWave (2 * m)) =
      realRow 0
        ((4 * (m : Rat) ^ 2 / ((m : Rat) ^ 2 + 1)) *
          (x * w + z * y)) 0 := by
  unfold yCellAction rationalVorticityGeneratorCoefficientAt
  rw [yCellNonlinear_childAxis_eq m mTwo,
    yCellState_childAxis_zero m mTwo]
  funext coordinate
  apply GaussianRat.ext <;>
    simp [GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.ratScale]

/-- The positive child sideband is generated on the same parent action. -/
theorem yCellNonlinear_childPlus_eq
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    rationalVorticityNonlinearCoefficientAt (yCellModes m)
        (yCellState m a x z y w) (axisWave (2 * m) + pumpY) =
      realRow (-(a * x / (m : Rat))) (2 * a * x)
        (-(a * z / ((m : Rat) * ((m : Rat) ^ 2 + 1)))) := by
  unfold rationalVorticityNonlinearCoefficientAt
  rw [yCellBilinear_eq_slotSum m mTwo]
  simp_rw [YCellSlot.add_eq_childPlus_iff m mTwo]
  simp_rw [yCellState_slot m mTwo a x z y w]
  have mNe : m ≠ 0 := by omega
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
  simp (config := { maxSteps := 5000000 })
    [yCellSlots, YCellSlot.wave, YCellSlot.row,
      yCellPlusWave, yCellMinusWave,
      yCellPlusRow, yCellMinusRow, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq, axisWave, pumpY, realRow, realGaussian,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

/-- The negative child sideband is generated on the same parent action. -/
theorem yCellNonlinear_childMinus_eq
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat) :
    rationalVorticityNonlinearCoefficientAt (yCellModes m)
        (yCellState m a x z y w) (axisWave (2 * m) - pumpY) =
      realRow (a * y / (m : Rat)) (2 * a * y)
        (a * w / ((m : Rat) * ((m : Rat) ^ 2 + 1))) := by
  unfold rationalVorticityNonlinearCoefficientAt
  rw [yCellBilinear_eq_slotSum m mTwo]
  simp_rw [YCellSlot.add_eq_childMinus_iff m mTwo]
  simp_rw [yCellState_slot m mTwo a x z y w]
  have mNe : m ≠ 0 := by omega
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
  simp (config := { maxSteps := 5000000 })
    [yCellSlots, YCellSlot.wave, YCellSlot.row,
      yCellPlusWave, yCellMinusWave,
      yCellPlusRow, yCellMinusRow, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq, axisWave, pumpY, realRow, realGaussian,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    field_simp [mNe] <;> ring

/-- All three child rows carry a nonzero, correctly oriented incidence when
the parent lies in its source orthant. -/
theorem yCell_childRows_oriented
    (m : Int) (mTwo : 2 ≤ m) (a x z y w : Rat)
    (aNeg : a < 0) (xPos : 0 < x) (zNeg : z < 0)
    (yNeg : y < 0) (wPos : 0 < w) :
    0 < (rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m)) 1).re ∧
      0 < (rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m) + pumpY) 0).re ∧
      (rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m) + pumpY) 2).re < 0 ∧
      0 < (rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m) - pumpY) 0).re ∧
      (rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m) - pumpY) 2).re < 0 := by
  rw [yCellNonlinear_childAxis_eq m mTwo,
    yCellNonlinear_childPlus_eq m mTwo,
    yCellNonlinear_childMinus_eq m mTwo]
  have mPos : (0 : Rat) < (m : Rat) := by exact_mod_cast
    (lt_of_lt_of_le (by norm_num : (0 : Int) < 2) mTwo)
  have denominatorPos :
      0 < (m : Rat) * ((m : Rat) ^ 2 + 1) := by positivity
  have coefficientPos :
      0 < 4 * (m : Rat) ^ 2 / ((m : Rat) ^ 2 + 1) := by positivity
  simp [realRow, realGaussian, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  constructor
  · exact mul_pos coefficientPos
      (add_pos (mul_pos xPos wPos) (mul_pos_of_neg_of_neg zNeg yNeg))
  constructor
  · exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos aNeg xPos) mPos
  constructor
  · have positive :=
      div_pos (mul_pos_of_neg_of_neg aNeg zNeg) denominatorPos
    linarith
  constructor
  · exact div_pos (mul_pos_of_neg_of_neg aNeg yNeg) mPos
  · exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos aNeg wPos)
      denominatorPos

/-- The same orientation is an exact row of the full viscous action.  All
three child modes are fresh for the parent carrier, so the viscous term
vanishes definitionally rather than being estimated. -/
theorem yCellAction_childRows_oriented
    (m : Int) (mTwo : 2 ≤ m) (a q x z y w : Rat)
    (aNeg : a < 0) (xPos : 0 < x) (zNeg : z < 0)
    (yNeg : y < 0) (wPos : 0 < w) :
    0 < (yCellAction m a q x z y w (axisWave (2 * m)) 1).re ∧
      0 < (yCellAction m a q x z y w
          (axisWave (2 * m) + pumpY) 0).re ∧
      (yCellAction m a q x z y w
          (axisWave (2 * m) + pumpY) 2).re < 0 ∧
      0 < (yCellAction m a q x z y w
          (axisWave (2 * m) - pumpY) 0).re ∧
      (yCellAction m a q x z y w
          (axisWave (2 * m) - pumpY) 2).re < 0 := by
  have childAxisNotMem : axisWave (2 * m) ∉ yCellModes m := by
    intro childMem
    rw [yCellModes, Finset.mem_image] at childMem
    obtain ⟨slot, _slotMem, slotEq⟩ := childMem
    have xEq := congrArg (fun wave : IntegerWavevector => wave 0) slotEq
    cases slot <;>
      simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
        axisWave, pumpY] at xEq <;>
      omega
  have childPlusNotMem : axisWave (2 * m) + pumpY ∉ yCellModes m := by
    intro childMem
    rw [yCellModes, Finset.mem_image] at childMem
    obtain ⟨slot, _slotMem, slotEq⟩ := childMem
    have xEq := congrArg (fun wave : IntegerWavevector => wave 0) slotEq
    cases slot <;>
      simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
        axisWave, pumpY] at xEq <;>
      omega
  have childMinusNotMem : axisWave (2 * m) - pumpY ∉ yCellModes m := by
    intro childMem
    rw [yCellModes, Finset.mem_image] at childMem
    obtain ⟨slot, _slotMem, slotEq⟩ := childMem
    have xEq := congrArg (fun wave : IntegerWavevector => wave 0) slotEq
    cases slot <;>
      simp [YCellSlot.wave, yCellPlusWave, yCellMinusWave,
        axisWave, pumpY] at xEq <;>
      omega
  have axisAction :
      yCellAction m a q x z y w (axisWave (2 * m)) =
        rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m)) := by
    unfold yCellAction rationalVorticityGeneratorCoefficientAt
    rw [yCellState_supported m a x z y w _ childAxisNotMem]
    funext coordinate
    apply GaussianRat.ext <;>
      simp [GaussianRatVector.sub, GaussianRatVector.ratScale,
        GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
        GaussianRat.ratScale]
  have plusAction :
      yCellAction m a q x z y w (axisWave (2 * m) + pumpY) =
        rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m) + pumpY) := by
    unfold yCellAction rationalVorticityGeneratorCoefficientAt
    rw [yCellState_supported m a x z y w _ childPlusNotMem]
    funext coordinate
    apply GaussianRat.ext <;>
      simp [GaussianRatVector.sub, GaussianRatVector.ratScale,
        GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
        GaussianRat.ratScale]
  have minusAction :
      yCellAction m a q x z y w (axisWave (2 * m) - pumpY) =
        rationalVorticityNonlinearCoefficientAt (yCellModes m)
          (yCellState m a x z y w) (axisWave (2 * m) - pumpY) := by
    unfold yCellAction rationalVorticityGeneratorCoefficientAt
    rw [yCellState_supported m a x z y w _ childMinusNotMem]
    funext coordinate
    apply GaussianRat.ext <;>
      simp [GaussianRatVector.sub, GaussianRatVector.ratScale,
        GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
        GaussianRat.ratScale]
  rw [axisAction, plusAction, minusAction]
  exact yCell_childRows_oriented m mTwo a x z y w
    aNeg xPos zNeg yNeg wPos

theorem rationalIntegerWaveNormSq_yCellPlusWave
    (m : Int) :
    rationalIntegerWaveNormSq (yCellPlusWave m) = (m : Rat) ^ 2 + 1 := by
  simp [rationalIntegerWaveNormSq, yCellPlusWave, axisWave, pumpY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem rationalIntegerWaveNormSq_yCellMinusWave
    (m : Int) :
    rationalIntegerWaveNormSq (yCellMinusWave m) = (m : Rat) ^ 2 + 1 := by
  simp [rationalIntegerWaveNormSq, yCellMinusWave, axisWave, pumpY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem yCellAction_plus_eq
    (m : Int) (mTwo : 2 ≤ m) (a q x z y w : Rat) :
    yCellAction m a q x z y w (yCellPlusWave m) =
      yCellPlusActionRow m a q x z := by
  unfold yCellAction rationalVorticityGeneratorCoefficientAt
    yCellPlusActionRow
  rw [yCellNonlinear_plus_eq m mTwo,
    rationalIntegerWaveNormSq_yCellPlusWave,
    yCellState_plusPos m mTwo]

theorem yCellAction_minus_eq
    (m : Int) (mTwo : 2 ≤ m) (a q x z y w : Rat) :
    yCellAction m a q x z y w (yCellMinusWave m) =
      yCellMinusActionRow m a q y w := by
  unfold yCellAction rationalVorticityGeneratorCoefficientAt
    yCellMinusActionRow
  rw [yCellNonlinear_minus_eq m mTwo,
    rationalIntegerWaveNormSq_yCellMinusWave,
    yCellState_minusPos m mTwo]

theorem yCellPlusActionRow_wallX
    (m : Int) (mTwo : 2 ≤ m) (a q z : Rat) :
    (yCellPlusActionRow m a q 0 z 0).re = -(a / (m : Rat)) := by
  have mNe : m ≠ 0 := by omega
  simp [yCellPlusActionRow, yCellPlusRow, sidebandPlusY_eq m mNe,
    realRow, realGaussian, GaussianRatVector.sub,
    GaussianRatVector.ratScale, GaussianRat.add, GaussianRat.neg,
    GaussianRat.sub, GaussianRat.mul,
    GaussianRat.ratScale, Matrix.cons_val_zero]
  ring

theorem yCellPlusActionRow_wallZ
    (m : Int) (mTwo : 2 ≤ m) (a q x : Rat) :
    (yCellPlusActionRow m a q x 0 2).re =
      a * ((m : Rat) - 1 / m) := by
  have mNe : m ≠ 0 := by omega
  simp [yCellPlusActionRow, yCellPlusRow, sidebandPlusY_eq m mNe,
    realRow, realGaussian, GaussianRatVector.sub,
    GaussianRatVector.ratScale, GaussianRat.add, GaussianRat.neg,
    GaussianRat.sub, GaussianRat.mul,
    GaussianRat.ratScale, Matrix.cons_val_two]

theorem yCellMinusActionRow_wallY
    (m : Int) (mTwo : 2 ≤ m) (a q w : Rat) :
    (yCellMinusActionRow m a q 0 w 0).re = a / (m : Rat) := by
  have mNe : m ≠ 0 := by omega
  simp [yCellMinusActionRow, yCellMinusRow, sidebandMinusY_eq m mNe,
    realRow, realGaussian, GaussianRatVector.sub,
    GaussianRatVector.ratScale, GaussianRat.add, GaussianRat.neg,
    GaussianRat.sub, GaussianRat.mul,
    GaussianRat.ratScale, Matrix.cons_val_zero]

theorem yCellMinusActionRow_wallW
    (m : Int) (mTwo : 2 ≤ m) (a q y : Rat) :
    (yCellMinusActionRow m a q y 0 2).re =
      a * (1 / (m : Rat) - m) := by
  have mNe : m ≠ 0 := by omega
  simp [yCellMinusActionRow, yCellMinusRow, sidebandMinusY_eq m mNe,
    realRow, realGaussian, GaussianRatVector.sub,
    GaussianRatVector.ratScale, GaussianRat.add, GaussianRat.neg,
    GaussianRat.sub, GaussianRat.mul,
    GaussianRat.ratScale, Matrix.cons_val_two]

/-- The parametric cell has a viscosity-independent Nagumo orientation.
The damping coordinate vanishes on its own wall; only the exact axis/pump
incidence remains. -/
theorem yCellAction_walls_strictly_inward
    (m : Int) (mTwo : 2 ≤ m) (a q x z y w : Rat)
    (amplitudeNeg : a < 0) :
    0 < (yCellPlusActionRow m a q 0 z 0).re ∧
      (yCellPlusActionRow m a q x 0 2).re < 0 ∧
      (yCellMinusActionRow m a q 0 w 0).re < 0 ∧
      0 < (yCellMinusActionRow m a q y 0 2).re := by
  have mRatTwo : (2 : Rat) ≤ (m : Rat) := by exact_mod_cast mTwo
  have mPos : (0 : Rat) < (m : Rat) := by linarith
  have reciprocalLt : (1 / (m : Rat)) < (m : Rat) := by
    apply (div_lt_iff₀ mPos).2
    nlinarith
  rw [yCellPlusActionRow_wallX m mTwo,
    yCellPlusActionRow_wallZ m mTwo,
    yCellMinusActionRow_wallY m mTwo,
    yCellMinusActionRow_wallW m mTwo]
  constructor
  · exact neg_pos.mpr (div_neg_of_neg_of_pos amplitudeNeg mPos)
  constructor
  · exact mul_neg_of_neg_of_pos amplitudeNeg (sub_pos.mpr reciprocalLt)
  constructor
  · exact div_neg_of_neg_of_pos amplitudeNeg mPos
  · exact mul_pos_of_neg_of_neg amplitudeNeg (sub_neg.mpr reciprocalLt)

end
end ButterflyParametricOrientedCell
end SaturationMonoid.NavierStokes.RationalVorticityEvaluator
