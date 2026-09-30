import H0mework.Computation.ADC.Word

/-!
# Integer energy decision with bounded arithmetic

Positive calibration spans allow comparison of the two squared calibrated
ratios by cross multiplication. No real-valued division, square root or
trigonometric function occurs in the integer decision.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

def finiteADCEnergyIntegerLeft (rd ld : Int) : Int := rd ^ 2 * ld ^ 2

def finiteADCEnergyIntegerRight (rn rd ln ld : Int) : Int :=
  4 * (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2)

def finiteADCEnergyIntegerAboveQuarter (rn rd ln ld : Int) : Bool :=
  decide (0 < rd ∧ 0 < ld ∧
    finiteADCEnergyIntegerLeft rd ld < finiteADCEnergyIntegerRight rn rd ln ld)

theorem finiteADCEnergyIntegerAboveQuarter_correct
    (rn rd ln ld : Int) (rightSpan : 0 < rd) (leftSpan : 0 < ld) :
    finiteADCEnergyIntegerAboveQuarter rn rd ln ld = true ↔
      (1 : ℚ) / 4 < ((rn : ℚ) / rd) ^ 2 + ((ln : ℚ) / ld) ^ 2 := by
  have rdPositive : (0 : ℚ) < rd := by exact_mod_cast rightSpan
  have ldPositive : (0 : ℚ) < ld := by exact_mod_cast leftSpan
  have denominator : (0 : ℚ) < (rd : ℚ) ^ 2 * (ld : ℚ) ^ 2 :=
    mul_pos (sq_pos_of_pos rdPositive) (sq_pos_of_pos ldPositive)
  have ratios :
      ((rn : ℚ) / rd) ^ 2 + ((ln : ℚ) / ld) ^ 2 =
        ((rn : ℚ) ^ 2 * (ld : ℚ) ^ 2 + (ln : ℚ) ^ 2 * (rd : ℚ) ^ 2) /
          ((rd : ℚ) ^ 2 * (ld : ℚ) ^ 2) := by
    field_simp
  simp only [finiteADCEnergyIntegerAboveQuarter, decide_eq_true_eq,
    rightSpan, leftSpan, true_and]
  rw [ratios, lt_div_iff₀ denominator]
  unfold finiteADCEnergyIntegerLeft finiteADCEnergyIntegerRight
  constructor
  · intro less
    have cast :
        (rd : ℚ) ^ 2 * (ld : ℚ) ^ 2 <
          4 * ((rn : ℚ) ^ 2 * (ld : ℚ) ^ 2 + (ln : ℚ) ^ 2 * (rd : ℚ) ^ 2) := by
      exact_mod_cast less
    linarith
  · intro less
    have cast :
        (rd : ℚ) ^ 2 * (ld : ℚ) ^ 2 <
          4 * ((rn : ℚ) ^ 2 * (ld : ℚ) ^ 2 + (ln : ℚ) ^ 2 * (rd : ℚ) ^ 2) := by
      linarith
    exact_mod_cast cast

theorem finiteADCWord_difference_abs_le
    (code : FiniteADCResolutionCode) (left right : FiniteADCWord code) :
    |left.val - right.val| ≤ 32000000 := by
  have ll := left.property.1
  have lu := left.property.2
  have rl := right.property.1
  have ru := right.property.2
  apply abs_le.mpr
  cases code <;> norm_num [finiteADCGridDenominator] at ll lu rl ru <;>
    constructor <;> omega

theorem finiteADCEnergy_square_bound (x : Int) (bound : |x| ≤ 32000000) :
    x ^ 2 ≤ 32000000 ^ 2 := by
  have bounds := abs_le.mp bound
  nlinarith

theorem finiteADCEnergyInteger_bounds
    (rn rd ln ld : Int)
    (rnBound : |rn| ≤ 32000000) (rdBound : |rd| ≤ 32000000)
    (lnBound : |ln| ≤ 32000000) (ldBound : |ld| ≤ 32000000) :
    (0 ≤ finiteADCEnergyIntegerLeft rd ld ∧
      finiteADCEnergyIntegerLeft rd ld < 2 ^ 128) ∧
    (0 ≤ finiteADCEnergyIntegerRight rn rd ln ld ∧
      finiteADCEnergyIntegerRight rn rd ln ld < 2 ^ 128) := by
  have rnSq := finiteADCEnergy_square_bound rn rnBound
  have rdSq := finiteADCEnergy_square_bound rd rdBound
  have lnSq := finiteADCEnergy_square_bound ln lnBound
  have ldSq := finiteADCEnergy_square_bound ld ldBound
  have leftBound : rd ^ 2 * ld ^ 2 ≤ (32000000 : Int) ^ 2 * 32000000 ^ 2 :=
    mul_le_mul rdSq ldSq (sq_nonneg _) (by norm_num)
  have rightRBound : rn ^ 2 * ld ^ 2 ≤ (32000000 : Int) ^ 2 * 32000000 ^ 2 :=
    mul_le_mul rnSq ldSq (sq_nonneg _) (by norm_num)
  have rightLBound : ln ^ 2 * rd ^ 2 ≤ (32000000 : Int) ^ 2 * 32000000 ^ 2 :=
    mul_le_mul lnSq rdSq (sq_nonneg _) (by norm_num)
  unfold finiteADCEnergyIntegerLeft finiteADCEnergyIntegerRight
  constructor
  · exact ⟨mul_nonneg (sq_nonneg _) (sq_nonneg _), by norm_num at leftBound ⊢; omega⟩
  · constructor
    · positivity
    · norm_num at rightRBound rightLBound ⊢
      omega

/-- Actual ADC symbols generate two unsigned 128-bit comparison operands. -/
def finiteADCWordEnergyOperands128
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) :
    QuantizedWord 128 × QuantizedWord 128 := by
  let rn := roperational.val - rzero.val
  let rd := rspan.val - rzero.val
  let ln := loperational.val - lzero.val
  let ld := lspan.val - lzero.val
  have bounded := finiteADCEnergyInteger_bounds rn rd ln ld
    (finiteADCWord_difference_abs_le code roperational rzero)
    (finiteADCWord_difference_abs_le code rspan rzero)
    (finiteADCWord_difference_abs_le code loperational lzero)
    (finiteADCWord_difference_abs_le code lspan lzero)
  exact
    (⟨(finiteADCEnergyIntegerLeft rd ld).toNat,
        (Int.toNat_lt bounded.1.1).mpr (by exact_mod_cast bounded.1.2)⟩,
      ⟨(finiteADCEnergyIntegerRight rn rd ln ld).toNat,
        (Int.toNat_lt bounded.2.1).mpr (by exact_mod_cast bounded.2.2)⟩)

def finiteADCWordEnergyDecision128
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) : Bool :=
  let operands := finiteADCWordEnergyOperands128
    code rzero rspan roperational lzero lspan loperational
  decide (rzero.val < rspan.val ∧ lzero.val < lspan.val ∧ operands.1.val < operands.2.val)

theorem finiteADCWordEnergyDecision128_exact
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) :
    finiteADCWordEnergyDecision128 code rzero rspan roperational lzero lspan loperational =
      finiteADCEnergyIntegerAboveQuarter
        (roperational.val - rzero.val) (rspan.val - rzero.val)
        (loperational.val - lzero.val) (lspan.val - lzero.val) := by
  have leftNonnegative : 0 ≤ finiteADCEnergyIntegerLeft
      (rspan.val - rzero.val) (lspan.val - lzero.val) :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have compare :
      (finiteADCEnergyIntegerLeft (rspan.val - rzero.val) (lspan.val - lzero.val)).toNat <
          (finiteADCEnergyIntegerRight
            (roperational.val - rzero.val) (rspan.val - rzero.val)
            (loperational.val - lzero.val) (lspan.val - lzero.val)).toNat ↔
        finiteADCEnergyIntegerLeft (rspan.val - rzero.val) (lspan.val - lzero.val) <
          finiteADCEnergyIntegerRight
            (roperational.val - rzero.val) (rspan.val - rzero.val)
            (loperational.val - lzero.val) (lspan.val - lzero.val) := by omega
  simp only [finiteADCWordEnergyDecision128, finiteADCWordEnergyOperands128,
    finiteADCEnergyIntegerAboveQuarter, compare, sub_pos]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
