import Mathlib.Data.BitVec
import H0mework.Computation.ADC.EnergyArithmetic

/-!
# Fixed-width ADC energy circuit

This file executes the energy comparison with actual `BitVec 128` operations.
The four signed ADC differences are embedded in two's-complement form.  Their
first squaring step is justified by modular ring semantics (and is therefore
not mislabelled as unsigned no-overflow when a difference is negative).  Every
subsequent square-product, sum, scale-by-four and unsigned comparison is proved
to agree with the corresponding unbounded integer calculation.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

/-- The complete value trace of one 128-bit energy comparator. -/
structure FiniteADCBitVectorEnergyExecution where
  resistorNumerator : BitVec 128
  resistorSpan : BitVec 128
  inductorNumerator : BitVec 128
  inductorSpan : BitVec 128
  resistorNumeratorSquared : BitVec 128
  resistorSpanSquared : BitVec 128
  inductorNumeratorSquared : BitVec 128
  inductorSpanSquared : BitVec 128
  thresholdDenominator : BitVec 128
  resistorEnergyTerm : BitVec 128
  inductorEnergyTerm : BitVec 128
  energySum : BitVec 128
  scaledEnergyNumerator : BitVec 128
  deriving DecidableEq, Repr

/-- Two's-complement embedding of one signed ADC-word difference. -/
def finiteADCBitVectorDifference128
    {code : FiniteADCResolutionCode}
    (left right : FiniteADCWord code) : BitVec 128 :=
  BitVec.ofInt 128 left.val - BitVec.ofInt 128 right.val

@[simp] theorem finiteADCBitVectorDifference128_eq_ofInt
    {code : FiniteADCResolutionCode}
    (left right : FiniteADCWord code) :
    finiteADCBitVectorDifference128 left right =
      BitVec.ofInt 128 (left.val - right.val) := by
  unfold finiteADCBitVectorDifference128
  rw [sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  rfl

/-- Execute every arithmetic stage at width 128. -/
def finiteADCBitVectorEnergyExecute
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) :
    FiniteADCBitVectorEnergyExecution :=
  let rn := finiteADCBitVectorDifference128 roperational rzero
  let rd := finiteADCBitVectorDifference128 rspan rzero
  let ln := finiteADCBitVectorDifference128 loperational lzero
  let ld := finiteADCBitVectorDifference128 lspan lzero
  let rn2 := rn * rn
  let rd2 := rd * rd
  let ln2 := ln * ln
  let ld2 := ld * ld
  let denominator := rd2 * ld2
  let resistorTerm := rn2 * ld2
  let inductorTerm := ln2 * rd2
  let sum := resistorTerm + inductorTerm
  let scaled := BitVec.ofNat 128 4 * sum
  { resistorNumerator := rn
    resistorSpan := rd
    inductorNumerator := ln
    inductorSpan := ld
    resistorNumeratorSquared := rn2
    resistorSpanSquared := rd2
    inductorNumeratorSquared := ln2
    inductorSpanSquared := ld2
    thresholdDenominator := denominator
    resistorEnergyTerm := resistorTerm
    inductorEnergyTerm := inductorTerm
    energySum := sum
    scaledEnergyNumerator := scaled }

/-- Read the generated trace using signed-positive span tests followed by one
unsigned 128-bit comparison. -/
def finiteADCBitVectorEnergyRead
    (execution : FiniteADCBitVectorEnergyExecution) : Bool :=
  (BitVec.zero 128).slt execution.resistorSpan &&
    (BitVec.zero 128).slt execution.inductorSpan &&
    execution.thresholdDenominator.ult execution.scaledEnergyNumerator

/-- End-to-end fixed-width decision on six physical ADC symbols. -/
def finiteADCBitVectorEnergyCircuit
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) : Bool :=
  finiteADCBitVectorEnergyRead
    (finiteADCBitVectorEnergyExecute
      code rzero rspan roperational lzero lspan loperational)

private theorem bitVector128_ofInt_toNat_exact
    (value : Int) (nonnegative : 0 ≤ value) (bounded : value < 2 ^ 128) :
    (BitVec.ofInt 128 value).toNat = value.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt nonnegative (by
    norm_num at bounded ⊢
    exact bounded)]

theorem finiteADCBitVectorDifference128_toInt
    {code : FiniteADCResolutionCode}
    (left right : FiniteADCWord code) :
    (finiteADCBitVectorDifference128 left right).toInt = left.val - right.val := by
  rw [finiteADCBitVectorDifference128_eq_ofInt]
  apply BitVec.toInt_ofInt_eq_self (by norm_num)
  · have bounded := finiteADCWord_difference_abs_le code left right
    have bounds := abs_le.mp bounded
    norm_num at bounds ⊢
    omega
  · have bounded := finiteADCWord_difference_abs_le code left right
    have bounds := abs_le.mp bounded
    norm_num at bounds ⊢
    omega

private theorem finiteADCBitVectorSquare128_eq_ofInt
    (value : Int) :
    BitVec.ofInt 128 value * BitVec.ofInt 128 value =
      BitVec.ofInt 128 (value ^ 2) := by
  simpa [pow_two] using (BitVec.ofInt_mul (n := 128) value value).symm

private theorem finiteADCBitVectorSignedSquare128_toNat_exact
    (value : Int) (bounded : |value| ≤ 32000000) :
    (BitVec.ofInt 128 value * BitVec.ofInt 128 value).toNat =
      (value ^ 2).toNat := by
  rw [finiteADCBitVectorSquare128_eq_ofInt]
  apply bitVector128_ofInt_toNat_exact
  · exact sq_nonneg value
  · have squareBound := finiteADCEnergy_square_bound value bounded
    norm_num at squareBound ⊢
    omega

private theorem bitVector128_nonnegativeMul_toNat_exact
    (left right : Int) (nonnegative : 0 ≤ left * right)
    (bounded : left * right < 2 ^ 128) :
    (BitVec.ofInt 128 left * BitVec.ofInt 128 right).toNat =
      (left * right).toNat := by
  rw [← BitVec.ofInt_mul]
  exact bitVector128_ofInt_toNat_exact _ nonnegative bounded

private theorem bitVector128_nonnegativeAdd_toNat_exact
    (left right : Int) (nonnegative : 0 ≤ left + right)
    (bounded : left + right < 2 ^ 128) :
    (BitVec.ofInt 128 left + BitVec.ofInt 128 right).toNat =
      (left + right).toNat := by
  rw [← BitVec.ofInt_add]
  exact bitVector128_ofInt_toNat_exact _ nonnegative bounded

/-- Exact mathematical values of every generated fixed-width stage. -/
structure FiniteADCBitVectorEnergyExecutionExactAt
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code)
    (execution : FiniteADCBitVectorEnergyExecution) : Prop where
  resistorNumeratorSigned :
    execution.resistorNumerator.toInt = roperational.val - rzero.val
  resistorSpanSigned :
    execution.resistorSpan.toInt = rspan.val - rzero.val
  inductorNumeratorSigned :
    execution.inductorNumerator.toInt = loperational.val - lzero.val
  inductorSpanSigned :
    execution.inductorSpan.toInt = lspan.val - lzero.val
  resistorNumeratorSquaredExact :
    execution.resistorNumeratorSquared.toNat =
      ((roperational.val - rzero.val) ^ 2).toNat
  resistorSpanSquaredExact :
    execution.resistorSpanSquared.toNat =
      ((rspan.val - rzero.val) ^ 2).toNat
  inductorNumeratorSquaredExact :
    execution.inductorNumeratorSquared.toNat =
      ((loperational.val - lzero.val) ^ 2).toNat
  inductorSpanSquaredExact :
    execution.inductorSpanSquared.toNat =
      ((lspan.val - lzero.val) ^ 2).toNat
  thresholdDenominatorExact :
    execution.thresholdDenominator.toNat =
      (finiteADCEnergyIntegerLeft
        (rspan.val - rzero.val) (lspan.val - lzero.val)).toNat
  resistorEnergyTermExact :
    execution.resistorEnergyTerm.toNat =
      (((roperational.val - rzero.val) ^ 2 *
        (lspan.val - lzero.val) ^ 2)).toNat
  inductorEnergyTermExact :
    execution.inductorEnergyTerm.toNat =
      (((loperational.val - lzero.val) ^ 2 *
        (rspan.val - rzero.val) ^ 2)).toNat
  energySumExact :
    execution.energySum.toNat =
      (((roperational.val - rzero.val) ^ 2 *
          (lspan.val - lzero.val) ^ 2 +
        (loperational.val - lzero.val) ^ 2 *
          (rspan.val - rzero.val) ^ 2)).toNat
  scaledEnergyNumeratorExact :
    execution.scaledEnergyNumerator.toNat =
      (finiteADCEnergyIntegerRight
        (roperational.val - rzero.val) (rspan.val - rzero.val)
        (loperational.val - lzero.val) (lspan.val - lzero.val)).toNat
  thresholdDenominatorNoUnsignedOverflow :
    execution.resistorSpanSquared.umulOverflow execution.inductorSpanSquared = false
  resistorEnergyTermNoUnsignedOverflow :
    execution.resistorNumeratorSquared.umulOverflow execution.inductorSpanSquared = false
  inductorEnergyTermNoUnsignedOverflow :
    execution.inductorNumeratorSquared.umulOverflow execution.resistorSpanSquared = false
  energySumNoUnsignedOverflow :
    execution.resistorEnergyTerm.uaddOverflow execution.inductorEnergyTerm = false
  scaleByFourNoUnsignedOverflow :
    (BitVec.ofNat 128 4).umulOverflow execution.energySum = false

theorem finiteADCBitVectorEnergyExecute_exact
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) :
    FiniteADCBitVectorEnergyExecutionExactAt
      code rzero rspan roperational lzero lspan loperational
      (finiteADCBitVectorEnergyExecute
        code rzero rspan roperational lzero lspan loperational) := by
  let rn : Int := roperational.val - rzero.val
  let rd : Int := rspan.val - rzero.val
  let ln : Int := loperational.val - lzero.val
  let ld : Int := lspan.val - lzero.val
  have rnBound : |rn| ≤ 32000000 :=
    finiteADCWord_difference_abs_le code roperational rzero
  have rdBound : |rd| ≤ 32000000 :=
    finiteADCWord_difference_abs_le code rspan rzero
  have lnBound : |ln| ≤ 32000000 :=
    finiteADCWord_difference_abs_le code loperational lzero
  have ldBound : |ld| ≤ 32000000 :=
    finiteADCWord_difference_abs_le code lspan lzero
  have bounds := finiteADCEnergyInteger_bounds rn rd ln ld
    rnBound rdBound lnBound ldBound
  have rnSquareBV :
      BitVec.ofInt 128 rn * BitVec.ofInt 128 rn = BitVec.ofInt 128 (rn ^ 2) :=
    finiteADCBitVectorSquare128_eq_ofInt rn
  have rdSquareBV :
      BitVec.ofInt 128 rd * BitVec.ofInt 128 rd = BitVec.ofInt 128 (rd ^ 2) :=
    finiteADCBitVectorSquare128_eq_ofInt rd
  have lnSquareBV :
      BitVec.ofInt 128 ln * BitVec.ofInt 128 ln = BitVec.ofInt 128 (ln ^ 2) :=
    finiteADCBitVectorSquare128_eq_ofInt ln
  have ldSquareBV :
      BitVec.ofInt 128 ld * BitVec.ofInt 128 ld = BitVec.ofInt 128 (ld ^ 2) :=
    finiteADCBitVectorSquare128_eq_ofInt ld
  have denominatorBV :
      (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd) *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) =
        BitVec.ofInt 128 (rd ^ 2 * ld ^ 2) := by
    rw [rdSquareBV, ldSquareBV, ← BitVec.ofInt_mul]
  have resistorTermBV :
      (BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) =
        BitVec.ofInt 128 (rn ^ 2 * ld ^ 2) := by
    rw [rnSquareBV, ldSquareBV, ← BitVec.ofInt_mul]
  have inductorTermBV :
      (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
          (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd) =
        BitVec.ofInt 128 (ln ^ 2 * rd ^ 2) := by
    rw [lnSquareBV, rdSquareBV, ← BitVec.ofInt_mul]
  have energySumBV :
      (BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
            (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) +
          (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
            (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd) =
        BitVec.ofInt 128 (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2) := by
    rw [resistorTermBV, inductorTermBV, ← BitVec.ofInt_add]
  have scaledBV :
      BitVec.ofNat 128 4 *
          ((BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
              (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) +
            (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
              (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd)) =
        BitVec.ofInt 128 (4 * (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2)) := by
    rw [energySumBV]
    change BitVec.ofInt 128 4 *
        BitVec.ofInt 128 (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2) = _
    rw [← BitVec.ofInt_mul]
  have termRNonnegative : 0 ≤ rn ^ 2 * ld ^ 2 :=
    mul_nonneg (sq_nonneg rn) (sq_nonneg ld)
  have termLNonnegative : 0 ≤ ln ^ 2 * rd ^ 2 :=
    mul_nonneg (sq_nonneg ln) (sq_nonneg rd)
  have sumNonnegative : 0 ≤ rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2 :=
    add_nonneg termRNonnegative termLNonnegative
  have termRLt : rn ^ 2 * ld ^ 2 < 2 ^ 128 := by
    unfold finiteADCEnergyIntegerRight at bounds
    nlinarith
  have termLLt : ln ^ 2 * rd ^ 2 < 2 ^ 128 := by
    unfold finiteADCEnergyIntegerRight at bounds
    nlinarith
  have sumLt : rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2 < 2 ^ 128 := by
    unfold finiteADCEnergyIntegerRight at bounds
    nlinarith
  have rnSquareExact := finiteADCBitVectorSignedSquare128_toNat_exact rn rnBound
  have rdSquareExact := finiteADCBitVectorSignedSquare128_toNat_exact rd rdBound
  have lnSquareExact := finiteADCBitVectorSignedSquare128_toNat_exact ln lnBound
  have ldSquareExact := finiteADCBitVectorSignedSquare128_toNat_exact ld ldBound
  have denominatorExact :
      ((BitVec.ofInt 128 rd * BitVec.ofInt 128 rd) *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld)).toNat =
        (rd ^ 2 * ld ^ 2).toNat := by
    rw [denominatorBV]
    exact bitVector128_ofInt_toNat_exact _ bounds.1.1 bounds.1.2
  have resistorTermExact :
      ((BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld)).toNat =
        (rn ^ 2 * ld ^ 2).toNat := by
    rw [resistorTermBV]
    exact bitVector128_ofInt_toNat_exact _ termRNonnegative termRLt
  have inductorTermExact :
      ((BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
          (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd)).toNat =
        (ln ^ 2 * rd ^ 2).toNat := by
    rw [inductorTermBV]
    exact bitVector128_ofInt_toNat_exact _ termLNonnegative termLLt
  have energySumExact :
      ((BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
            (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) +
          (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
            (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd)).toNat =
        (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2).toNat := by
    rw [energySumBV]
    exact bitVector128_ofInt_toNat_exact _ sumNonnegative sumLt
  have scaledExact :
      (BitVec.ofNat 128 4 *
          ((BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
              (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) +
            (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
              (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd))).toNat =
        (4 * (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2)).toNat := by
    rw [scaledBV]
    exact bitVector128_ofInt_toNat_exact _ bounds.2.1 (by
      simpa [finiteADCEnergyIntegerRight] using bounds.2.2)
  have denominatorNatLt : (rd ^ 2 * ld ^ 2).toNat < 2 ^ 128 :=
    (Int.toNat_lt bounds.1.1).mpr (by exact_mod_cast bounds.1.2)
  have termRNatLt : (rn ^ 2 * ld ^ 2).toNat < 2 ^ 128 :=
    (Int.toNat_lt termRNonnegative).mpr (by exact_mod_cast termRLt)
  have termLNatLt : (ln ^ 2 * rd ^ 2).toNat < 2 ^ 128 :=
    (Int.toNat_lt termLNonnegative).mpr (by exact_mod_cast termLLt)
  have sumNatLt :
      (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2).toNat < 2 ^ 128 :=
    (Int.toNat_lt sumNonnegative).mpr (by exact_mod_cast sumLt)
  have scaledNatLt :
      (4 * (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2)).toNat < 2 ^ 128 :=
    (Int.toNat_lt bounds.2.1).mpr (by
      exact_mod_cast (show
        finiteADCEnergyIntegerRight rn rd ln ld < (2 : Int) ^ 128 from
          bounds.2.2))
  refine {
    resistorNumeratorSigned := ?_
    resistorSpanSigned := ?_
    inductorNumeratorSigned := ?_
    inductorSpanSigned := ?_
    resistorNumeratorSquaredExact := ?_
    resistorSpanSquaredExact := ?_
    inductorNumeratorSquaredExact := ?_
    inductorSpanSquaredExact := ?_
    thresholdDenominatorExact := ?_
    resistorEnergyTermExact := ?_
    inductorEnergyTermExact := ?_
    energySumExact := ?_
    scaledEnergyNumeratorExact := ?_
    thresholdDenominatorNoUnsignedOverflow := ?_
    resistorEnergyTermNoUnsignedOverflow := ?_
    inductorEnergyTermNoUnsignedOverflow := ?_
    energySumNoUnsignedOverflow := ?_
    scaleByFourNoUnsignedOverflow := ?_ }
  · exact finiteADCBitVectorDifference128_toInt roperational rzero
  · exact finiteADCBitVectorDifference128_toInt rspan rzero
  · exact finiteADCBitVectorDifference128_toInt loperational lzero
  · exact finiteADCBitVectorDifference128_toInt lspan lzero
  · simpa [finiteADCBitVectorEnergyExecute, rn] using rnSquareExact
  · simpa [finiteADCBitVectorEnergyExecute, rd] using rdSquareExact
  · simpa [finiteADCBitVectorEnergyExecute, ln] using lnSquareExact
  · simpa [finiteADCBitVectorEnergyExecute, ld] using ldSquareExact
  · simpa [finiteADCBitVectorEnergyExecute,
      finiteADCEnergyIntegerLeft, rd, ld] using denominatorExact
  · simpa [finiteADCBitVectorEnergyExecute, rn, ld] using resistorTermExact
  · simpa [finiteADCBitVectorEnergyExecute, ln, rd] using inductorTermExact
  · simpa [finiteADCBitVectorEnergyExecute, rn, rd, ln, ld] using energySumExact
  · simpa [finiteADCBitVectorEnergyExecute,
      finiteADCEnergyIntegerRight, rn, rd, ln, ld] using scaledExact
  · simp only [finiteADCBitVectorEnergyExecute,
      finiteADCBitVectorDifference128_eq_ofInt, BitVec.umulOverflow]
    apply decide_eq_false_iff_not.mpr
    intro overflow
    change
      (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd).toNat *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld).toNat ≥ 2 ^ 128
      at overflow
    rw [rdSquareExact, ldSquareExact,
      ← Int.toNat_mul (sq_nonneg rd) (sq_nonneg ld)] at overflow
    omega
  · simp only [finiteADCBitVectorEnergyExecute,
      finiteADCBitVectorDifference128_eq_ofInt, BitVec.umulOverflow]
    apply decide_eq_false_iff_not.mpr
    intro overflow
    change
      (BitVec.ofInt 128 rn * BitVec.ofInt 128 rn).toNat *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld).toNat ≥ 2 ^ 128
      at overflow
    rw [rnSquareExact, ldSquareExact,
      ← Int.toNat_mul (sq_nonneg rn) (sq_nonneg ld)] at overflow
    omega
  · simp only [finiteADCBitVectorEnergyExecute,
      finiteADCBitVectorDifference128_eq_ofInt, BitVec.umulOverflow]
    apply decide_eq_false_iff_not.mpr
    intro overflow
    change
      (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln).toNat *
          (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd).toNat ≥ 2 ^ 128
      at overflow
    rw [lnSquareExact, rdSquareExact,
      ← Int.toNat_mul (sq_nonneg ln) (sq_nonneg rd)] at overflow
    omega
  · simp only [finiteADCBitVectorEnergyExecute,
      finiteADCBitVectorDifference128_eq_ofInt, BitVec.uaddOverflow]
    apply decide_eq_false_iff_not.mpr
    intro overflow
    change
      ((BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
          (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld)).toNat +
        ((BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
          (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd)).toNat ≥ 2 ^ 128
      at overflow
    rw [resistorTermExact, inductorTermExact,
      ← Int.toNat_add termRNonnegative termLNonnegative] at overflow
    omega
  · simp only [finiteADCBitVectorEnergyExecute,
      finiteADCBitVectorDifference128_eq_ofInt, BitVec.umulOverflow]
    apply decide_eq_false_iff_not.mpr
    intro overflow
    change
      4 *
        ((BitVec.ofInt 128 rn * BitVec.ofInt 128 rn) *
            (BitVec.ofInt 128 ld * BitVec.ofInt 128 ld) +
          (BitVec.ofInt 128 ln * BitVec.ofInt 128 ln) *
            (BitVec.ofInt 128 rd * BitVec.ofInt 128 rd)).toNat ≥ 2 ^ 128
      at overflow
    rw [energySumExact] at overflow
    have scaledToNat :
        (4 * (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2) : Int).toNat =
          4 * (rn ^ 2 * ld ^ 2 + ln ^ 2 * rd ^ 2).toNat := by
      simpa using Int.toNat_mul (by norm_num : (0 : Int) ≤ 4) sumNonnegative
    rw [← scaledToNat] at overflow
    omega

/-- The fixed-width circuit has exactly the same decision as the previously
verified bounded-integer ADC comparator, for every six-word input. -/
theorem finiteADCBitVectorEnergyCircuit_exact
    (code : FiniteADCResolutionCode)
    (rzero rspan roperational lzero lspan loperational : FiniteADCWord code) :
    finiteADCBitVectorEnergyCircuit
        code rzero rspan roperational lzero lspan loperational =
      finiteADCWordEnergyDecision128
        code rzero rspan roperational lzero lspan loperational := by
  rw [finiteADCWordEnergyDecision128_exact, Bool.eq_iff_iff]
  simp only [finiteADCBitVectorEnergyCircuit, finiteADCBitVectorEnergyRead,
    Bool.and_eq_true, BitVec.slt, BitVec.ult, decide_eq_true_eq,
    finiteADCEnergyIntegerAboveQuarter]
  have exact := finiteADCBitVectorEnergyExecute_exact
    code rzero rspan roperational lzero lspan loperational
  rw [exact.resistorSpanSigned, exact.inductorSpanSigned,
    exact.thresholdDenominatorExact, exact.scaledEnergyNumeratorExact]
  have leftNonnegative :
      0 ≤ finiteADCEnergyIntegerLeft
        (rspan.val - rzero.val) (lspan.val - lzero.val) :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have compare :
      (finiteADCEnergyIntegerLeft
          (rspan.val - rzero.val) (lspan.val - lzero.val)).toNat <
          (finiteADCEnergyIntegerRight
            (roperational.val - rzero.val) (rspan.val - rzero.val)
            (loperational.val - lzero.val) (lspan.val - lzero.val)).toNat ↔
        finiteADCEnergyIntegerLeft
            (rspan.val - rzero.val) (lspan.val - lzero.val) <
          finiteADCEnergyIntegerRight
            (roperational.val - rzero.val) (rspan.val - rzero.val)
            (loperational.val - lzero.val) (lspan.val - lzero.val) := by
    omega
  rw [compare]
  simp [and_assoc]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
