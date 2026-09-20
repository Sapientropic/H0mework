import H0mework.Arithmetic.GoldbachFourier.PairCarrier
import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite Fourier identity for ordered pair correlation

The identity is proved on the finite cyclic group `ZMod modulus`, using
Mathlib's discrete Fourier transform.  It is an exact finite theorem: the DFT
of ordered pair correlation is the square of the DFT of the weight, and
Fourier inversion recovers each cyclic pair coefficient.

No analytic estimate and no Goldbach existence claim appears in this file.
Transport from a natural truncation to the cyclic carrier requires an explicit
no-wrap equality; that bridge is represented separately below.
-/

noncomputable section

open Finset AddChar ZMod
open scoped BigOperators ZMod

namespace GoldbachPrimePairTrace

variable {modulus : ℕ} [NeZero modulus]

/-! ## Cyclic pair carrier -/

/-- Additive pair geometry on the finite cyclic group. -/
def cyclicPairGeometry :
    AdditivePairGeometry (ZMod modulus) (ZMod modulus) where
  indexEnergy x := x

/-- Exact cyclic pair fiber over one residue. -/
abbrev CyclicPairFiber (target : ZMod modulus) :=
  AdditivePairGeometry.Fiber (cyclicPairGeometry (modulus := modulus)) target

/-- Ordered cyclic pair correlation.  For each left endpoint there is a
unique right endpoint `target - left`. -/
def cyclicPairCorrelation
    (weight : ZMod modulus → ℂ) (target : ZMod modulus) : ℂ :=
  ∑ left : ZMod modulus, weight left * weight (target - left)

/-- The finite prime/exponential sum is exactly Mathlib's DFT, with its
negative-phase convention. -/
def finiteExponentialSum
    (weight : ZMod modulus → ℂ) (frequency : ZMod modulus) : ℂ :=
  𝓕 weight frequency

/-! ## Convolution-square identity -/

/-- Translation by subtraction on an additive group. -/
private def subRightEquiv {G : Type*} [AddGroup G] (a : G) : G ≃ G where
  toFun x := x - a
  invFun x := x + a
  left_inv x := sub_add_cancel x a
  right_inv x := add_sub_cancel_right x a

/-- The DFT of cyclic ordered-pair correlation is the square of the DFT of
the endpoint weight. -/
theorem dft_cyclicPairCorrelation
    (weight : ZMod modulus → ℂ) (frequency : ZMod modulus) :
    𝓕 (cyclicPairCorrelation weight) frequency =
      (finiteExponentialSum weight frequency) ^ 2 := by
  simp only [ZMod.dft_apply, cyclicPairCorrelation, finiteExponentialSum,
    smul_eq_mul, pow_two, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Fintype.sum_equiv (subRightEquiv left)
  intro total
  rw [show (subRightEquiv left) total = total - left by rfl]
  change
    stdAddChar (-(total * frequency)) *
        (weight left * weight (total - left)) =
      (stdAddChar (-((total - left) * frequency)) *
          weight (total - left)) *
        (stdAddChar (-(left * frequency)) * weight left)
  rw [show -(total * frequency) =
      -((total - left) * frequency) + -(left * frequency) by ring]
  rw [map_add_eq_mul]
  ring

/-- Exact finite Fourier coefficient identity for cyclic pair correlation. -/
theorem cyclicPairCorrelation_eq_fourierCoefficient
    (weight : ZMod modulus → ℂ) (target : ZMod modulus) :
    cyclicPairCorrelation weight target =
      (modulus : ℂ)⁻¹ *
        ∑ frequency : ZMod modulus,
          stdAddChar (frequency * target) *
            (finiteExponentialSum weight frequency) ^ 2 := by
  have hdft :
      𝓕 (cyclicPairCorrelation weight) =
        fun frequency : ZMod modulus =>
          (finiteExponentialSum weight frequency) ^ 2 := by
    funext frequency
    exact dft_cyclicPairCorrelation weight frequency
  calc
    cyclicPairCorrelation weight target =
        𝓕⁻ (𝓕 (cyclicPairCorrelation weight)) target := by
      rw [LinearEquiv.symm_apply_apply]
    _ = 𝓕⁻
        (fun frequency : ZMod modulus =>
          (finiteExponentialSum weight frequency) ^ 2) target := by
      rw [hdft]
    _ = (modulus : ℂ)⁻¹ *
          ∑ frequency : ZMod modulus,
            stdAddChar (frequency * target) *
              (finiteExponentialSum weight frequency) ^ 2 := by
      rw [ZMod.invDFT_apply]
      simp only [smul_eq_mul]

/-! ## Explicit natural-to-cyclic no-wrap boundary -/

/-- Data required to identify one natural finite correlation with a cyclic
correlation.  The equality is kept explicit because modular equality can wrap;
the finite Fourier theorem itself must not silently replace natural addition
by addition modulo `modulus`. -/
structure NaturalCyclicNoWrapAdapter
    (weight : ℕ → ℂ) (target modulus : ℕ) [NeZero modulus] where
  cyclicWeight : ZMod modulus → ℂ
  correlation_eq :
    natPairCorrelation weight target =
      cyclicPairCorrelation cyclicWeight (target : ZMod modulus)

/-- A proved no-wrap adapter transports the exact cyclic Fourier identity to
the corresponding natural finite correlation. -/
theorem natPairCorrelation_eq_fourierCoefficient_of_noWrap
    {weight : ℕ → ℂ} {target modulus : ℕ} [NeZero modulus]
    (adapter : NaturalCyclicNoWrapAdapter weight target modulus) :
    natPairCorrelation weight target =
      (modulus : ℂ)⁻¹ *
        ∑ frequency : ZMod modulus,
          stdAddChar (frequency * (target : ZMod modulus)) *
            (finiteExponentialSum adapter.cyclicWeight frequency) ^ 2 := by
  rw [adapter.correlation_eq]
  exact cyclicPairCorrelation_eq_fourierCoefficient
    adapter.cyclicWeight (target : ZMod modulus)

end GoldbachPrimePairTrace
