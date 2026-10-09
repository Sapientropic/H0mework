import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CommonCarrier
import H0mework.Versions.V2.Arithmetic.FockResponsibility.DirectActuality

/-!
# Direct midpoint production for the exact Goldbach Fourier coefficient

At the fixed exact-even occurrence, the source-generated Fourier coefficient
splits into the midpoint prime norm-square and a nonnegative off-diagonal
coupling.  A source-generated prime midpoint therefore produces a direct
`PrimePairActualitySettlementAt`; no fibre witness, process gate, or branch
classifier is supplied to the construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockExactFourierMidpointProducer

open CanonicalUnitArithmeticCommonCarrier
open ArithmeticGeneration
open GoldbachPrimePairTrace
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDirect
open ParticleWaveFockRuntimeExactPrimeFourierSibling

noncomputable section

def primeOnlyMidpointOffDiagonal (half : Nat) : ℝ :=
  ∑ left ∈ (Finset.Ico 1 (2 * half)).erase half,
    primeVonMangoldtWeight left *
      primeVonMangoldtWeight (2 * half - left)

theorem primeOnlyMidpointOffDiagonal_nonneg (half : Nat) :
    0 ≤ primeOnlyMidpointOffDiagonal half := by
  unfold primeOnlyMidpointOffDiagonal
  exact Finset.sum_nonneg fun left _leftMem =>
    mul_nonneg (primeVonMangoldtWeight_nonneg left)
      (primeVonMangoldtWeight_nonneg (2 * half - left))

/-- The exact even coefficient is a midpoint norm-square plus the genuinely
off-diagonal prime/complement coupling. -/
theorem primeOnlyGoldbachCorrelation_two_mul_eq_midpoint_sq_add_offDiagonal
    {half : Nat} (halfPositive : 0 < half) :
    primeOnlyGoldbachCorrelation (2 * half) =
      primeVonMangoldtWeight half ^ 2 +
        primeOnlyMidpointOffDiagonal half := by
  have halfMem : half ∈ Finset.Ico 1 (2 * half) := by
    rw [Finset.mem_Ico]
    omega
  rw [primeOnlyGoldbachCorrelation, natPairCorrelation,
    ← Finset.sum_erase_add _ _ halfMem]
  unfold primeOnlyMidpointOffDiagonal
  have reflectedHalf : 2 * half - half = half := by omega
  rw [reflectedHalf, pow_two, add_comm]

theorem runtimePrimeOnlyFourierCoefficient_eq_exactPrimeCorrelation
    (depth : Nat) :
    runtimePrimeOnlyFourierCoefficient depth =
      (primeOnlyGoldbachCorrelation (runtimeEvenTarget depth) : ℂ) := by
  rw [← runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient,
    runtimePrimeOnlyWeightedNaturalCorrelation_eq_exact,
    exactPrimeOnlyComplexCorrelation_eq_cast]

/-- Source formula at the emitted exact-even occurrence. -/
theorem runtimePrimeOnlyFourierCoefficient_eq_midpoint_sq_add_offDiagonal
    (depth : Nat) :
    runtimePrimeOnlyFourierCoefficient depth =
      ((primeVonMangoldtWeight (depth + 2) ^ 2 +
          primeOnlyMidpointOffDiagonal (depth + 2) : ℝ) : ℂ) := by
  rw [runtimePrimeOnlyFourierCoefficient_eq_exactPrimeCorrelation,
    runtimeEvenTarget_eq,
    primeOnlyGoldbachCorrelation_two_mul_eq_midpoint_sq_add_offDiagonal]
  omega

theorem midpoint_sq_le_runtimePrimeOnlyFourierCoefficient_re
    (depth : Nat) :
    primeVonMangoldtWeight (depth + 2) ^ 2 ≤
      (runtimePrimeOnlyFourierCoefficient depth).re := by
  rw [runtimePrimeOnlyFourierCoefficient_eq_midpoint_sq_add_offDiagonal]
  simp only [Complex.ofReal_re]
  exact le_add_of_nonneg_right
    (primeOnlyMidpointOffDiagonal_nonneg (depth + 2))

theorem runtimePrimeOnlyFourierCoefficient_re_pos_of_midpoint_prime
    (depth : Nat) (midpointPrime : Nat.Prime (depth + 2)) :
    0 < (runtimePrimeOnlyFourierCoefficient depth).re := by
  have midpointWeightPositive :
      0 < primeVonMangoldtWeight (depth + 2) :=
    (primeVonMangoldtWeight_pos_iff (depth + 2)).2 midpointPrime
  have midpointSquarePositive :
      0 < primeVonMangoldtWeight (depth + 2) ^ 2 :=
    pow_pos midpointWeightPositive 2
  exact midpointSquarePositive.trans_le
    (midpoint_sq_le_runtimePrimeOnlyFourierCoefficient_re depth)

/-- A prime midpoint supplies a direct nonzero exact Fourier coefficient. -/
theorem runtimePrimeOnlyFourierCoefficient_ne_zero_of_midpoint_prime
    (depth : Nat) (midpointPrime : Nat.Prime (depth + 2)) :
    runtimePrimeOnlyFourierCoefficient depth ≠ 0 := by
  intro coefficientZero
  have positive :=
    runtimePrimeOnlyFourierCoefficient_re_pos_of_midpoint_prime
      depth midpointPrime
  rw [coefficientZero] at positive
  norm_num at positive

theorem runtimePrimeOnlyFourierCoefficient_im_eq_zero (depth : Nat) :
    (runtimePrimeOnlyFourierCoefficient depth).im = 0 := by
  rw [runtimePrimeOnlyFourierCoefficient_eq_midpoint_sq_add_offDiagonal]
  exact Complex.ofReal_im _

/-- At a composite midpoint, the remaining nonzero obligation is exactly the
positive off-diagonal additive coupling. -/
theorem runtimePrimeOnlyFourierCoefficient_ne_zero_iff_offDiagonal_pos
    (depth : Nat) (midpointComposite : ¬ Nat.Prime (depth + 2)) :
    runtimePrimeOnlyFourierCoefficient depth ≠ 0 ↔
      0 < primeOnlyMidpointOffDiagonal (depth + 2) := by
  rw [runtimePrimeOnlyFourierCoefficient_eq_midpoint_sq_add_offDiagonal,
    primeVonMangoldtWeight, if_neg midpointComposite]
  norm_num
  exact primeOnlyMidpointOffDiagonal_nonneg (depth + 2)

/-- Runtime depth whose exact target is twice the prime emitted at one
canonical Euler stage. -/
def generatedPrimeDiagonalDepth (stage : Nat) : Nat :=
  (primeAtStage stage : Nat) - 2

theorem generatedPrimeDiagonalDepth_add_two (stage : Nat) :
    generatedPrimeDiagonalDepth stage + 2 =
      (primeAtStage stage : Nat) := by
  exact Nat.sub_add_cancel (primeAtStage stage).property.two_le

theorem runtimeEvenTarget_generatedPrimeDiagonalDepth (stage : Nat) :
    runtimeEvenTarget (generatedPrimeDiagonalDepth stage) =
      (primeAtStage stage : Nat) + (primeAtStage stage : Nat) := by
  rw [runtimeEvenTarget_eq, generatedPrimeDiagonalDepth_add_two]
  omega

theorem runtimePrimeOnlyFourierCoefficient_generatedPrimeDiagonal_ne_zero
    (stage : Nat) :
    runtimePrimeOnlyFourierCoefficient
        (generatedPrimeDiagonalDepth stage) ≠ 0 := by
  apply runtimePrimeOnlyFourierCoefficient_ne_zero_of_midpoint_prime
  rw [generatedPrimeDiagonalDepth_add_two]
  exact (primeAtStage stage).property

theorem runtimePrimeOnlyFourierCoefficient_generatedPrimeDiagonal_re_pos
    (stage : Nat) :
    0 < (runtimePrimeOnlyFourierCoefficient
      (generatedPrimeDiagonalDepth stage)).re := by
  apply runtimePrimeOnlyFourierCoefficient_re_pos_of_midpoint_prime
  rw [generatedPrimeDiagonalDepth_add_two]
  exact (primeAtStage stage).property

/-- Fixed-root actuality settlement on the generated diagonal family. -/
theorem directRuntimeSettlement_generatedPrimeDiagonal
    (stage : Nat) :
    Nonempty (PrimePairActualitySettlementAt
      (directRuntimeActuality (generatedPrimeDiagonalDepth stage))) := by
  exact
    (directRuntimeSettlement_nonempty_iff_fourier_nonzero
      (generatedPrimeDiagonalDepth stage)).2
      (runtimePrimeOnlyFourierCoefficient_generatedPrimeDiagonal_ne_zero stage)

/-- Exact nonzero Fourier events occur beyond every prescribed runtime
depth, through the canonical Euler-prime lineage. -/
theorem exists_runtimePrimeOnlyFourierCoefficient_ne_zero_above
    (lower : Nat) :
    ∃ depth : Nat, lower ≤ depth ∧
      runtimePrimeOnlyFourierCoefficient depth ≠ 0 := by
  obtain ⟨primeValue, lowerPrime, primeProperty⟩ :=
    Nat.exists_infinite_primes (lower + 2)
  let prime : Nat.Primes := ⟨primeValue, primeProperty⟩
  let stage := stageOfPrime prime
  refine ⟨generatedPrimeDiagonalDepth stage, ?_,
    runtimePrimeOnlyFourierCoefficient_generatedPrimeDiagonal_ne_zero stage⟩
  have stagePrime : primeAtStage stage = prime :=
    primeAtStage_stageOfPrime prime
  rw [generatedPrimeDiagonalDepth, stagePrime]
  dsimp only [prime]
  omega

theorem exists_directRuntimeSettlement_above (lower : Nat) :
    ∃ depth : Nat, lower ≤ depth ∧
      Nonempty (PrimePairActualitySettlementAt
        (directRuntimeActuality depth)) := by
  obtain ⟨depth, lowerDepth, coefficientNonzero⟩ :=
    exists_runtimePrimeOnlyFourierCoefficient_ne_zero_above lower
  exact ⟨depth, lowerDepth,
    (directRuntimeSettlement_nonempty_iff_fourier_nonzero depth).2
      coefficientNonzero⟩

end
end ParticleWaveFockExactFourierMidpointProducer
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
