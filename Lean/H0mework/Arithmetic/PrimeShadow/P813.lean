import H0mework.Arithmetic.PrimeShadow.P812

/-!
# Proposition 813: sigma-atomic satOr cover as the Goldbach producer

Complement is too coarse to move multiplicative prime factorization into a
two-prime additive decomposition.  The sharper sigma-carrier object is the
binary `satOr` image of the sigma-atomic support:

`atomic σ × atomic σ -> even carrier`.

This file proves the exact cost of that cover.  On any nondegenerate fiber
`0 < σ < 1`, the statement that every even carrier point lies in the binary
`satOr` image of the sigma-atomic support is equivalent to ordinary Goldbach.
It is also equivalent to the P812 color-loop zero-energy producer.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra
open StandardModelConstraint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Atomic satOr cover of even carrier points -/

/-- The sigma-atomic binary `satOr` cover condition: every even effective-rate
carrier point is the serial composition of two untagged sigma-atomic rates. -/
def SigmaAtomicSatOrCoversEvenCarrier
    (σ : K) (hσ : σ ≠ 1) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ a b : SigmaAtomicRateSupport σ hσ,
      iteratedRate σ (2 * n) =
        satOrField a.1.1 b.1.1

/-- THEOREM 1: the atomic support cover implies the usual sigma-Goldbach
statement, because each untagged atomic support element reads back to a prime
exponent. -/
theorem sigmaEvenGoldbach_of_atomicSatOrCover
    {σ : K} {hσ : σ ≠ 1}
    (cover : SigmaAtomicSatOrCoversEvenCarrier σ hσ) :
    SigmaEvenGoldbachStatement σ := by
  intro n hn
  rcases cover n hn with ⟨a, b, hab⟩
  refine ⟨a.toPrimeExponent, b.toPrimeExponent, ?_⟩
  have ha :
      a.1.1 = iteratedRate σ a.toPrimeExponent.1 := by
    have h := congrArg Subtype.val a.eq_iterated_exponent
    simpa [SigmaAtomicRateSupport.toPrimeExponent] using h
  have hb :
      b.1.1 = iteratedRate σ b.toPrimeExponent.1 := by
    have h := congrArg Subtype.val b.eq_iterated_exponent
    simpa [SigmaAtomicRateSupport.toPrimeExponent] using h
  simpa [ha, hb] using hab

/-- THEOREM 2: sigma-Goldbach supplies an atomic support cover by mapping the
two prime exponents into the sigma-atomic support. -/
theorem atomicSatOrCover_of_sigmaEvenGoldbach
    {σ : K} {hσ : σ ≠ 1}
    (hgoldbach : SigmaEvenGoldbachStatement σ) :
    SigmaAtomicSatOrCoversEvenCarrier σ hσ := by
  intro n hn
  rcases hgoldbach n hn with ⟨p, q, hpq⟩
  refine ⟨primeToSigmaAtomicRateSupport σ hσ p,
    primeToSigmaAtomicRateSupport σ hσ q, ?_⟩
  simpa [primeToSigmaAtomicRateSupport] using hpq

/-- THEOREM 3: atomic support cover is exactly sigma-Goldbach. -/
theorem atomicSatOrCover_iff_sigmaEvenGoldbach
    {σ : K} {hσ : σ ≠ 1} :
    SigmaAtomicSatOrCoversEvenCarrier σ hσ ↔
      SigmaEvenGoldbachStatement σ := by
  constructor
  · exact sigmaEvenGoldbach_of_atomicSatOrCover
  · exact atomicSatOrCover_of_sigmaEvenGoldbach

/-- THEOREM 4: on `0 < σ < 1`, the sigma-atomic binary `satOr` cover is
exactly ordinary Goldbach. -/
theorem atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      EvenGoldbachStatement := by
  rw [atomicSatOrCover_iff_sigmaEvenGoldbach,
    sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1]

/-- A multiplicative-factorization-to-atomic-satOr transfer has exactly the
same strength as a multiplicative-factorization-to-Goldbach transfer. -/
theorem multiplicativeToAtomicSatOrCoverTransfer_iff_fta_to_goldbach
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (PrimeMultiplicativeFactorizationStatement ->
        SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1)) ↔
      (PrimeMultiplicativeFactorizationStatement ->
        EvenGoldbachStatement) := by
  constructor
  · intro h hfta
    exact (atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mp
      (h hfta)
  · intro h hfta
    exact (atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mpr
      (h hfta)

/-! ## Weld to the color-loop zero-energy face -/

/-- THEOREM 6: on the real nondegenerate carrier, the sigma-atomic binary
cover is exactly the color-loop zero-energy producer. -/
theorem realAtomicSatOrCover_iff_colorLoopZeroEnergyProducer
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      ColorLoopZeroEnergyPrimePairProducer := by
  rw [atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1,
    colorLoopZeroEnergyProducer_iff_evenGoldbach]

/-- THEOREM 7: on the real nondegenerate carrier, the sigma-atomic binary
cover is exactly the finite relaxed color-loop zero-energy producer. -/
theorem realAtomicSatOrCover_iff_colorLoopFiniteZeroEnergyProducer
    {σ : ℝ} (steps : ℕ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      ColorLoopFiniteZeroEnergyPrimePairProducer σ steps := by
  rw [atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1,
    colorLoopFiniteZeroEnergyProducer_iff_evenGoldbach σ steps hσ0 hσ1]

/-! ## Certificate packaging -/

/-- P813 certificate: the sharper sigma-carrier producer is binary `satOr`
coverage by sigma-atomic support, and its exact strength is Goldbach. -/
structure SigmaAtomicSatOrCoverGoldbachCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) : Prop where
  atomic_cover_iff_sigma_goldbach :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      SigmaEvenGoldbachStatement σ
  atomic_cover_iff_goldbach :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      EvenGoldbachStatement
  multiplicative_transfer_iff :
    (PrimeMultiplicativeFactorizationStatement ->
        SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1)) ↔
      (PrimeMultiplicativeFactorizationStatement ->
        EvenGoldbachStatement)

/-- THEOREM 8: canonical certificate for any nondegenerate ordered-field
sigma-carrier. -/
theorem sigmaAtomicSatOrCoverGoldbachCertificate
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaAtomicSatOrCoverGoldbachCertificate σ hσ0 hσ1 where
  atomic_cover_iff_sigma_goldbach :=
    atomicSatOrCover_iff_sigmaEvenGoldbach
  atomic_cover_iff_goldbach :=
    atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1
  multiplicative_transfer_iff :=
    multiplicativeToAtomicSatOrCoverTransfer_iff_fta_to_goldbach hσ0 hσ1

/-- P813 real certificate also names the color-loop zero-energy face. -/
structure RealSigmaAtomicSatOrColorLoopCertificate
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) : Prop where
  sigma_atomic_cover :
    SigmaAtomicSatOrCoverGoldbachCertificate σ hσ0 hσ1
  cover_iff_color_loop_zero_energy :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      ColorLoopZeroEnergyPrimePairProducer
  cover_iff_color_loop_finite_zero_energy :
    ∀ steps : ℕ,
      SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
        ColorLoopFiniteZeroEnergyPrimePairProducer σ steps

/-- THEOREM 9: the real sigma-atomic cover is the same producer as the
color-loop zero-energy Lyapunov face. -/
theorem realSigmaAtomicSatOrColorLoopCertificate
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    RealSigmaAtomicSatOrColorLoopCertificate σ hσ0 hσ1 where
  sigma_atomic_cover :=
    sigmaAtomicSatOrCoverGoldbachCertificate hσ0 hσ1
  cover_iff_color_loop_zero_energy :=
    realAtomicSatOrCover_iff_colorLoopZeroEnergyProducer hσ0 hσ1
  cover_iff_color_loop_finite_zero_energy := by
    intro steps
    exact realAtomicSatOrCover_iff_colorLoopFiniteZeroEnergyProducer
      steps hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
