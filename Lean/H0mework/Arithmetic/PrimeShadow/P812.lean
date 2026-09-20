import H0mework.Physics.ColorLoops.P811

/-!
# Proposition 812: global Goldbach as a color-loop zero-fiber producer

P811 proves the pointwise color-loop face:

* `trace diag(p,q,-2n) = p + q - 2n`;
* trace-zero is exactly the selected Goldbach pair equation;
* squared trace residual dissipates by P697's Lyapunov law.

This file closes the global formulation.  Ordinary Goldbach is equivalent to
the existence of a producer which, for every even exponent `2n`, selects a
prime pair in the color-loop trace-exact / zero-energy fiber.  For any
runtime rate `0 < sigma < 1`, the same statement is also equivalent to finite
zero of the relaxed Lyapunov energy.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open Filter
open SaturationMonoid.AffineRelaxation

/-! ## Global producer forms -/

/-- A global producer that chooses, for every even exponent `2n >= 4`, a prime
pair whose color-loop holonomy is trace-exact. -/
def ColorLoopTraceExactPrimePairProducer : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ p q : PrimeExponent,
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q)

/-- A global producer that chooses, for every even exponent `2n >= 4`, a prime
pair in the zero-energy fiber of the color-loop trace residual. -/
def ColorLoopZeroEnergyPrimePairProducer : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ p q : PrimeExponent,
      colorLoopTraceEnergy n p q = 0

/-- A global producer that chooses, for every even exponent `2n >= 4`, a prime
pair whose finite relaxed Lyapunov energy has reached the zero fiber. -/
def ColorLoopFiniteZeroEnergyPrimePairProducer
    (sigma : ℝ) (steps : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ p q : PrimeExponent,
      colorLoopTraceRelaxIterateEnergy sigma steps n p q = 0

/-! ## Equivalence with ordinary Goldbach -/

/-- THEOREM 1: the trace-exact color-loop producer is exactly ordinary
Goldbach. -/
theorem colorLoopTraceExactProducer_iff_evenGoldbach :
    ColorLoopTraceExactPrimePairProducer ↔
      AffineRelaxation.EvenGoldbachStatement := by
  constructor
  · intro producer n hn
    rcases producer n hn with ⟨p, q, hexact⟩
    exact ⟨p, q, (primeEdgeColorLoop_trace_zero_iff n p q).mp hexact⟩
  · intro goldbach n hn
    rcases goldbach n hn with ⟨p, q, hpq⟩
    exact ⟨p, q, (primeEdgeColorLoop_trace_zero_iff n p q).mpr hpq⟩

/-- THEOREM 2: the zero-energy color-loop producer is exactly ordinary
Goldbach. -/
theorem colorLoopZeroEnergyProducer_iff_evenGoldbach :
    ColorLoopZeroEnergyPrimePairProducer ↔
      AffineRelaxation.EvenGoldbachStatement := by
  constructor
  · intro producer n hn
    rcases producer n hn with ⟨p, q, henergy⟩
    exact ⟨p, q,
      (colorLoopTraceEnergy_zero_iff_goldbach_pair n p q).mp henergy⟩
  · intro goldbach n hn
    rcases goldbach n hn with ⟨p, q, hpq⟩
    exact ⟨p, q,
      (colorLoopTraceEnergy_zero_iff_goldbach_pair n p q).mpr hpq⟩

/-- THEOREM 3: at any active subunit rate, finite zero of the relaxed
color-loop Lyapunov energy is exactly ordinary Goldbach. -/
theorem colorLoopFiniteZeroEnergyProducer_iff_evenGoldbach
    (sigma : ℝ) (steps : ℕ) (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopFiniteZeroEnergyPrimePairProducer sigma steps ↔
      AffineRelaxation.EvenGoldbachStatement := by
  constructor
  · intro producer n hn
    rcases producer n hn with ⟨p, q, henergy⟩
    exact ⟨p, q,
      (colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair
        sigma steps n p q hσ0 hσ1).mp henergy⟩
  · intro goldbach n hn
    rcases goldbach n hn with ⟨p, q, hpq⟩
    exact ⟨p, q,
      (colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair
        sigma steps n p q hσ0 hσ1).mpr hpq⟩

/-- THEOREM 4: trace-exact and zero-energy producers are the same global
zero-fiber obligation. -/
theorem colorLoopTraceExactProducer_iff_zeroEnergyProducer :
    ColorLoopTraceExactPrimePairProducer ↔
      ColorLoopZeroEnergyPrimePairProducer := by
  rw [colorLoopTraceExactProducer_iff_evenGoldbach,
    colorLoopZeroEnergyProducer_iff_evenGoldbach]

/-- THEOREM 5: at any active subunit rate, finite relaxed zero-energy
producers are the same global zero-fiber obligation as trace-exact producers. -/
theorem colorLoopTraceExactProducer_iff_finiteZeroEnergyProducer
    (sigma : ℝ) (steps : ℕ) (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceExactPrimePairProducer ↔
      ColorLoopFiniteZeroEnergyPrimePairProducer sigma steps := by
  rw [colorLoopTraceExactProducer_iff_evenGoldbach,
    colorLoopFiniteZeroEnergyProducer_iff_evenGoldbach sigma steps hσ0 hσ1]

/-! ## Certificate packaging -/

/-- P812 certificate: global Goldbach is precisely the color-loop zero-fiber
producer obligation. -/
structure ColorLoopGoldbachZeroFiberProducerCertificate : Prop where
  p811_color_loop_lyapunov :
    ColorLoopTraceLyapunovGoldbachCertificate
  trace_exact_producer_iff_goldbach :
    ColorLoopTraceExactPrimePairProducer ↔
      AffineRelaxation.EvenGoldbachStatement
  zero_energy_producer_iff_goldbach :
    ColorLoopZeroEnergyPrimePairProducer ↔
      AffineRelaxation.EvenGoldbachStatement
  finite_zero_energy_producer_iff_goldbach :
    ∀ (sigma : ℝ) (steps : ℕ), 0 < sigma -> sigma < 1 ->
      (ColorLoopFiniteZeroEnergyPrimePairProducer sigma steps ↔
        AffineRelaxation.EvenGoldbachStatement)
  trace_exact_iff_zero_energy_producer :
    ColorLoopTraceExactPrimePairProducer ↔
      ColorLoopZeroEnergyPrimePairProducer
  trace_exact_iff_finite_zero_energy_producer :
    ∀ (sigma : ℝ) (steps : ℕ), 0 < sigma -> sigma < 1 ->
      (ColorLoopTraceExactPrimePairProducer ↔
        ColorLoopFiniteZeroEnergyPrimePairProducer sigma steps)

/-- THEOREM 6: the global color-loop zero-fiber producer certificate. -/
theorem colorLoopGoldbachZeroFiberProducerCertificate :
    ColorLoopGoldbachZeroFiberProducerCertificate where
  p811_color_loop_lyapunov :=
    colorLoopTraceLyapunovGoldbachCertificate
  trace_exact_producer_iff_goldbach :=
    colorLoopTraceExactProducer_iff_evenGoldbach
  zero_energy_producer_iff_goldbach :=
    colorLoopZeroEnergyProducer_iff_evenGoldbach
  finite_zero_energy_producer_iff_goldbach :=
    colorLoopFiniteZeroEnergyProducer_iff_evenGoldbach
  trace_exact_iff_zero_energy_producer :=
    colorLoopTraceExactProducer_iff_zeroEnergyProducer
  trace_exact_iff_finite_zero_energy_producer :=
    colorLoopTraceExactProducer_iff_finiteZeroEnergyProducer

end StandardModelConstraint
end SaturationMonoid
