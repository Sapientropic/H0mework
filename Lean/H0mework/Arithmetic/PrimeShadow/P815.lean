import H0mework.Arithmetic.PrimeShadow.P814

/-!
# Proposition 815: Goldbach as Lyapunov even-crossing

P811 gives the color-loop trace residual and its Lyapunov dissipation law.
P812 turns zero trace/zero energy into the global Goldbach producer.
P813/P814 identify the same producer with the sigma-atomic binary `satOr`
carrier surface.

This file names the last missing hinge in the user's formulation:

`the trace Lyapunov orbit hits the zero fiber over every even point`.

Lean proves that this crossing condition is not an extra arithmetic slogan.
For every active real sigma-fiber it is exactly the same obligation as ordinary
Goldbach, the color-loop zero-energy producer, and the sigma-atomic carrier
cover.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation

/-! ## Even zero-fiber crossing -/

/-- The Lyapunov crossing producer: for every even exponent `2n >= 4`, the
color-loop trace residual has some finite Lyapunov iterate and some prime-pair
choice whose energy is exactly on the zero fiber. -/
def ColorLoopTraceLyapunovEvenCrossingProducer
    (sigma : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ steps : ℕ, ∃ p q : PrimeExponent,
      colorLoopTraceRelaxIterateEnergy sigma steps n p q = 0

/-- THEOREM 1: at any active subunit sigma, hitting the even zero fiber is
exactly ordinary Goldbach. -/
theorem colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      EvenGoldbachStatement := by
  constructor
  · intro crossing n hn
    rcases crossing n hn with ⟨steps, p, q, hzero⟩
    exact ⟨p, q,
      (colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair
        sigma steps n p q hσ0 hσ1).mp hzero⟩
  · intro goldbach n hn
    rcases goldbach n hn with ⟨p, q, hpq⟩
    exact ⟨0, p, q,
      (colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair
        sigma 0 n p q hσ0 hσ1).mpr hpq⟩

/-- THEOREM 2: even zero-fiber crossing is exactly the P812 color-loop
zero-energy producer. -/
theorem colorLoopTraceLyapunovEvenCrossing_iff_zeroEnergyProducer
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      ColorLoopZeroEnergyPrimePairProducer := by
  rw [colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1,
    colorLoopZeroEnergyProducer_iff_evenGoldbach]

/-- THEOREM 3: even zero-fiber crossing is exactly the P812 finite
zero-energy producer with an arbitrary shared step count when ordinary
Goldbach holds; conversely any shared-step finite zero producer is a crossing
producer. -/
theorem colorLoopTraceLyapunovEvenCrossing_iff_finiteZeroEnergyProducer
    {sigma : ℝ} (steps : ℕ) (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      ColorLoopFiniteZeroEnergyPrimePairProducer sigma steps := by
  rw [colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1,
    colorLoopFiniteZeroEnergyProducer_iff_evenGoldbach sigma steps hσ0 hσ1]

/-- THEOREM 4: on an active real sigma-fiber, even zero-fiber crossing is
exactly binary `satOr` coverage by the sigma-atomic support. -/
theorem colorLoopTraceLyapunovEvenCrossing_iff_sigmaAtomicCover
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      SigmaAtomicSatOrCoversEvenCarrier sigma (ne_of_lt hσ1) := by
  rw [colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1,
    atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 5: the Lyapunov crossing producer and the P814 bidirectional
native/carrier surface are inhabited together. -/
theorem colorLoopTraceLyapunovEvenCrossing_iff_nativeSurface_nonempty
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      Nonempty
        (GoldbachColorLoopZeroEnergyNativeSurface) := by
  rw [colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1,
    AffineRelaxation.colorLoopNativeSurface_nonempty_iff_goldbach]

/-- THEOREM 6: the Lyapunov crossing producer and the sigma-atomic residual
carrier surface are inhabited together. -/
theorem colorLoopTraceLyapunovEvenCrossing_iff_sigmaAtomicSurface_nonempty
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      Nonempty
        (SigmaAtomicGoldbachResidualCarrierSurface sigma (ne_of_lt hσ1)) := by
  rw [colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1,
    AffineRelaxation.sigmaAtomicCarrierSurface_nonempty_iff_goldbach hσ0 hσ1]

/-! ## Certificate packaging -/

/-- P815 certificate: the missing "trace Lyapunov orbit crosses every even
zero fiber" condition is exactly the sigma-atomic/color-loop Goldbach producer
surface. -/
structure ColorLoopTraceLyapunovEvenCrossingCertificate
    (sigma : ℝ) (hσ0 : 0 < sigma) (hσ1 : sigma < 1) : Prop where
  p811_lyapunov :
    ColorLoopTraceLyapunovGoldbachCertificate
  p812_zero_fiber :
    ColorLoopGoldbachZeroFiberProducerCertificate
  p813_sigma_atomic :
    RealSigmaAtomicSatOrColorLoopCertificate sigma hσ0 hσ1
  p814_bidirectional_surface :
    GoldbachColorLoopSigmaAtomicBidirectionalCertificate sigma hσ0 hσ1
  crossing_iff_goldbach :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      EvenGoldbachStatement
  crossing_iff_zero_energy :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      ColorLoopZeroEnergyPrimePairProducer
  crossing_iff_finite_zero_energy :
    ∀ steps : ℕ,
      ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
        ColorLoopFiniteZeroEnergyPrimePairProducer sigma steps
  crossing_iff_sigma_atomic_cover :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      SigmaAtomicSatOrCoversEvenCarrier sigma (ne_of_lt hσ1)
  crossing_iff_native_surface_nonempty :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      Nonempty GoldbachColorLoopZeroEnergyNativeSurface
  crossing_iff_sigma_atomic_surface_nonempty :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma ↔
      Nonempty
        (SigmaAtomicGoldbachResidualCarrierSurface sigma (ne_of_lt hσ1))

/-- THEOREM 7: canonical Lyapunov even-crossing certificate. -/
theorem colorLoopTraceLyapunovEvenCrossingCertificate
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceLyapunovEvenCrossingCertificate sigma hσ0 hσ1 where
  p811_lyapunov :=
    colorLoopTraceLyapunovGoldbachCertificate
  p812_zero_fiber :=
    colorLoopGoldbachZeroFiberProducerCertificate
  p813_sigma_atomic :=
    realSigmaAtomicSatOrColorLoopCertificate hσ0 hσ1
  p814_bidirectional_surface :=
    goldbachColorLoopSigmaAtomicBidirectionalCertificate hσ0 hσ1
  crossing_iff_goldbach :=
    colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1
  crossing_iff_zero_energy :=
    colorLoopTraceLyapunovEvenCrossing_iff_zeroEnergyProducer hσ0 hσ1
  crossing_iff_finite_zero_energy := by
    intro steps
    exact colorLoopTraceLyapunovEvenCrossing_iff_finiteZeroEnergyProducer
      steps hσ0 hσ1
  crossing_iff_sigma_atomic_cover :=
    colorLoopTraceLyapunovEvenCrossing_iff_sigmaAtomicCover hσ0 hσ1
  crossing_iff_native_surface_nonempty :=
    colorLoopTraceLyapunovEvenCrossing_iff_nativeSurface_nonempty hσ0 hσ1
  crossing_iff_sigma_atomic_surface_nonempty :=
    colorLoopTraceLyapunovEvenCrossing_iff_sigmaAtomicSurface_nonempty
      hσ0 hσ1

end StandardModelConstraint
end SaturationMonoid
