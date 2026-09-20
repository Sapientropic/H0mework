import H0mework.Arithmetic.PrimeShadow.P754

/-!
# Proposition 755: prime-pair zero energy is dynamical fixedness

P754 welded the explicit prime-pair producer to the P703 Hamiltonian/SAT shared
energy ledger by the arithmetic residual `N - p - q`.  This file pushes one
step further: on that same one-clause residual carrier, zero energy is exactly
fixedness under the certified saturation/phase-flow step.

For the half-rate dissipation step with zero direction and zero time step,
the angle component is inert and the obstruction component is multiplied by
`1/2`.  The state is fixed exactly when the obstruction residual is already
zero.  Thus the remaining Goldbach producer can be read equivalently as:

* a prime-pair producer,
* a zero-energy producer,
* a global search-success surface,
* or a global dynamical fixed-point producer.

Boundary: this does not prove Goldbach.  It proves that any solution of the
remaining producer debt is simultaneously a fixed point of the certified
energy dynamics, not merely a static arithmetic witness.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open ComplexityProjection

/-! ## A canonical arithmetic fixed-point step -/

/-- The inert direction field for the one-clause arithmetic carrier. -/
def goldbachZeroDirection : Unit -> Unit -> ℝ :=
  fun _ _ => 0

/-- The canonical half-rate arithmetic dissipation step.  At this rate the
obstruction component is multiplied by `1/2`; therefore fixedness forces the
arithmetic residual itself to vanish. -/
def goldbachHalfDissipationStep
    (S : SATPhaseFlowState Unit Unit) : SATPhaseFlowState Unit Unit :=
  phaseFlowDissipationStep (1 / 2 : ℝ) 0 goldbachZeroDirection S

/-- A candidate prime pair is dynamically fixed when its arithmetic residual
state is fixed by the canonical half-rate dissipation step. -/
def goldbachDynamicalFixedPoint
    (target : ℕ) (pair : PrimeExponent × PrimeExponent) : Prop :=
  goldbachHalfDissipationStep (goldbachEnergyState target pair) =
    goldbachEnergyState target pair

/-- THEOREM 1: the arithmetic residual state is fixed by the canonical
half-rate step exactly when the candidate pair sums to the target. -/
theorem goldbachDynamicalFixedPoint_iff_sum
    (target : ℕ) (pair : PrimeExponent × PrimeExponent) :
    goldbachDynamicalFixedPoint target pair ↔
      target = pair.1.1 + pair.2.1 := by
  constructor
  · intro hfix
    have hobs := congrArg (fun S : SATPhaseFlowState Unit Unit =>
      S.obstruction ()) hfix
    simp [goldbachHalfDissipationStep, goldbachEnergyState,
      goldbachPairResidual, phaseFlowDissipationStep,
      phaseResidualRelaxStep] at hobs
    have hres :
        (target : ℝ) - (pair.1.1 : ℝ) - (pair.2.1 : ℝ) = 0 := by
      linarith
    have hcast :
        (target : ℝ) = ((pair.1.1 + pair.2.1 : ℕ) : ℝ) := by
      norm_num
      linarith
    exact_mod_cast hcast
  · intro hsum
    unfold goldbachDynamicalFixedPoint goldbachHalfDissipationStep
    exact phaseFlowDissipationStep_fixed_of_hamiltonianEnergy_zero
      (1 / 2 : ℝ) 0 goldbachZeroDirection
      (goldbachEnergyState target pair)
      ((goldbachEnergyState_zero_iff_sum target pair).mpr hsum)

/-- THEOREM 2: dynamical fixedness is exactly zero shared energy. -/
theorem goldbachDynamicalFixedPoint_iff_zeroEnergy
    (target : ℕ) (pair : PrimeExponent × PrimeExponent) :
    goldbachDynamicalFixedPoint target pair ↔
      hamiltonianEnergyReadout (goldbachEnergyState target pair) = 0 :=
  (goldbachDynamicalFixedPoint_iff_sum target pair).trans
    (goldbachEnergyState_zero_iff_sum target pair).symm

/-! ## Global fixed-point producer surfaces -/

/-- A global even-Goldbach producer read as certified dynamical fixedness:
for each even target it chooses a typed prime pair whose residual state is
fixed by the canonical half-rate phase-flow step. -/
structure EvenGoldbachDynamicalFixedPointProducer where
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  fixed :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      goldbachDynamicalFixedPoint (2 * n) (pick n hn)

/-- THEOREM 3: global dynamical fixed-point production is equivalent to the
explicit prime-pair producer. -/
theorem evenGoldbachDynamicalFixedPointProducer_iff_primePairProducer :
    Nonempty EvenGoldbachDynamicalFixedPointProducer ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  constructor
  · rintro ⟨D⟩
    refine ⟨{ pick := D.pick, sum_pick := ?_ }⟩
    intro n hn
    exact (goldbachDynamicalFixedPoint_iff_sum (2 * n) (D.pick n hn)).mp
      (D.fixed n hn)
  · rintro ⟨P⟩
    refine ⟨{ pick := P.pick, fixed := ?_ }⟩
    intro n hn
    exact (goldbachDynamicalFixedPoint_iff_sum (2 * n) (P.pick n hn)).mpr
      (P.sum_pick n hn)

/-- THEOREM 4: global fixed-point production is exactly ordinary even
Goldbach. -/
theorem evenGoldbachDynamicalFixedPointProducer_iff_goldbach :
    Nonempty EvenGoldbachDynamicalFixedPointProducer ↔ EvenGoldbachStatement :=
  evenGoldbachDynamicalFixedPointProducer_iff_primePairProducer.trans
    evenGoldbachPrimePairProducer_iff_goldbach

/-- THEOREM 5: global fixed-point production is exactly global zero-energy
production from P754. -/
theorem evenGoldbachDynamicalFixedPointProducer_iff_zeroEnergyProducer :
    Nonempty EvenGoldbachDynamicalFixedPointProducer ↔
      Nonempty EvenGoldbachZeroEnergyProducer :=
  evenGoldbachDynamicalFixedPointProducer_iff_primePairProducer.trans
    evenGoldbachZeroEnergyProducer_iff_primePairProducer.symm

/-- A search-backed fixed-point surface: the P329 search returns a typed pair
whose arithmetic residual state is dynamically fixed. -/
def EvenGoldbachSearchFixedPointSuccess : Prop :=
  ∀ (n : ℕ), 2 ≤ n ->
    ∃ p q : PrimeExponent,
      goldbachSearchPrimePair (2 * n) = some (p, q) ∧
        goldbachDynamicalFixedPoint (2 * n) (p, q)

/-- THEOREM 6: search-backed fixedness is exactly ordinary even Goldbach. -/
theorem evenGoldbachSearchFixedPointSuccess_iff_goldbach :
    EvenGoldbachSearchFixedPointSuccess ↔ EvenGoldbachStatement := by
  constructor
  · intro h n hn
    rcases h n hn with ⟨p, q, _hsearch, hfix⟩
    exact ⟨p, q, (goldbachDynamicalFixedPoint_iff_sum (2 * n) (p, q)).mp hfix⟩
  · intro h n hn
    have hsome :
        (goldbachSearchPrimePair (2 * n)).isSome = true := by
      exact (goldbachSearchPrimePair_isSome_iff (2 * n)).mpr (h n hn)
    cases hsearch : goldbachSearchPrimePair (2 * n) with
    | none =>
        simp [hsearch] at hsome
    | some pair =>
        rcases pair with ⟨p, q⟩
        refine ⟨p, q, rfl, ?_⟩
        have hsum : 2 * n = p.1 + q.1 :=
          goldbachSearchPrimePair_sound hsearch
        exact (goldbachDynamicalFixedPoint_iff_sum (2 * n) (p, q)).mpr hsum

/-- THEOREM 7: the natural-coded Euler-pullback representative producer exists
exactly when the global dynamical fixed-point producer exists. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_fixedPoint :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  naturalCodedEulerPullbackRepresentativeProducer_iff_primePairProducer.trans
    evenGoldbachDynamicalFixedPointProducer_iff_primePairProducer.symm

/-- THEOREM 8: the natural-coded Euler-pullback representative producer exists
exactly when P329 search returns fixed-point witnesses globally. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_searchFixedPoint :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachSearchFixedPointSuccess :=
  naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach.trans
    evenGoldbachSearchFixedPointSuccess_iff_goldbach.symm

/-! ## Certificate packaging -/

/-- P755 certificate: the remaining prime-pair/zero-energy producer is exactly
a certified dynamical fixed-point producer on the same residual carrier. -/
structure NaturalCodedPrimePairFixedPointCertificate where
  fixed_point_iff_sum :
    ∀ (target : ℕ) (pair : PrimeExponent × PrimeExponent),
      goldbachDynamicalFixedPoint target pair ↔
        target = pair.1.1 + pair.2.1
  fixed_point_iff_zero_energy :
    ∀ (target : ℕ) (pair : PrimeExponent × PrimeExponent),
      goldbachDynamicalFixedPoint target pair ↔
        hamiltonianEnergyReadout (goldbachEnergyState target pair) = 0
  fixed_point_producer_iff_prime_pair_producer :
    Nonempty EvenGoldbachDynamicalFixedPointProducer ↔
      Nonempty EvenGoldbachPrimePairProducer
  fixed_point_producer_iff_goldbach :
    Nonempty EvenGoldbachDynamicalFixedPointProducer ↔
      EvenGoldbachStatement
  fixed_point_producer_iff_zero_energy_producer :
    Nonempty EvenGoldbachDynamicalFixedPointProducer ↔
      Nonempty EvenGoldbachZeroEnergyProducer
  search_fixed_point_iff_goldbach :
    EvenGoldbachSearchFixedPointSuccess ↔ EvenGoldbachStatement
  euler_pullback_iff_fixed_point :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  euler_pullback_iff_search_fixed_point :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachSearchFixedPointSuccess
  p754_energy_bridge :
    NaturalCodedPrimePairEnergyProducerCertificate

/-- THEOREM 9: canonical P755 certificate. -/
def naturalCodedPrimePairFixedPointCertificate :
    NaturalCodedPrimePairFixedPointCertificate where
  fixed_point_iff_sum := goldbachDynamicalFixedPoint_iff_sum
  fixed_point_iff_zero_energy := goldbachDynamicalFixedPoint_iff_zeroEnergy
  fixed_point_producer_iff_prime_pair_producer :=
    evenGoldbachDynamicalFixedPointProducer_iff_primePairProducer
  fixed_point_producer_iff_goldbach :=
    evenGoldbachDynamicalFixedPointProducer_iff_goldbach
  fixed_point_producer_iff_zero_energy_producer :=
    evenGoldbachDynamicalFixedPointProducer_iff_zeroEnergyProducer
  search_fixed_point_iff_goldbach :=
    evenGoldbachSearchFixedPointSuccess_iff_goldbach
  euler_pullback_iff_fixed_point :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_fixedPoint
  euler_pullback_iff_search_fixed_point :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_searchFixedPoint
  p754_energy_bridge := naturalCodedPrimePairEnergyProducerCertificate

end AffineRelaxation

/-! ## Grand-root packaging -/

namespace GrandUnification

open AffineRelaxation

universe u

/-- P755 root: the natural-coded mathematical producer, the zero-energy
producer, and the certified dynamical fixed-point producer are the same
remaining front. -/
structure NaturalCodedPrimePairFixedPointRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p754_root :
    NaturalCodedPrimePairEnergyRootCertificate E
  fixed_point_bridge :
    NaturalCodedPrimePairFixedPointCertificate

/-- THEOREM 10: canonical P755 root certificate. -/
def naturalCodedPrimePairFixedPointRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    NaturalCodedPrimePairFixedPointRootCertificate E where
  p754_root := naturalCodedPrimePairEnergyRootCertificate (E := E)
  fixed_point_bridge := naturalCodedPrimePairFixedPointCertificate

end GrandUnification
end SaturationMonoid
