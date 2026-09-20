import H0mework.Arithmetic.PrimeShadow.P753
import H0mework.Computation.SelfReduction.P703

/-!
# Proposition 754: prime-pair production as zero residual energy

P753 sharpened the remaining mathematical producer debt to an explicit
prime-pair producer / global P329 search-success theorem.  P703 identified the
Hamiltonian-facing and SAT-facing energy readouts on one residual carrier.

This file welds those two fronts.  For a target exponent `N` and a typed prime
pair `(p,q)`, define the one-clause arithmetic residual

`r = N - p - q`.

On the P703 shared Hamiltonian/SAT carrier, the energy of this residual is
`r^2`; hence it vanishes exactly when the pair is a genuine additive
decomposition of `N`.  Therefore the global prime-pair producer from P753 is
equivalent to a global zero-energy producer on this explicit residual carrier.

Boundary: this still does not prove Goldbach.  It proves that the remaining
Goldbach producer is exactly a zero-energy residual producer on the same
Hamiltonian/SAT energy ledger, so the mathematics and energy fronts are no
longer merely parallel descriptions.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open ComplexityProjection

/-! ## The arithmetic residual carrier -/

/-- The one-clause residual attached to a target exponent and a typed
prime-pair candidate. -/
def goldbachPairResidual (target : ℕ)
    (pair : PrimeExponent × PrimeExponent) : Unit -> ℝ :=
  fun _ => (target : ℝ) - (pair.1.1 : ℝ) - (pair.2.1 : ℝ)

/-- The P703 shared Hamiltonian/SAT carrier for a single arithmetic
Goldbach residual.  The variable coordinate is inert; all content is in the
obstruction residual. -/
def goldbachEnergyState (target : ℕ)
    (pair : PrimeExponent × PrimeExponent) :
    SATPhaseFlowState Unit Unit where
  theta := fun _ => 0
  obstruction := goldbachPairResidual target pair

/-- THEOREM 1: the shared Hamiltonian/SAT energy of the arithmetic state is
the square of the additive prime-pair residual. -/
theorem goldbachEnergyState_energy_eq
    (target : ℕ) (pair : PrimeExponent × PrimeExponent) :
    hamiltonianEnergyReadout (goldbachEnergyState target pair) =
      ((target : ℝ) - (pair.1.1 : ℝ) - (pair.2.1 : ℝ)) ^ 2 := by
  classical
  simp [goldbachEnergyState, goldbachPairResidual,
    hamiltonianEnergyReadout, phaseResidualEnergy]

/-- THEOREM 2: zero shared energy is exactly the additive prime-pair
equation. -/
theorem goldbachEnergyState_zero_iff_sum
    (target : ℕ) (pair : PrimeExponent × PrimeExponent) :
    hamiltonianEnergyReadout (goldbachEnergyState target pair) = 0 ↔
      target = pair.1.1 + pair.2.1 := by
  constructor
  · intro hE
    rw [goldbachEnergyState_energy_eq] at hE
    have hres :
        (target : ℝ) - (pair.1.1 : ℝ) - (pair.2.1 : ℝ) = 0 := by
      exact sq_eq_zero_iff.mp hE
    have hcast :
        (target : ℝ) = ((pair.1.1 + pair.2.1 : ℕ) : ℝ) := by
      norm_num
      linarith
    exact_mod_cast hcast
  · intro hsum
    rw [goldbachEnergyState_energy_eq]
    have hcast :
        (target : ℝ) = ((pair.1.1 + pair.2.1 : ℕ) : ℝ) := by
      exact_mod_cast hsum
    norm_num [hcast]

/-! ## Global zero-energy producer surfaces -/

/-- A global even-Goldbach producer read through the P703 shared energy ledger:
for every even target `2*n`, it chooses a typed prime pair whose arithmetic
residual has zero Hamiltonian/SAT energy. -/
structure EvenGoldbachZeroEnergyProducer where
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  zero_energy :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      hamiltonianEnergyReadout
        (goldbachEnergyState (2 * n) (pick n hn)) = 0

/-- THEOREM 3: the explicit zero-energy producer is equivalent to the usual
explicit prime-pair producer. -/
theorem evenGoldbachZeroEnergyProducer_iff_primePairProducer :
    Nonempty EvenGoldbachZeroEnergyProducer ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  constructor
  · rintro ⟨Z⟩
    refine ⟨{ pick := Z.pick, sum_pick := ?_ }⟩
    intro n hn
    exact (goldbachEnergyState_zero_iff_sum (2 * n) (Z.pick n hn)).mp
      (Z.zero_energy n hn)
  · rintro ⟨P⟩
    refine ⟨{ pick := P.pick, zero_energy := ?_ }⟩
    intro n hn
    exact (goldbachEnergyState_zero_iff_sum (2 * n) (P.pick n hn)).mpr
      (P.sum_pick n hn)

/-- THEOREM 4: zero-energy production is exactly ordinary even Goldbach. -/
theorem evenGoldbachZeroEnergyProducer_iff_goldbach :
    Nonempty EvenGoldbachZeroEnergyProducer ↔ EvenGoldbachStatement :=
  evenGoldbachZeroEnergyProducer_iff_primePairProducer.trans
    evenGoldbachPrimePairProducer_iff_goldbach

/-- A search-backed zero-energy surface: the P329 search must return an
explicit typed pair, and that returned pair must have zero shared energy. -/
def EvenGoldbachSearchZeroEnergySuccess : Prop :=
  ∀ (n : ℕ), 2 ≤ n ->
    ∃ p q : PrimeExponent,
      goldbachSearchPrimePair (2 * n) = some (p, q) ∧
        hamiltonianEnergyReadout
          (goldbachEnergyState (2 * n) (p, q)) = 0

/-- THEOREM 5: the search-backed zero-energy surface is equivalent to ordinary
even Goldbach. -/
theorem evenGoldbachSearchZeroEnergySuccess_iff_goldbach :
    EvenGoldbachSearchZeroEnergySuccess ↔ EvenGoldbachStatement := by
  constructor
  · intro h n hn
    rcases h n hn with ⟨p, q, _hsearch, hE⟩
    exact ⟨p, q, (goldbachEnergyState_zero_iff_sum (2 * n) (p, q)).mp hE⟩
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
        exact (goldbachEnergyState_zero_iff_sum (2 * n) (p, q)).mpr hsum

/-- THEOREM 6: the P753 Euler-pullback representative producer exists exactly
when the explicit zero-energy producer exists. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_zeroEnergy :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachZeroEnergyProducer :=
  naturalCodedEulerPullbackRepresentativeProducer_iff_primePairProducer.trans
    evenGoldbachZeroEnergyProducer_iff_primePairProducer.symm

/-- THEOREM 7: the P753 Euler-pullback representative producer exists exactly
when the P329 search returns zero-energy witnesses globally. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_searchZeroEnergy :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachSearchZeroEnergySuccess :=
  naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach.trans
    evenGoldbachSearchZeroEnergySuccess_iff_goldbach.symm

/-! ## Certificate packaging -/

/-- P754 certificate: the explicit prime-pair producer is the same thing as a
zero-energy residual producer on the P703 Hamiltonian/SAT ledger. -/
structure NaturalCodedPrimePairEnergyProducerCertificate where
  pair_energy_zero_iff_sum :
    ∀ (target : ℕ) (pair : PrimeExponent × PrimeExponent),
      hamiltonianEnergyReadout (goldbachEnergyState target pair) = 0 ↔
        target = pair.1.1 + pair.2.1
  zero_energy_iff_prime_pair_producer :
    Nonempty EvenGoldbachZeroEnergyProducer ↔
      Nonempty EvenGoldbachPrimePairProducer
  zero_energy_iff_goldbach :
    Nonempty EvenGoldbachZeroEnergyProducer ↔ EvenGoldbachStatement
  search_zero_energy_iff_goldbach :
    EvenGoldbachSearchZeroEnergySuccess ↔ EvenGoldbachStatement
  euler_pullback_iff_zero_energy :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachZeroEnergyProducer
  euler_pullback_iff_search_zero_energy :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer
      naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachSearchZeroEnergySuccess
  p753_explicit_prime_pair :
    NaturalCodedExplicitPrimePairProducerCertificate
  p703_same_energy :
    ComplexityProjection.HamiltonianSATEnergySameCarrierCertificate.{0, 0}

/-- THEOREM 8: canonical P754 certificate. -/
def naturalCodedPrimePairEnergyProducerCertificate :
    NaturalCodedPrimePairEnergyProducerCertificate where
  pair_energy_zero_iff_sum := goldbachEnergyState_zero_iff_sum
  zero_energy_iff_prime_pair_producer :=
    evenGoldbachZeroEnergyProducer_iff_primePairProducer
  zero_energy_iff_goldbach := evenGoldbachZeroEnergyProducer_iff_goldbach
  search_zero_energy_iff_goldbach :=
    evenGoldbachSearchZeroEnergySuccess_iff_goldbach
  euler_pullback_iff_zero_energy :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_zeroEnergy
  euler_pullback_iff_search_zero_energy :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_searchZeroEnergy
  p753_explicit_prime_pair := naturalCodedExplicitPrimePairProducerCertificate
  p703_same_energy :=
    ComplexityProjection.hamiltonianSATEnergySameCarrierCertificate

end AffineRelaxation

/-! ## Grand-root packaging -/

namespace GrandUnification

open AffineRelaxation

universe u

/-- P754 root: the natural-coded mathematical producer and the
Hamiltonian/SAT energy ledger share a concrete zero-residual witness surface. -/
structure NaturalCodedPrimePairEnergyRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p753_root :
    NaturalCodedExplicitPrimePairProducerRootCertificate E
  p703_root :
    HamiltonianSATEnergySameCarrierUnifiedRootCertificate E
  energy_bridge :
    NaturalCodedPrimePairEnergyProducerCertificate

/-- THEOREM 9: canonical P754 root certificate. -/
def naturalCodedPrimePairEnergyRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    NaturalCodedPrimePairEnergyRootCertificate E where
  p753_root := naturalCodedExplicitPrimePairProducerRootCertificate (E := E)
  p703_root := hamiltonianSATEnergySameCarrierUnifiedRootCertificate (E := E)
  energy_bridge := naturalCodedPrimePairEnergyProducerCertificate

end GrandUnification
end SaturationMonoid
