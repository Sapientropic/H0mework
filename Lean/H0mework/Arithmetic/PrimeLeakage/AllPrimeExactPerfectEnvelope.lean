import H0mework.Arithmetic.PrimeLeakage.AllPrimeJointRelationFace
import H0mework.Realization.Perfectification.IntegralPair

/-!
# Exact perfect envelope of the all-prime current

The source-generated prime basis supplies its canonical integral dual
evaluation.  The generic exact-envelope engine then produces the coimage,
generated dual image, coevaluation and both zig-zags without a finite,
projective, nondegenerate or determinant premise.

The same evaluation gives the finite-support sum-of-squares energy.  It is
nonnegative and vanishes exactly at the zero prime current.  This is the
canonical positive integral pairing on the already generated current; it does
not assert that the later analytic leakage is zero.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace ActionCofiber
namespace RawEffect
namespace AllPrimePerfectEnvelope

open AllPrimeCofinal
open SourceGeneratedCanonicalPerfectPair
open SourceGeneratedPerfectification

noncomputable section

noncomputable def allPrimeBasis : Module.Basis Nat.Primes ℤ AllPrimeCurrent :=
  Finsupp.basisSingleOne

noncomputable def allPrimeDualEvaluation :
    AllPrimeCurrent →ₗ[ℤ] Module.Dual ℤ AllPrimeCurrent :=
  allPrimeBasis.toDual

theorem allPrimeDualEvaluation_injective :
    Function.Injective allPrimeDualEvaluation :=
  allPrimeBasis.toDual_injective

@[simp] theorem allPrimeDualEvaluation_single
    (left right : Nat.Primes) :
    allPrimeDualEvaluation (Finsupp.single left 1)
        (Finsupp.single right 1) = if left = right then 1 else 0 := by
  exact allPrimeBasis.toDual_apply left right

theorem allPrimeDualEvaluation_apply
    (left right : AllPrimeCurrent) :
    allPrimeDualEvaluation left right =
      left.sum fun prime coefficient => coefficient * right prime := by
  classical
  induction left using Finsupp.induction_linear with
  | zero => simp
  | add first second firstHypothesis secondHypothesis =>
      rw [map_add, LinearMap.add_apply, Finsupp.sum_add_index]
      · rw [firstHypothesis, secondHypothesis]
      · intro _ _
        simp
      · intro _ _ firstCoefficient secondCoefficient
        ring
  | single prime coefficient =>
      change (Finsupp.basisSingleOne.toDual
          (Finsupp.single prime coefficient)) right = _
      have single_eq : Finsupp.single prime coefficient =
          coefficient • (Finsupp.basisSingleOne prime : AllPrimeCurrent) := by
        ext index
        simp [Finsupp.single_apply]
      rw [single_eq, map_smul, LinearMap.smul_apply,
        Finsupp.basisSingleOne.toDual_apply_right]
      simp

def allPrimeQuadraticEnergy (current : AllPrimeCurrent) : ℤ :=
  allPrimeDualEvaluation current current

theorem allPrimeQuadraticEnergy_eq_sum_sq (current : AllPrimeCurrent) :
    allPrimeQuadraticEnergy current =
      current.sum fun _ coefficient => coefficient ^ 2 := by
  rw [allPrimeQuadraticEnergy, allPrimeDualEvaluation_apply]
  apply Finsupp.sum_congr
  intro _prime _prime_mem
  ring

@[simp] theorem allPrimeQuadraticEnergy_single
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeQuadraticEnergy (Finsupp.single prime coefficient) =
      coefficient ^ 2 := by
  rw [allPrimeQuadraticEnergy_eq_sum_sq]
  simp

theorem allPrimeQuadraticEnergy_nonnegative (current : AllPrimeCurrent) :
    0 ≤ allPrimeQuadraticEnergy current := by
  rw [allPrimeQuadraticEnergy_eq_sum_sq]
  exact Finsupp.sum_nonneg fun _ _ => sq_nonneg _

theorem allPrimeQuadraticEnergy_eq_zero_iff (current : AllPrimeCurrent) :
    allPrimeQuadraticEnergy current = 0 ↔ current = 0 := by
  rw [allPrimeQuadraticEnergy_eq_sum_sq]
  constructor
  · intro energyZero
    ext prime
    by_contra coefficient_ne
    have prime_mem : prime ∈ current.support :=
      Finsupp.mem_support_iff.mpr coefficient_ne
    have square_le : current prime ^ 2 ≤
        current.sum fun _ coefficient => coefficient ^ 2 := by
      change current prime ^ 2 ≤
        current.support.sum fun index => current index ^ 2
      exact Finset.single_le_sum
        (fun index _ => sq_nonneg (current index)) prime_mem
    rw [energyZero] at square_le
    have squareZero : current prime ^ 2 = 0 := by
      nlinarith [sq_nonneg (current prime)]
    exact coefficient_ne (sq_eq_zero_iff.mp squareZero)
  · intro currentZero
    subst current
    simp

theorem allPrimeCurrent_not_finite :
    ¬ Module.Finite ℤ AllPrimeCurrent :=
  Module.not_finite_of_infinite_basis allPrimeBasis

abbrev AllPrimeExactCarrier :=
  PerfectificationCarrier allPrimeDualEvaluation

noncomputable def allPrimeCarrierEquiv :
    AllPrimeCurrent ≃ₗ[ℤ] AllPrimeExactCarrier :=
  LinearEquiv.ofBijective (canonicalMap allPrimeDualEvaluation) ⟨by
    intro left right equality
    apply allPrimeDualEvaluation_injective
    have mapped := congrArg (dualEmbedding allPrimeDualEvaluation) equality
    simpa only [← LinearMap.comp_apply,
      dualEmbedding_comp_canonicalMap] using mapped,
    Submodule.mkQ_surjective _⟩

def allPrimeExactEnvelope :
    UniversalPerfectEnvelope allPrimeDualEvaluation :=
  sourceGeneratedPerfectification allPrimeDualEvaluation

theorem allPrimeExactEnvelope_zigzags :
    allPrimeExactEnvelope.coevaluation.comp allPrimeExactEnvelope.map =
        LinearMap.id ∧
      allPrimeExactEnvelope.map.comp allPrimeExactEnvelope.coevaluation =
        LinearMap.id :=
  ⟨allPrimeExactEnvelope.left_zigzag,
    allPrimeExactEnvelope.right_zigzag⟩

/-- The exact envelope is a dependent child of the existing all-prime joint
relation occurrence. -/
def allPrimeExactEnvelopeOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (AllPrimeCofinal.allPrimeJointRelationOccurrence observation nontrivial).map
    fun payload => (payload, allPrimeExactEnvelope)

theorem allPrimeExactEnvelopeOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (allPrimeExactEnvelopeOccurrence observation nontrivial).map Prod.fst =
      AllPrimeCofinal.allPrimeJointRelationOccurrence
        observation nontrivial := by
  rw [allPrimeExactEnvelopeOccurrence, RootedAccountedUnfolding.map_map]
  change (AllPrimeCofinal.allPrimeJointRelationOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

end
end AllPrimePerfectEnvelope
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
