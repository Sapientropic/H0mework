import H0mework.Versions.X.Arithmetic.UnitArithmetic.SettlementFacade

/-!
# Classical Goldbach readout of the canonical effective carrier

This file states the classical prime-pair proposition afresh and proves that
it is equivalent to inhabitance of every canonical effective fibre in the
classical range `4, 6, 8, ...`.

The nontrivial direction sends an arbitrary classical prime pair into the
actual factorization support of the same generated target.  Thus the finite
candidate carrier is coverage-complete for classical prime pairs; no
historical Goldbach statement, prime table, or caller landing enters the
authority chain.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticClassicalGoldbachBridge

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticGeneratedSettlementFacade
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

/-- Fresh external-coordinate statement; this is a downstream readout, not
source material or a second Goldbach root. -/
def CanonicalClassicalGoldbach : Prop :=
  ∀ target : Nat, 4 ≤ target → Even target →
    ∃ left right : Nat,
      Nat.Prime left ∧ Nat.Prime right ∧ target = left + right

/-- Internal positive mouth over exactly the classical target range. -/
def AllClassicalRangeEffectiveFibres : Prop :=
  ∀ index : Nat, 1 ≤ index → Nonempty (EffectiveAdditiveFibreAt index)

/-- Every prime not exceeding the generated target occurs in the target
factorial's actual factorization support. -/
def primeIndexOfPrime
    {index : Nat} (value : Nat) (isPrime : Nat.Prime value)
    (leTarget : value ≤ (evenTargetHistory index).cardinalShadow) :
    GeneratedPrimeIndexAt index := by
  refine ⟨value, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  apply Nat.ne_of_gt
  apply isPrime.factorization_pos_of_dvd
  · rw [factorialHistory_cardinalShadow]
    exact Nat.factorial_ne_zero _
  · rw [factorialHistory_cardinalShadow]
    exact Nat.dvd_factorial isPrime.pos leTarget

@[simp] theorem primeIndexOfPrime_value
    {index : Nat} (value : Nat) (isPrime : Nat.Prime value)
    (leTarget : value ≤ (evenTargetHistory index).cardinalShadow) :
    (primeIndexOfPrime value isPrime leTarget).1 = value :=
  rfl

@[simp] theorem generatedPrimeHistory_primeIndexOfPrime_cardinalShadow
    {index : Nat} (value : Nat) (isPrime : Nat.Prime value)
    (leTarget : value ≤ (evenTargetHistory index).cardinalShadow) :
    (generatedPrimeHistory
      (primeIndexOfPrime value isPrime leTarget)).cardinalShadow = value := by
  simp [generatedPrimeHistory,
    GeneratedUnitFactorizationAt.actualPrimePowerHistory,
    primePowerHistory, firstExponentIndex, exponent, primeIndexOfPrime]
  rfl

/-- A classical prime pair generates an actual canonical fibre. -/
theorem effectiveFibres_of_classical
    (classical : CanonicalClassicalGoldbach) :
    AllClassicalRangeEffectiveFibres := by
  intro index indexInRange
  have targetAtLeastFour :
      4 ≤ (evenTargetHistory index).cardinalShadow := by
    rw [evenTargetHistory_eq_generate,
      UnitHistory.cardinalShadow_generate]
    omega
  obtain ⟨left, right, leftPrime, rightPrime, landing⟩ :=
    classical (evenTargetHistory index).cardinalShadow
      targetAtLeastFour (evenTargetHistory_is_even index)
  have leftLeTarget :
      left ≤ (evenTargetHistory index).cardinalShadow := by
    omega
  have rightLeTarget :
      right ≤ (evenTargetHistory index).cardinalShadow := by
    omega
  let leftIndex : GeneratedPrimeIndexAt index :=
    primeIndexOfPrime left leftPrime leftLeTarget
  let rightIndex : GeneratedPrimeIndexAt index :=
    primeIndexOfPrime right rightPrime rightLeTarget
  refine ⟨⟨(leftIndex, rightIndex), ?_⟩⟩
  apply UnitHistory.eq_of_cardinalShadow_eq
  simp only [additiveEvaluation, UnitHistory.cardinalShadow_parallel]
  rw [show (generatedPrimeHistory leftIndex).cardinalShadow = left by
      simp [leftIndex],
    show (generatedPrimeHistory rightIndex).cardinalShadow = right by
      simp [rightIndex]]
  exact landing.symm

/-- An actual canonical fibre reads back a classical prime pair. -/
theorem classical_of_effectiveFibres
    (effective : AllClassicalRangeEffectiveFibres) :
    CanonicalClassicalGoldbach := by
  intro target targetAtLeastFour targetEven
  obtain ⟨half, target_eq⟩ := targetEven
  let index := half - 1
  have indexInRange : 1 ≤ index := by
    omega
  obtain ⟨fibre⟩ := effective index indexInRange
  refine ⟨fibre.leftHistory.cardinalShadow,
    fibre.rightHistory.cardinalShadow,
    fibre.left_isPrime, fibre.right_isPrime, ?_⟩
  have targetHistory_eq_target :
      (evenTargetHistory index).cardinalShadow = target := by
    rw [evenTargetHistory_eq_generate,
      UnitHistory.cardinalShadow_generate]
    dsimp [index]
    omega
  have landing := congrArg UnitHistory.cardinalShadow fibre.lands
  rw [UnitHistory.cardinalShadow_parallel] at landing
  exact targetHistory_eq_target.symm.trans landing

theorem classical_iff_all_effectiveFibres :
    CanonicalClassicalGoldbach ↔ AllClassicalRangeEffectiveFibres :=
  ⟨effectiveFibres_of_classical, classical_of_effectiveFibres⟩

/-- Public named-facade form of the same positive mouth. -/
def AllNamedGoldbachDispositionsPositive : Prop :=
  ∀ index : Nat, 1 ≤ index →
    ∃ fibre : EffectiveAdditiveFibreAt index,
      generatedFacade.additiveDisposition index = .inhabited fibre

theorem all_effectiveFibres_iff_namedPositive :
    AllClassicalRangeEffectiveFibres ↔
      AllNamedGoldbachDispositionsPositive := by
  constructor
  · intro effective index indexInRange
    let inhabited := effective index indexInRange
    refine ⟨Classical.choice inhabited, ?_⟩
    rw [generatedFacade.additiveDisposition_eq]
    exact settle_eq_inhabited_of_nonempty _ _ inhabited
  · intro named index indexInRange
    obtain ⟨fibre, _selected⟩ := named index indexInRange
    exact ⟨fibre⟩

theorem classical_iff_namedPositive :
    CanonicalClassicalGoldbach ↔ AllNamedGoldbachDispositionsPositive :=
  classical_iff_all_effectiveFibres.trans
    all_effectiveFibres_iff_namedPositive

end
end CanonicalUnitArithmeticClassicalGoldbachBridge
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
