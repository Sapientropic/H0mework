import H0mework.Versions.X.Arithmetic.FockUnitAction.FourierSibling

/-!
# Successor prime-field Fourier no-go

At stage `index`, the exact owner prime field already contains every prime at
most `2 * (index + 1)`.  A prime pair for the next target
`2 * (index + 2)` cannot use a larger prime: its partner would be `0` or `1`.
Consequently the actual successor prime-support update contributes exactly
zero to the new fixed-target correlation.  The runtime Fourier coefficient
is literally the correlation already visible from the previous prime field.

This rules out the installed successor support expansion as the missing
cross-prime nonvanishing action.  It does not assert that the coefficient is
zero and takes no fibre, landing, positivity, or nonvanishing premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset AddChar ZMod
open scoped BigOperators ZMod
open GoldbachPrimePairTrace

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockSuccessorPrimeFieldFourierNoGo

open ParticleWaveFock
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open ParticleWaveFockRuntime
open ParticleWaveFockRuntimeExactPrimeFourierSibling

noncomputable section

def nextEvenTarget (index : Nat) : Nat :=
  2 * (index + 2)

def ownerPrimeOnlyCorrelationAtNextTarget
    (owner : GlobalParentOwner) (index : Nat) : ℂ :=
  natPairCorrelation (ownerPrimeOnlyComplexWeight owner index)
    (nextEvenTarget index)

theorem exactPrimeOnlyComplexWeight_one_eq_zero :
    exactPrimeOnlyComplexWeight 1 = 0 := by
  simp [exactPrimeOnlyComplexWeight, primeVonMangoldtWeight]

theorem previousOwnerPrimeOnlyCorrelation_eq_exact
    (owner : GlobalParentOwner) (index : Nat) :
    ownerPrimeOnlyCorrelationAtNextTarget owner index =
      natPairCorrelation exactPrimeOnlyComplexWeight
        (nextEvenTarget index) := by
  classical
  rw [ownerPrimeOnlyCorrelationAtNextTarget, natPairCorrelation]
  apply Finset.sum_congr rfl
  intro left leftMem
  have leftLower : 1 ≤ left := (Finset.mem_Ico.mp leftMem).1
  have leftUpper : left < nextEvenTarget index :=
    (Finset.mem_Ico.mp leftMem).2
  let oldTarget := 2 * (index + 1)
  have targetEq : nextEvenTarget index = oldTarget + 2 := by
    simp [nextEvenTarget, oldTarget]
    omega
  by_cases leftOld : left ≤ oldTarget
  · by_cases rightOld : nextEvenTarget index - left ≤ oldTarget
    · rw [ownerPrimeOnlyComplexWeight_eq_exact owner index left leftOld,
        ownerPrimeOnlyComplexWeight_eq_exact owner index
          (nextEvenTarget index - left) rightOld]
    · have leftEq : left = 1 := by omega
      subst left
      rw [ownerPrimeOnlyComplexWeight_eq_exact owner index 1 (by omega),
        exactPrimeOnlyComplexWeight_one_eq_zero]
      simp
  · have rightEq : nextEvenTarget index - left = 1 := by omega
    rw [ownerPrimeOnlyComplexWeight_eq_exact owner index
      (nextEvenTarget index - left) (by omega), rightEq,
      exactPrimeOnlyComplexWeight_one_eq_zero]
    simp

theorem successor_and_previous_primeField_same_newTarget_correlation
    (sourceOwner targetOwner : GlobalParentOwner) (index : Nat) :
    natPairCorrelation (ownerPrimeOnlyComplexWeight targetOwner (index + 1))
        (nextEvenTarget index) =
      ownerPrimeOnlyCorrelationAtNextTarget sourceOwner index := by
  rw [previousOwnerPrimeOnlyCorrelation_eq_exact sourceOwner,
    natPairCorrelation]
  apply Finset.sum_congr rfl
  intro left leftMem
  have leftLe : left ≤ nextEvenTarget index :=
    (Finset.mem_Ico.mp leftMem).2.le
  have rightLe : nextEvenTarget index - left ≤ nextEvenTarget index :=
    Nat.sub_le _ _
  have stageTarget : 2 * ((index + 1) + 1) = nextEvenTarget index := by
    simp [nextEvenTarget]
  rw [ownerPrimeOnlyComplexWeight_eq_exact targetOwner (index + 1) left (by
      omega),
    ownerPrimeOnlyComplexWeight_eq_exact targetOwner (index + 1)
      (nextEvenTarget index - left) (by omega)]

def rootSourcePrimeOnlyCorrelationAtNextTarget
    (current : CanonicalUnitArithmeticRoot.Current) : ℂ :=
  ownerPrimeOnlyCorrelationAtNextTarget
    (liveGlobalOwner current) (ParticleWaveFockRuntime.scanIndex current)

def rootTargetPrimeOnlyCorrelationAtNextTarget
    (current : CanonicalUnitArithmeticRoot.Current) : ℂ :=
  natPairCorrelation
    (ownerPrimeOnlyComplexWeight
      (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current))
      (ParticleWaveFockRuntime.scanIndex
        (CanonicalUnitArithmeticRoot.next current)))
    (nextEvenTarget (ParticleWaveFockRuntime.scanIndex current))

def rootPrimeSupportUpdateContributionAtNextTarget
    (current : CanonicalUnitArithmeticRoot.Current) : ℂ :=
  rootTargetPrimeOnlyCorrelationAtNextTarget current -
    rootSourcePrimeOnlyCorrelationAtNextTarget current

theorem rootTargetPrimeOnlyCorrelation_eq_sourceAtNextTarget
    (current : CanonicalUnitArithmeticRoot.Current) :
    rootTargetPrimeOnlyCorrelationAtNextTarget current =
      rootSourcePrimeOnlyCorrelationAtNextTarget current := by
  rw [rootTargetPrimeOnlyCorrelationAtNextTarget,
    rootSourcePrimeOnlyCorrelationAtNextTarget,
    ParticleWaveFockRuntime.scanIndex_next]
  exact successor_and_previous_primeField_same_newTarget_correlation
    (liveGlobalOwner current)
    (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current))
    (ParticleWaveFockRuntime.scanIndex current)

theorem rootPrimeSupportUpdateContributionAtNextTarget_eq_zero
    (current : CanonicalUnitArithmeticRoot.Current) :
    rootPrimeSupportUpdateContributionAtNextTarget current = 0 := by
  rw [rootPrimeSupportUpdateContributionAtNextTarget,
    rootTargetPrimeOnlyCorrelation_eq_sourceAtNextTarget]
  simp

theorem runtimePrimeOnlyFourierCoefficient_eq_previousOwnerCorrelation
    (depth : Nat) :
    let current :=
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt depth)
        |>.current.visit.current
    runtimePrimeOnlyFourierCoefficient depth =
      ownerPrimeOnlyCorrelationAtNextTarget
        (liveGlobalOwner current) depth := by
  dsimp only
  rw [← runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient,
    runtimePrimeOnlyWeightedNaturalCorrelation_eq_exact,
    previousOwnerPrimeOnlyCorrelation_eq_exact]
  congr 2
  rw [runtimeEvenTarget_eq]
  simp [nextEvenTarget]

#print axioms previousOwnerPrimeOnlyCorrelation_eq_exact
#print axioms successor_and_previous_primeField_same_newTarget_correlation
#print axioms rootPrimeSupportUpdateContributionAtNextTarget_eq_zero
#print axioms runtimePrimeOnlyFourierCoefficient_eq_previousOwnerCorrelation

end
end ParticleWaveFockSuccessorPrimeFieldFourierNoGo
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
