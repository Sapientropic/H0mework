import H0mework.Arithmetic.GoldbachFourier.FlexibleWindow
import H0mework.Versions.R2.Arithmetic.GoldbachFourier.ClassicalBridge
import H0mework.Versions.R2.Arithmetic.FockUnitAction.RuntimeOccupation

/-!
# Exact-owner prime-only Fourier sibling

The operational runtime owns the target, exact prime field, and Fock state.
This probe derives the natural prime-only von-Mangoldt correlation and its
no-wrap finite Fourier coefficient from that same runtime depth.  No prime
pair, Goldbach fibre, nonvanishing law, or Fourier estimate is an input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset AddChar ZMod
open scoped BigOperators ZMod

open SaturationMonoid
open SaturationMonoid.ResponsibilityLifecycle
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticGeneration
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalUnitArithmeticClassicalGoldbachBridge
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalUnitArithmeticEffectiveAdditiveProducer
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalUnitArithmeticOperationalGoldbachRuntime
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntimePrimePairOccupation
open GoldbachPrimePairTrace

noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockRuntimeExactPrimeFourierSibling

def runtimeEvenTarget (depth : Nat) : Nat :=
  2 * (scanIndex (runtimeAt depth).current.visit.current + 1)

theorem runtimeEvenTarget_eq (depth : Nat) :
    runtimeEvenTarget depth = 2 * (depth + 2) := by
  rw [runtimeEvenTarget, runtimeAt_scanIndex]

def exactPrimeOnlyComplexWeight (value : Nat) : ℂ :=
  primeVonMangoldtWeight value

/-- Prime-only weight exposed from the exact owner's finite prime-index face.
The existential is over source-generated indices, not over a caller prime
table. -/
def ownerPrimeOnlyComplexWeight
    (owner : GlobalParentOwner) (index value : Nat) : ℂ :=
  if ∃ primeIndex : OwnerPrimeIndexAt owner index,
      primeIndex.1 = value then
    exactPrimeOnlyComplexWeight value
  else 0

theorem ownerPrimeOnlyComplexWeight_eq_exact
    (owner : GlobalParentOwner) (index value : Nat)
    (leTarget : value ≤ 2 * (index + 1)) :
    ownerPrimeOnlyComplexWeight owner index value =
      exactPrimeOnlyComplexWeight value := by
  classical
  by_cases valuePrime : Nat.Prime value
  · have leHistory :
        value ≤ (evenTargetHistory index).cardinalShadow := by
      simpa [evenTargetHistory_eq_generate,
        UnitHistory.cardinalShadow_generate] using leTarget
    let generated : GeneratedPrimeIndexAt index :=
      primeIndexOfPrime value valuePrime leHistory
    let ownerIndex : OwnerPrimeIndexAt owner index :=
      (ownerPrimeIndexEquivGenerated owner index).symm generated
    have ownerValue : ownerIndex.1 = value := by
      have mapped :=
        (ownerPrimeIndexEquivGenerated owner index).apply_symm_apply generated
      exact congrArg Subtype.val mapped
    rw [ownerPrimeOnlyComplexWeight, if_pos ⟨ownerIndex, ownerValue⟩]
  · simp [ownerPrimeOnlyComplexWeight, exactPrimeOnlyComplexWeight,
      primeVonMangoldtWeight, valuePrime]

def runtimePrimeOnlyComplexWeight (depth value : Nat) : ℂ :=
  let current := (runtimeAt depth).current.visit.current
  ownerPrimeOnlyComplexWeight
    (ParticleWaveFockRuntime.liveGlobalOwner current)
    (scanIndex current) value

def runtimePrimeOnlyWeightedNaturalCorrelation (depth : Nat) : ℂ :=
  natPairCorrelation (runtimePrimeOnlyComplexWeight depth)
    (runtimeEvenTarget depth)

noncomputable def runtimePrimeOnlyFourierCoefficient (depth : Nat) : ℂ :=
  let target := runtimeEvenTarget depth
  letI : NeZero (target + 2) := ⟨by omega⟩
  ((target + 2 : Nat) : ℂ)⁻¹ *
    ∑ frequency : ZMod (target + 2),
          stdAddChar (frequency * (target : ZMod (target + 2))) *
            (finiteExponentialSum
              (naturalWindowCyclicWeightAtModulus
                (runtimePrimeOnlyComplexWeight depth) target (target + 2))
              frequency) ^ 2

theorem exactPrimeOnlyComplexCorrelation_eq_cast (target : Nat) :
    natPairCorrelation exactPrimeOnlyComplexWeight target =
      (primeOnlyGoldbachCorrelation target : ℂ) := by
  rw [primeOnlyGoldbachCorrelation]
  unfold natPairCorrelation exactPrimeOnlyComplexWeight
  push_cast
  rfl

theorem runtimePrimeOnlyWeightedNaturalCorrelation_eq_exact
    (depth : Nat) :
    runtimePrimeOnlyWeightedNaturalCorrelation depth =
      natPairCorrelation exactPrimeOnlyComplexWeight
        (runtimeEvenTarget depth) := by
  classical
  rw [runtimePrimeOnlyWeightedNaturalCorrelation, natPairCorrelation]
  apply Finset.sum_congr rfl
  intro left leftMem
  have leftLe : left ≤ runtimeEvenTarget depth :=
    (Finset.mem_Ico.mp leftMem).2.le
  have rightLe : runtimeEvenTarget depth - left ≤ runtimeEvenTarget depth :=
    Nat.sub_le _ _
  simp only [runtimePrimeOnlyComplexWeight]
  rw [ownerPrimeOnlyComplexWeight_eq_exact _ _ _ leftLe,
    ownerPrimeOnlyComplexWeight_eq_exact _ _ _ rightLe]

theorem runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient
    (depth : Nat) :
    runtimePrimeOnlyWeightedNaturalCorrelation depth =
      runtimePrimeOnlyFourierCoefficient depth := by
  rw [runtimePrimeOnlyWeightedNaturalCorrelation,
    runtimePrimeOnlyFourierCoefficient]
  let _ : NeZero (runtimeEvenTarget depth + 2) := ⟨by omega⟩
  exact naturalFiniteFourierCoefficientIdentityAtModulus
    (runtimePrimeOnlyComplexWeight depth) (by omega)

def exactPrimePairOfEffectiveFibre {index : Nat}
    (fibre : EffectiveAdditiveFibreAt index) :
    ExactPrimePairFiber (2 * (index + 1)) := by
  refine ⟨(⟨fibre.leftHistory.cardinalShadow, fibre.left_isPrime⟩,
      ⟨fibre.rightHistory.cardinalShadow, fibre.right_isPrime⟩), ?_⟩
  change fibre.leftHistory.cardinalShadow +
      fibre.rightHistory.cardinalShadow = 2 * (index + 1)
  have landing := congrArg UnitHistory.cardinalShadow fibre.lands
  simp only [evenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate,
    UnitHistory.cardinalShadow_parallel] at landing
  exact landing.symm

def effectiveFibreOfExactPrimePair {index : Nat}
    (pair : ExactPrimePairFiber (2 * (index + 1))) :
    EffectiveAdditiveFibreAt index := by
  have pairSum : pair.1.1.1 + pair.1.2.1 = 2 * (index + 1) := by
    simpa [AdditivePairGeometry.pairEnergy, primePairGeometry] using pair.2
  let leftIndex : GeneratedPrimeIndexAt index :=
    primeIndexOfPrime pair.1.1.1 pair.1.1.2 (by
      rw [evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]
      have rightPositive := pair.1.2.2.pos
      omega)
  let rightIndex : GeneratedPrimeIndexAt index :=
    primeIndexOfPrime pair.1.2.1 pair.1.2.2 (by
      rw [evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]
      have leftPositive := pair.1.1.2.pos
      omega)
  refine ⟨(leftIndex, rightIndex), ?_⟩
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [additiveEvaluation, UnitHistory.cardinalShadow_parallel,
    evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]
  rw [show (generatedPrimeHistory leftIndex).cardinalShadow = pair.1.1.1 by
      simp [leftIndex],
    show (generatedPrimeHistory rightIndex).cardinalShadow = pair.1.2.1 by
      simp [rightIndex]]
  exact pairSum

theorem effectiveFibre_nonempty_iff_exactPrimePairFiber (index : Nat) :
    Nonempty (EffectiveAdditiveFibreAt index) ↔
      Nonempty (ExactPrimePairFiber (2 * (index + 1))) := by
  constructor
  · rintro ⟨fibre⟩
    exact ⟨exactPrimePairOfEffectiveFibre fibre⟩
  · rintro ⟨pair⟩
    exact ⟨effectiveFibreOfExactPrimePair pair⟩

theorem primeOnlyGoldbachCorrelation_nonneg (target : Nat) :
    0 ≤ primeOnlyGoldbachCorrelation target := by
  rw [primeOnlyGoldbachCorrelation, natPairCorrelation]
  exact Finset.sum_nonneg fun left _leftMem =>
    mul_nonneg (primeVonMangoldtWeight_nonneg left)
      (primeVonMangoldtWeight_nonneg (target - left))

theorem primeOnlyGoldbachCorrelation_ne_zero_iff_exactPrimePairFiber
    (target : Nat) :
    primeOnlyGoldbachCorrelation target ≠ 0 ↔
      Nonempty (ExactPrimePairFiber target) := by
  constructor
  · intro nonzero
    apply (primeOnlyGoldbachCorrelation_pos_iff target).1
    exact lt_of_le_of_ne (primeOnlyGoldbachCorrelation_nonneg target)
      (Ne.symm nonzero)
  · intro fibre
    exact ne_of_gt ((primeOnlyGoldbachCorrelation_pos_iff target).2 fibre)

theorem exactPrimeOnlyComplexCorrelation_ne_zero_iff_exactPrimePairFiber
    (target : Nat) :
    natPairCorrelation exactPrimeOnlyComplexWeight target ≠ 0 ↔
      Nonempty (ExactPrimePairFiber target) := by
  rw [exactPrimeOnlyComplexCorrelation_eq_cast]
  exact_mod_cast
    primeOnlyGoldbachCorrelation_ne_zero_iff_exactPrimePairFiber target

theorem runtimeAtomicOccupation_ne_zero_iff_primeOnlyWeightedNaturalCorrelation
    (depth : Nat) :
    let current := (runtimeAt depth).current.visit.current
    atomicTargetAmplitude (scanIndex current)
        (runtimeParticleWavePayload depth).sourceState ≠ 0 ↔
      runtimePrimeOnlyWeightedNaturalCorrelation depth ≠ 0 := by
  dsimp only
  refine (runtimeAtomicOccupation_ne_zero_iff_effectiveFibre depth).trans ?_
  let index := scanIndex (runtimeAt depth).current.visit.current
  change Nonempty (EffectiveAdditiveFibreAt index) ↔
    runtimePrimeOnlyWeightedNaturalCorrelation depth ≠ 0
  rw [runtimePrimeOnlyWeightedNaturalCorrelation_eq_exact]
  change Nonempty (EffectiveAdditiveFibreAt index) ↔
    natPairCorrelation exactPrimeOnlyComplexWeight (2 * (index + 1)) ≠ 0
  exact (effectiveFibre_nonempty_iff_exactPrimePairFiber index).trans
    (exactPrimeOnlyComplexCorrelation_ne_zero_iff_exactPrimePairFiber
      (2 * (index + 1))).symm

theorem runtimeAtomicOccupation_ne_zero_iff_primeOnlyFourierCoefficient
    (depth : Nat) :
    let current := (runtimeAt depth).current.visit.current
    atomicTargetAmplitude (scanIndex current)
        (runtimeParticleWavePayload depth).sourceState ≠ 0 ↔
      runtimePrimeOnlyFourierCoefficient depth ≠ 0 := by
  dsimp only
  constructor
  · intro amplitudeNonzero
    have correlationNonzero :=
      (runtimeAtomicOccupation_ne_zero_iff_primeOnlyWeightedNaturalCorrelation
        depth).1 amplitudeNonzero
    rw [runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient]
      at correlationNonzero
    exact correlationNonzero
  · intro fourierNonzero
    apply
      (runtimeAtomicOccupation_ne_zero_iff_primeOnlyWeightedNaturalCorrelation
        depth).2
    rw [runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient]
    exact fourierNonzero

/-- The arithmetic and Fourier siblings are fixed by the same runtime depth.
The owner equality is read from the existing particle-wave payload; the target
is not a caller argument. -/
theorem runtimeExactOwnerPrimeOnlyFourierSibling (depth : Nat) :
    let current := (runtimeAt depth).current.visit.current
    let owner := ParticleWaveFockRuntime.liveGlobalOwner current
    (runtimePayload depth).targetOccurrence.root.rootOccurrence =
        (runtimeParticleWavePayload depth).sourceOccurrence ∧
      (runtimeParticleWavePayload depth).sourceState =
        secondQuantizedState (ownerPrimeField owner (scanIndex current)) ∧
      (atomicTargetAmplitude (scanIndex current)
            (runtimeParticleWavePayload depth).sourceState ≠ 0 ↔
        runtimePrimeOnlyWeightedNaturalCorrelation depth ≠ 0) ∧
      runtimePrimeOnlyWeightedNaturalCorrelation depth =
        runtimePrimeOnlyFourierCoefficient depth := by
  dsimp only
  refine ⟨(runtime_particleWave_goldbach_share_occurrence depth).2, ?_,
    runtimeAtomicOccupation_ne_zero_iff_primeOnlyWeightedNaturalCorrelation depth,
    runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient depth⟩
  rw [(runtimeParticleWavePayload depth).sourceState_eq]
  rfl

#print axioms runtimePrimeOnlyWeightedNaturalCorrelation_eq_fourierCoefficient
#print axioms ownerPrimeOnlyComplexWeight_eq_exact
#print axioms runtimePrimeOnlyWeightedNaturalCorrelation_eq_exact
#print axioms effectiveFibre_nonempty_iff_exactPrimePairFiber
#print axioms runtimeAtomicOccupation_ne_zero_iff_primeOnlyWeightedNaturalCorrelation
#print axioms runtimeAtomicOccupation_ne_zero_iff_primeOnlyFourierCoefficient
#print axioms runtimeExactOwnerPrimeOnlyFourierSibling

end ParticleWaveFockRuntimeExactPrimeFourierSibling
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
