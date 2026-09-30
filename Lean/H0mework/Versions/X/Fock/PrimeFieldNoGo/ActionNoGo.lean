import H0mework.Versions.X.Fock.PrimeFieldNoGo.FourierNoGo

/-!
# Successor prime-field Fock-action no-go

The weighted deletion is lifted back to the literal integral Fock state.
Prime-pair fibres for the next target are already completely represented by
the preceding stage: both primes are at most the old even target because the
other endpoint is at least two.  Hence the root-generated second-quantized
`forcedTraceAt` has zero atomic amplitude at the next target.

This is an exact audit of the installed root action, not an estimate and not
a classifier.  The theorem does not set the target occupation to zero; it
shows that the successor trace cannot be its missing nonzero producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockSuccessorPrimeFieldActionNoGo

open ParticleWaveFock
open CanonicalUnitArithmeticClassicalGoldbachBridge
open CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open ParticleWaveFockRuntime
open ParticleWaveFockSuccessorPrimeFieldFourierNoGo

noncomputable section

def previousStageAtomicOccupation
    (owner : GlobalParentOwner) (index : Nat) : ℤ :=
  atomicTargetAmplitude (index + 1)
    (secondQuantizedState (ownerPrimeField owner index))

theorem previousStageAtomicOccupation_eq_sum
    (owner : GlobalParentOwner) (index : Nat) :
    previousStageAtomicOccupation owner index =
      ∑ left : OwnerPrimeIndexAt owner index,
        ∑ right : OwnerPrimeIndexAt owner index,
          if left.1 + right.1 = nextEvenTarget index
          then (1 : ℤ) else 0 := by
  classical
  have scale_eq (primeIndex : OwnerPrimeIndexAt owner index) :
      ((ownerPrimeScaleUnit primeIndex : Units NNReal) : NNReal) =
        primeIndex.1 := by
    apply NNReal.eq
    exact ownerPrimeScaleUnit_value primeIndex
  rw [previousStageAtomicOccupation, atomicTargetAmplitude,
    LinearMap.comp_apply, Finsupp.lapply_apply,
    particleMeasurement_secondQuantizedState]
  simp_rw [ownerPrimeField, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, map_sum, ownerPrimeOneParticle_eq_delta,
    pairCharge_delta_tmul_delta]
  simp_rw [pairChargeBasis, scale_eq]
  simp_rw [Finset.sum_apply']
  simp only [Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro left _leftMem
  apply Finset.sum_congr rfl
  intro right _rightMem
  rw [Finsupp.single_apply]
  split <;> rename_i equality
  · have arithmeticEquality :
        left.1 + right.1 = nextEvenTarget index := by
      exact_mod_cast equality
    simp [arithmeticEquality, nextEvenTarget]
  · have arithmeticInequality :
        left.1 + right.1 ≠ nextEvenTarget index := by
      intro arithmeticEquality
      apply equality
      exact_mod_cast arithmeticEquality
    rw [if_neg arithmeticInequality]

def previousStagePairCoordinate
    (owner : GlobalParentOwner) (index : Nat)
    (candidate : OwnerPrimePairCandidateAt owner index) : Nat :=
  candidate.1.1 + candidate.2.1

noncomputable def previousStageAdditiveCoefficient
    (owner : GlobalParentOwner) (index : Nat) : Nat :=
  SourceGeneratedFiniteEffectiveCoefficient.effectiveCoefficient
    (previousStagePairCoordinate owner index) (nextEvenTarget index)

abbrev PreviousStageAdditiveFibreAt
    (owner : GlobalParentOwner) (index : Nat) :=
  SourceGeneratedEffectiveFibreDisposition.Fibre
    (previousStagePairCoordinate owner index) (nextEvenTarget index)

theorem previousStageAtomicOccupation_eq_coefficient
    (owner : GlobalParentOwner) (index : Nat) :
    previousStageAtomicOccupation owner index =
      (previousStageAdditiveCoefficient owner index : ℤ) := by
  rw [previousStageAtomicOccupation_eq_sum,
    previousStageAdditiveCoefficient,
    SourceGeneratedFiniteEffectiveCoefficient.effectiveCoefficient_eq_card_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  push_cast
  rfl

def ownerPrimeIndexOfPrime
    (owner : GlobalParentOwner) (index value : Nat)
    (isPrime : Nat.Prime value) (leTarget : value ≤ 2 * (index + 1)) :
    OwnerPrimeIndexAt owner index :=
  (ownerPrimeIndexEquivGenerated owner index).symm
    (primeIndexOfPrime value isPrime (by
      rw [evenTargetHistory_eq_generate,
        ArithmeticGeneration.UnitHistory.cardinalShadow_generate]
      exact leTarget))

@[simp] theorem ownerPrimeIndexOfPrime_value
    (owner : GlobalParentOwner) (index value : Nat)
    (isPrime : Nat.Prime value) (leTarget : value ≤ 2 * (index + 1)) :
    (ownerPrimeIndexOfPrime owner index value isPrime leTarget).1 = value := by
  unfold ownerPrimeIndexOfPrime
  have mapped := (ownerPrimeIndexEquivGenerated owner index).apply_symm_apply
    (primeIndexOfPrime value isPrime (by
      rw [evenTargetHistory_eq_generate,
        ArithmeticGeneration.UnitHistory.cardinalShadow_generate]
      exact leTarget))
  exact congrArg Subtype.val mapped

def currentEffectiveFibreOfPreviousStage
    {owner : GlobalParentOwner} {index : Nat}
    (fibre : PreviousStageAdditiveFibreAt owner index) :
    EffectiveAdditiveFibreAt (index + 1) := by
  have leftPrime : Nat.Prime fibre.1.1.1 := by
    simpa using ownerPrimeHistory_isPrime fibre.1.1
  have rightPrime : Nat.Prime fibre.1.2.1 := by
    simpa using ownerPrimeHistory_isPrime fibre.1.2
  have pairSum : fibre.1.1.1 + fibre.1.2.1 = nextEvenTarget index :=
    fibre.2
  have leftLe :
      fibre.1.1.1 ≤ (evenTargetHistory (index + 1)).cardinalShadow := by
    rw [evenTargetHistory_eq_generate,
      ArithmeticGeneration.UnitHistory.cardinalShadow_generate]
    simp [nextEvenTarget] at pairSum
    omega
  have rightLe :
      fibre.1.2.1 ≤ (evenTargetHistory (index + 1)).cardinalShadow := by
    rw [evenTargetHistory_eq_generate,
      ArithmeticGeneration.UnitHistory.cardinalShadow_generate]
    simp [nextEvenTarget] at pairSum
    omega
  let leftIndex : GeneratedPrimeIndexAt (index + 1) :=
    primeIndexOfPrime fibre.1.1.1 leftPrime leftLe
  let rightIndex : GeneratedPrimeIndexAt (index + 1) :=
    primeIndexOfPrime fibre.1.2.1 rightPrime rightLe
  refine ⟨(leftIndex, rightIndex), ?_⟩
  apply ArithmeticGeneration.UnitHistory.eq_of_cardinalShadow_eq
  rw [additiveEvaluation,
    ArithmeticGeneration.UnitHistory.cardinalShadow_parallel,
    evenTargetHistory_eq_generate,
    ArithmeticGeneration.UnitHistory.cardinalShadow_generate]
  rw [show (generatedPrimeHistory leftIndex).cardinalShadow =
        fibre.1.1.1 by simp [leftIndex],
    show (generatedPrimeHistory rightIndex).cardinalShadow =
        fibre.1.2.1 by simp [rightIndex]]
  simpa [nextEvenTarget] using pairSum

def previousStageFibreOfCurrentEffective
    (owner : GlobalParentOwner) (index : Nat)
    (fibre : EffectiveAdditiveFibreAt (index + 1)) :
    PreviousStageAdditiveFibreAt owner index := by
  have pairSum : fibre.1.1.1 + fibre.1.2.1 = nextEvenTarget index := by
    have landing := congrArg ArithmeticGeneration.UnitHistory.cardinalShadow fibre.2
    simpa [additiveEvaluation, evenTargetHistory_eq_generate,
      nextEvenTarget] using landing
  have leftPrime : Nat.Prime fibre.1.1.1 := by
    simpa using generatedPrimeHistory_isPrime fibre.1.1
  have rightPrime : Nat.Prime fibre.1.2.1 := by
    simpa using generatedPrimeHistory_isPrime fibre.1.2
  have leftLe : fibre.1.1.1 ≤ 2 * (index + 1) := by
    have rightTwo := rightPrime.two_le
    simp [nextEvenTarget] at pairSum
    omega
  have rightLe : fibre.1.2.1 ≤ 2 * (index + 1) := by
    have leftTwo := leftPrime.two_le
    simp [nextEvenTarget] at pairSum
    omega
  refine ⟨(ownerPrimeIndexOfPrime owner index fibre.1.1.1 leftPrime leftLe,
      ownerPrimeIndexOfPrime owner index fibre.1.2.1 rightPrime rightLe), ?_⟩
  simpa [previousStagePairCoordinate] using pairSum

def previousStageFibreEquivCurrentEffective
    (owner : GlobalParentOwner) (index : Nat) :
    PreviousStageAdditiveFibreAt owner index ≃
      EffectiveAdditiveFibreAt (index + 1) where
  toFun := currentEffectiveFibreOfPreviousStage
  invFun := previousStageFibreOfCurrentEffective owner index
  left_inv fibre := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [currentEffectiveFibreOfPreviousStage,
        previousStageFibreOfCurrentEffective]
  right_inv fibre := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [currentEffectiveFibreOfPreviousStage,
        previousStageFibreOfCurrentEffective]

theorem previousStageAdditiveCoefficient_eq_current
    (owner : GlobalParentOwner) (index : Nat) :
    previousStageAdditiveCoefficient owner index =
      generatedAdditiveCoefficient (index + 1) := by
  calc
    previousStageAdditiveCoefficient owner index =
        Fintype.card (PreviousStageAdditiveFibreAt owner index) :=
      SourceGeneratedFiniteEffectiveCoefficient.effectiveCoefficient_eq_card_fibre _ _
    _ = Fintype.card (EffectiveAdditiveFibreAt (index + 1)) :=
      Fintype.card_congr
        (previousStageFibreEquivCurrentEffective owner index)
    _ = generatedAdditiveCoefficient (index + 1) :=
      (generatedAdditiveCoefficient_eq_card_effectiveFibre (index + 1)).symm

theorem previousStageAtomicOccupation_eq_currentCoefficient
    (owner : GlobalParentOwner) (index : Nat) :
    previousStageAtomicOccupation owner index =
      (generatedAdditiveCoefficient (index + 1) : ℤ) := by
  rw [previousStageAtomicOccupation_eq_coefficient,
    previousStageAdditiveCoefficient_eq_current]

/-- The actual root-generated Fock trace cannot create the next target's
atomic occupation: its exact read at that target is zero. -/
theorem nextTargetAtomicAmplitude_forcedTrace_eq_zero
    (current : CanonicalUnitArithmeticRoot.Current) :
    atomicTargetAmplitude
        (ParticleWaveFockRuntime.scanIndex current + 1)
        (ParticleWaveFockRuntime.forcedTraceAt current) = 0 := by
  have update := congrArg
    (atomicTargetAmplitude (ParticleWaveFockRuntime.scanIndex current + 1))
    (ParticleWaveFockRuntime.targetState_eq_source_add_forcedTrace current)
  rw [map_add] at update
  have targetRead :
      atomicTargetAmplitude
          (ParticleWaveFockRuntime.scanIndex current + 1)
          (ParticleWaveFockRuntime.targetStateAt current) =
        (generatedAdditiveCoefficient
          (ParticleWaveFockRuntime.scanIndex current + 1) : ℤ) := by
    rw [ParticleWaveFockRuntime.targetStateAt,
      ParticleWaveFockRuntime.targetFieldAt,
      ParticleWaveFockRuntime.scanIndex_next]
    change atomicPrimePairOccupation
      (ParticleWaveFockRuntime.liveGlobalOwner
        (CanonicalUnitArithmeticRoot.next current))
      (ParticleWaveFockRuntime.scanIndex current + 1) = _
    exact atomicPrimePairOccupation_eq_generatedAdditiveCoefficient _ _
  have sourceRead :
      atomicTargetAmplitude
          (ParticleWaveFockRuntime.scanIndex current + 1)
          (ParticleWaveFockRuntime.sourceStateAt current) =
        (generatedAdditiveCoefficient
          (ParticleWaveFockRuntime.scanIndex current + 1) : ℤ) := by
    rw [ParticleWaveFockRuntime.sourceStateAt,
      ParticleWaveFockRuntime.sourceFieldAt]
    exact previousStageAtomicOccupation_eq_currentCoefficient _ _
  rw [targetRead, sourceRead] at update
  omega

#print axioms previousStageFibreEquivCurrentEffective
#print axioms previousStageAtomicOccupation_eq_currentCoefficient
#print axioms nextTargetAtomicAmplitude_forcedTrace_eq_zero

end
end ParticleWaveFockSuccessorPrimeFieldActionNoGo
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
