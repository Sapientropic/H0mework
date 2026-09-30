import H0mework.Versions.Y.Arithmetic.FockResponsibility.ProcessReceipt

/-!
# Target-six compiled process action

At depth one the existing atomic runtime current is the canonical split
`2 + 4`.  Its source-selected factor-two repair is a genuine physical action
and lands at `3 + 3`.  The target classifier then emits the prime-pair
terminal, yielding the action receipt used by the actuality debt.

This construction consumes the production compiler directly.  It does not
import a regression fixture or use the old runtime successor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityTargetSixProcessAction

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticFullFactorRepairReachabilityProducer
open ParticleWaveFockAtomicDebtRuntime
open ParticleWaveFockAtomicDynamicsRuntime
open ParticleWaveFockAtomicProcess
open ParticleWaveFockAtomicSectorDebt
open ParticleWaveFockPrimePairActualityProcessAction

noncomputable section

theorem runtimeIndex_one : RuntimeIndex 1 = 2 := by
  exact ParticleWaveFockAtomicDynamicsRuntime.runtimeAt_scanIndex 1

theorem repairTargetValue_runtimeIndex_one :
    repairTargetValue (RuntimeIndex 1) = 6 := by
  rw [repairTargetValue, evenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate, runtimeIndex_one]

theorem sourceLeft_eq_two :
    splitLeft (runtimeDebtState 1).1.current = 2 := by
  rw [runtimeDebtState_eq_initial]
  rfl

theorem sourceRight_eq_four :
    splitRight (runtimeDebtState 1).1.current = 4 := by
  rw [runtimeDebtState_eq_initial]
  change splitRight (canonicalSplit (RuntimeIndex 1)
    (ParticleWaveFockAtomicDynamicsRuntime.runtimeActive 1).down) = 4
  rw [canonicalSplit_right, repairTargetValue_runtimeIndex_one]

theorem sourceRight_notPrime :
    ¬ Nat.Prime (splitRight (runtimeDebtState 1).1.current) := by
  rw [sourceRight_eq_four]
  exact Nat.not_prime_of_dvd_of_lt
    (by norm_num : 2 ∣ 4) (by norm_num) (by norm_num)

def sourceRepairAlternative :
    FactorRepairAlternativeAt (runtimeDebtState 1).1.current :=
  generatedRightFactorAlternative
    (runtimeDebtState 1).1.current sourceRight_notPrime

theorem sourceRepairAlternative_factor_eq_two :
    sourceRepairAlternative.factor = 2 := by
  change Nat.minFac (splitRight (runtimeDebtState 1).1.current) = 2
  rw [sourceRight_eq_four]
  norm_num [Nat.minFac]

theorem sourceClassifier_eq_repair :
    (fullFactorDecayLaw (RuntimeIndex 1)).classify
        (runtimeDebtState 1).1.current =
      Sum.inr (FactorDecayChannelAt.repair sourceRepairAlternative) := by
  change fullFactorDecayClassify (runtimeDebtState 1).1.current = _
  unfold fullFactorDecayClassify
  have sourceLeftPrime :
      Nat.Prime (splitLeft (runtimeDebtState 1).1.current) := by
    rw [sourceLeft_eq_two]
    exact Nat.prime_two
  rw [show (fullFactorRepairLaw (RuntimeIndex 1)).classify
      (runtimeDebtState 1).1.current = Sum.inr sourceRepairAlternative by
    simp only [fullFactorRepairLaw]
    rw [dif_pos sourceLeftPrime, dif_neg sourceRight_notPrime]
    rfl]
  rfl

/-- The production compiler selects its actual step branch at depth one. -/
def targetSixCompiledStep : CompiledStepAt 1 := by
  cases compiled_eq : compileDisposition 1 with
  | settlement compiled =>
      exact False.elim
        (sourceRight_notPrime compiled.settlement.generated.terminal.rightPrime)
  | step compiled => exact compiled
  | obstruction compiled =>
      exact False.elim (compiled.blocked.keyNotRemaining
        (runtimeDebtState_contains_every_structuralKey 1
          compiled.blocked.structuralKey))

theorem sourceChannel_eq_repair :
    targetSixCompiledStep.step.generated.channel =
      .repair sourceRepairAlternative := by
  exact targetSixCompiledStep.step.generated.channel_eq_preferredRepair
    sourceRepairAlternative sourceClassifier_eq_repair
      (repairFactorTwo_physicalProgress sourceRepairAlternative
        sourceRepairAlternative_factor_eq_two)

theorem generatedTarget_eq_repairTarget :
    targetSixCompiledStep.target.1.current = sourceRepairAlternative.target := by
  rw [targetSixCompiledStep.step.target_eq,
    targetSixCompiledStep.step.generated.target_eq]
  change targetSixCompiledStep.step.generated.channel.target = _
  rw [sourceChannel_eq_repair]
  rfl

theorem generatedTarget_is_three_three :
    splitLeft targetSixCompiledStep.target.1.current = 3 ∧
      splitRight targetSixCompiledStep.target.1.current = 3 := by
  rw [generatedTarget_eq_repairTarget]
  constructor
  · have leftRead := generatedRightFactorAlternative_target_left
      (runtimeDebtState 1).1.current sourceRight_notPrime
    change splitLeft sourceRepairAlternative.target =
      splitLeft (runtimeDebtState 1).1.current +
        (sourceRepairAlternative.factor - 1) at leftRead
    rw [sourceLeft_eq_two, sourceRepairAlternative_factor_eq_two] at leftRead
    norm_num at leftRead
    exact leftRead
  · have leftRead := generatedRightFactorAlternative_target_left
      (runtimeDebtState 1).1.current sourceRight_notPrime
    change splitLeft sourceRepairAlternative.target =
      splitLeft (runtimeDebtState 1).1.current +
        (sourceRepairAlternative.factor - 1) at leftRead
    rw [sourceLeft_eq_two, sourceRepairAlternative_factor_eq_two] at leftRead
    norm_num at leftRead
    have landing := split_landing sourceRepairAlternative.target
    rw [leftRead] at landing
    change splitRight sourceRepairAlternative.target = 3
    rw [repairTargetValue_runtimeIndex_one] at landing
    omega

def generatedTargetPrimePair :
    PrimePairTerminalAt targetSixCompiledStep.target.1.current :=
  ⟨by rw [generatedTarget_is_three_three.1]; exact Nat.prime_three,
    by rw [generatedTarget_is_three_three.2]; exact Nat.prime_three⟩

def targetSixActionReceipt : GeneratedActionReceiptAt 1 :=
  GeneratedActionReceiptAt.ofCompiled targetSixCompiledStep

def targetSixTerminalReadout : TerminalReadoutAt targetSixActionReceipt :=
  TerminalReadoutAt.ofPrimePair targetSixActionReceipt
    generatedTargetPrimePair

end

end ParticleWaveFockPrimePairActualityTargetSixProcessAction
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
