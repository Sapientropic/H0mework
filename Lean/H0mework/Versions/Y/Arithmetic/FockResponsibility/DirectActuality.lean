import H0mework.Versions.X.Arithmetic.FockUnitAction.FourierSibling
import H0mework.Versions.Y.Arithmetic.FockResponsibility.OccurrenceRuntime

/-!
# Direct prime-pair actuality settlement

The exact even-charge runtime occurrence generates its prime-pair actuality
object directly.  Settlement is identified with the already generated atomic
occupation/Fourier coefficient, without a pending claim, gated current,
paid-root compiler, or auxiliary process.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityDirect

open CanonicalUnitArithmeticClassicalGoldbachBridge
open CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open ArithmeticGeneration
open ParticleWaveFock
open ParticleWaveFockOccurrenceResponsibilityRuntime
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockRuntimeExactPrimeFourierSibling
open ParticleWaveFockRuntimePrimePairOccupation

noncomputable section

def directRuntimeActuality (depth : Nat) :
    RootGeneratedPrimePairActualityAt
      (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current
      (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).emittedOccurrence
      (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActive depth).down :=
  ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActualityPayload depth

theorem directRuntimeActuality_fixed_root (depth : Nat) :
    (directRuntimeActuality depth).sourceOccurrence =
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).emittedOccurrence ∧
      (directRuntimeActuality depth).exactEvenOccurrence.root.rootOccurrence =
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).emittedOccurrence :=
  ⟨(directRuntimeActuality depth).sourceOccurrence_eq,
    (directRuntimeActuality depth).exactEvenRoot⟩

theorem directRuntimeActuality_occupation_eq_generatedCoefficient
    (depth : Nat) :
    (directRuntimeActuality depth).occupation =
      (generatedAdditiveCoefficient (depth + 1) : ℤ) := by
  rw [(directRuntimeActuality depth).occupation_eq,
    (directRuntimeActuality depth).particle_eq]
  rw [(ParticleWaveFockRuntime.generateParticleWaveCurrent
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).emittedOccurrence
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActive depth).down).sourceState_eq]
  change atomicPrimePairOccupation
      (ParticleWaveFockRuntime.liveGlobalOwner
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current)
      (ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current) = _
  rw [atomicPrimePairOccupation_eq_generatedAdditiveCoefficient,
    ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt_scanIndex]

/-- An actual settlement forces the already generated actuality disposition
onto its settlement branch.  The obstruction branch is eliminated by the
settlement fibre itself, not by a new classifier. -/
theorem directRuntimeDisposition_is_settlement
    (depth : Nat)
    (settled : PrimePairActualitySettlementAt
      (directRuntimeActuality depth)) :
    ∃ generatedSettlement : PrimePairActualitySettlementAt
        (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) =
        .settlement generatedSettlement := by
  generalize dispositionEq :
    generatePrimePairActualityDisposition (directRuntimeActuality depth) =
      disposition
  cases disposition with
  | settlement generatedSettlement =>
      exact ⟨generatedSettlement, rfl⟩
  | obstruction blocked =>
      exact False.elim
        (blocked.residual.fibre_is_empty.false settled.fibre)

/-- Direct settlement remains a dependent face of the fixed named runtime:
the source occurrence, whole-ledger write, and canonical successor are those
of the same runtime tick. -/
theorem directRuntimeSettlement_keeps_fixed_root_wholeLedger_next
    (depth : Nat)
    (settled : PrimePairActualitySettlementAt
      (directRuntimeActuality depth)) :
    (∃ generatedSettlement : PrimePairActualitySettlementAt
        (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) =
        .settlement generatedSettlement) ∧
      ((directRuntimeActuality depth).sourceOccurrence =
          (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
              (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current ∧
        HEq
          (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).tick.generated.wholeLedgerWriteBack
          ((ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
              (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current) ∧
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).tick.nextCurrent =
          ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeFacade.process.stateAt
            (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeFacade.process.successor
              (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).state)) := by
  refine ⟨directRuntimeDisposition_is_settlement depth settled, ?_⟩
  simpa only [directRuntimeActuality] using
    ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActuality_keeps_occurrence_ledger_next
      depth

theorem directRuntimeSettlement_nonempty_iff_fourier_nonzero
    (depth : Nat) :
    Nonempty (PrimePairActualitySettlementAt
        (directRuntimeActuality depth)) ↔
      runtimePrimeOnlyFourierCoefficient depth ≠ 0 := by
  have coefficientIffFourier :
      (generatedAdditiveCoefficient (depth + 1) : ℤ) ≠ 0 ↔
        runtimePrimeOnlyFourierCoefficient depth ≠ 0 := by
    have coupling :=
      runtimeAtomicOccupation_ne_zero_iff_primeOnlyFourierCoefficient depth
    dsimp only at coupling
    have occupationReadback :=
      runtimeAtomicOccupation_eq_generatedAdditiveCoefficient depth
    dsimp only at occupationReadback
    rw [occupationReadback,
      CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt_scanIndex]
      at coupling
    exact coupling
  constructor
  · rintro ⟨settled⟩
    apply coefficientIffFourier.mp
    rw [← directRuntimeActuality_occupation_eq_generatedCoefficient]
    exact settled.occupation_ne_zero
  · intro fourierNonzero
    have coefficientNonzero := coefficientIffFourier.mpr fourierNonzero
    have coefficientPositive :
        0 < generatedAdditiveCoefficient (depth + 1) := by
      have naturalNonzero : generatedAdditiveCoefficient (depth + 1) ≠ 0 := by
        exact_mod_cast coefficientNonzero
      exact Nat.pos_of_ne_zero naturalNonzero
    obtain ⟨fibre⟩ :=
      (generatedAdditiveCoefficient_pos_iff_effectiveFibre (depth + 1)).mp
        coefficientPositive
    have fibreAtCurrent : EffectiveAdditiveFibreAt
        (ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
          (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current) := by
      simpa only [ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt_scanIndex]
        using fibre
    exact ⟨PrimePairActualitySettlementAt.ofFibre
      (directRuntimeActuality depth) fibreAtCurrent⟩

/-- Uniform direct settlement is exactly the classical Goldbach statement;
no process-layer payment can weaken or strengthen this mouth. -/
theorem allDirectRuntimeSettlements_iff_classicalGoldbach :
    (∀ depth : Nat,
      Nonempty (PrimePairActualitySettlementAt
        (directRuntimeActuality depth))) ↔
      CanonicalClassicalGoldbach := by
  constructor
  · intro allSettled
    apply classical_iff_all_effectiveFibres.mpr
    intro index indexInRange
    let depth := index - 1
    have depth_succ : depth + 1 = index := by
      dsimp only [depth]
      omega
    obtain ⟨settled⟩ := allSettled depth
    have occupationNonzero := settled.occupation_ne_zero
    rw [directRuntimeActuality_occupation_eq_generatedCoefficient,
      depth_succ] at occupationNonzero
    exact (generatedAdditiveCoefficient_pos_iff_effectiveFibre index).1
      (by omega)
  · intro classical depth
    have fibre := (classical_iff_all_effectiveFibres.mp classical)
      (depth + 1) (by omega)
    obtain ⟨fibre⟩ := fibre
    have fibreAtCurrent : EffectiveAdditiveFibreAt
        (ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
          (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth).current.visit.current) := by
      simpa only [ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt_scanIndex]
        using fibre
    exact ⟨PrimePairActualitySettlementAt.ofFibre
      (directRuntimeActuality depth) fibreAtCurrent⟩

/-- The prime `3` as an actual factorization-support atom of the generated
target `6`. -/
def targetSixThreePrimeIndex : GeneratedPrimeIndexAt 2 := by
  refine ⟨3, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  apply Nat.ne_of_gt
  apply Nat.prime_three.factorization_pos_of_dvd
  · rw [factorialHistory_cardinalShadow,
      evenTargetHistory_eq_generate,
      UnitHistory.cardinalShadow_generate]
    exact Nat.factorial_ne_zero 6
  · rw [factorialHistory_cardinalShadow,
      evenTargetHistory_eq_generate,
      UnitHistory.cardinalShadow_generate]
    exact Nat.dvd_factorial (by omega) (by omega)

def targetSixPrimePairCandidate : GeneratedPrimePairCandidateAt 2 :=
  (targetSixThreePrimeIndex, targetSixThreePrimeIndex)

/-- Actual `3+3=6` fibre, constructed from the same target's generated
factorization support. -/
def targetSixAdditiveFibre : EffectiveAdditiveFibreAt 2 :=
  ⟨targetSixPrimePairCandidate, rfl⟩

/-- At depth one the exact even occurrence is target `6`; its generated
`3+3` fibre settles actuality directly. -/
def depthOneTargetSixDirectSettlement :
    PrimePairActualitySettlementAt (directRuntimeActuality 1) := by
  have fibreAtCurrent : EffectiveAdditiveFibreAt
      (ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt 1).current.visit.current) := by
    rw [ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt_scanIndex]
    exact targetSixAdditiveFibre
  exact PrimePairActualitySettlementAt.ofFibre
    (directRuntimeActuality 1) fibreAtCurrent

end
end ParticleWaveFockPrimePairActualityDirect
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
