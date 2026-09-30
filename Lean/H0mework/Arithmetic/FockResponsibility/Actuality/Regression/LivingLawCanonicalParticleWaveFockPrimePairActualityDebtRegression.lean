import H0mework.Arithmetic.FockResponsibility.ActualityDebt
import H0mework.Arithmetic.FockResponsibility.Actuality.Admission.LivingLawCanonicalParticleWaveFockPrimePairActualityAdmissionBoundary
import H0mework.Arithmetic.FockResponsibility.OccurrenceRuntime
import H0mework.Arithmetic.GoldbachFourier.ClassicalBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityDebtRegression

open ArithmeticGeneration
open CanonicalUnitArithmeticClassicalGoldbachBridge
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open DebtAdmissionFirstWrite
open ParticleWaveFockOccurrenceResponsibilityRuntime
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDebt
open ParticleWaveFockPrimePairActualityAdmissionBoundary
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

def actuality : RootGeneratedPrimePairActualityAt
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt
      1).current.visit.current
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt
      1).emittedOccurrence
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActive 1).down :=
  ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActualityPayload 1

theorem depthOneIndex :
    CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
      (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt
        1).current.visit.current = 2 := by
  change ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex
    (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt
      1).current.visit.current = 2
  rw [ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt_scanIndex]

def targetSixThreeIndex : GeneratedPrimeIndexAt 2 :=
  primeIndexOfPrime 3 Nat.prime_three (by
    rw [evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]
    omega)

def targetSixFibre : EffectiveAdditiveFibreAt 2 := by
  refine ⟨(targetSixThreeIndex, targetSixThreeIndex), ?_⟩
  apply UnitHistory.eq_of_cardinalShadow_eq
  simp [additiveEvaluation, targetSixThreeIndex,
    evenTargetHistory_eq_generate]

def depthOneFibre : EffectiveAdditiveFibreAt
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
      (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt
        1).current.visit.current) := by
  rw [depthOneIndex]
  exact targetSixFibre

def depthOneSettlement : PrimePairActualitySettlementAt actuality :=
  PrimePairActualitySettlementAt.ofFibre actuality depthOneFibre

def depthOnePayment : StrictPaymentAt
    (StateAt.pending : StateAt actuality)
    (.settled depthOneSettlement) :=
  StrictPaymentAt.ofSettlement depthOneSettlement

def depthOneAdmissionEvent : PendingAdmissionEventAt actuality :=
  pendingAdmissionOfSettlement depthOneSettlement

def depthOneAdmissionFirstWrite : SourceGeneratedDebtAdmissionFirstWriteAt
    (N := CanonicalUnitArithmeticRoot.N)
    (CanonicalUnitArithmeticRoot.finiteVisit 1).current
    depthOneAdmissionEvent :=
  DebtAdmissionFirstWrite.generate
    (N := CanonicalUnitArithmeticRoot.N)
    (law := activationLaw actuality)
    (CanonicalUnitArithmeticRoot.finiteVisit 1).current depthOneAdmissionEvent

theorem depth_one_first_write_already_contains_actual_settlement :
    settlementOfGeneratedFirstWrite depthOneAdmissionFirstWrite =
      depthOneSettlement :=
  rfl

theorem depth_one_payment_is_strict :
    budget (.settled depthOneSettlement) <
      budget (StateAt.pending : StateAt actuality) :=
  depthOnePayment.budget_lt

theorem depth_one_debt_claim_matches_named_face_claim :
    (activationLaw actuality).debtClaim =
      PrimePairActualityClaimAt.generate actuality.exactEvenOccurrence :=
  activationLaw_claim_eq_generated actuality

theorem depth_one_pending_disposition_is_source_generated :
    Nonempty (GeneratedDispositionAt
      (StateAt.pending : StateAt actuality)) :=
  ⟨generateDisposition (StateAt.pending : StateAt actuality)⟩

theorem depth_one_transport_is_empty
    (source target : (activationLaw actuality).DebtState) :
    IsEmpty ((activationLaw actuality).TransportAt source target) :=
  transportAt_isEmpty actuality source target

/-- A factor-process payment has the wrong semantic claim and cannot inhabit
the actuality law's strict-payment family. -/
example
    {source target : ParticleWaveFockOccurrenceResponsibility.State 2}
    (_oldPayment : ParticleWaveFockOccurrenceResponsibility.StrictPaymentAt
      source target) :
    StrictPaymentAt (StateAt.pending : StateAt actuality)
      (.settled depthOneSettlement) := by
  fail_if_success exact _oldPayment
  exact depthOnePayment

#print axioms depth_one_payment_is_strict
#print axioms depth_one_first_write_already_contains_actual_settlement
#print axioms depth_one_debt_claim_matches_named_face_claim
#print axioms depth_one_pending_disposition_is_source_generated
#print axioms depth_one_transport_is_empty

end
end ParticleWaveFockPrimePairActualityDebtRegression
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
