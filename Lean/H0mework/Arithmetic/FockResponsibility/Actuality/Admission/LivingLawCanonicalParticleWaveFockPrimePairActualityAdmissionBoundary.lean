import H0mework.Realization.Audit.DebtFirstWrite
import H0mework.Arithmetic.FockResponsibility.ActualityDebt

/-!
# Prime-pair actuality admission boundary

The existing debt-admission first-write ABI begins with an actual strict
`StepAt`.  For the prime-pair actuality law, the only such step already
contains an actual prime-pair settlement.  Therefore that ABI cannot install
the witness-free pending claim without assuming the target settlement first.
This is the exact cross-network installation boundary; no sibling root or
fallback continuation is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityAdmissionBoundary

open DebtAdmissionFirstWrite
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDebt

noncomputable section

abbrev PendingAdmissionEventAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :=
  SourceFixedDebtAdmissionEventAt (activationLaw actuality)
    (StateAt.pending : StateAt actuality)

/-- Reading an admission event reveals the actual prime-pair settlement
already stored in its strict step. -/
def settlementOfPendingAdmission
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    (event : PendingAdmissionEventAt actuality) :
    PrimePairActualitySettlementAt actuality :=
  event.step.receipt

/-- Conversely, an actual settlement generates the strict first write.  The
equivalence below therefore identifies exactly what the old ABI demands. -/
def pendingAdmissionOfSettlement
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    (settlement : PrimePairActualitySettlementAt actuality) :
    PendingAdmissionEventAt actuality :=
  SourceFixedDebtAdmissionEventAt.ofStep
    (StrictPaymentAt.ofSettlement settlement)

theorem pendingAdmission_nonempty_iff_settlement
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :
    Nonempty (PendingAdmissionEventAt actuality) ↔
      Nonempty (PrimePairActualitySettlementAt actuality) := by
  constructor
  · rintro ⟨event⟩
    exact ⟨settlementOfPendingAdmission event⟩
  · rintro ⟨settlement⟩
    exact ⟨pendingAdmissionOfSettlement settlement⟩

/-- A source-generated first-write token cannot weaken the mouth: it still
projects the settlement carried by the admission event in its type index. -/
def settlementOfGeneratedFirstWrite
    {N : WorldRelationNetwork}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    {support : N.Support}
    {event : PendingAdmissionEventAt actuality}
    (_generated : SourceGeneratedDebtAdmissionFirstWriteAt support event) :
    PrimePairActualitySettlementAt actuality :=
  settlementOfPendingAdmission event

end

end ParticleWaveFockPrimePairActualityAdmissionBoundary
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityAdmissionBoundary.pendingAdmission_nonempty_iff_settlement
