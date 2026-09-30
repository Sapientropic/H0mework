import H0mework.Versions.Y.Arithmetic.FockResponsibility.ActualityClaim
import H0mework.Foundation.Responsibility.DebtWorldReadback
import H0mework.Foundation.Responsibility.PendingClaimBirth

/-!
# Prime-pair actuality debt dynamics

The actuality runtime face's zero-field claim becomes the literal debt claim.
Pending actuality has one unit of responsibility.  Only an actual prime-pair
settlement can pay it; a faithful empty-fibre residual remains an exact
obstruction, and same-debt transport is absent.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityDebt

open DebtActivationWorld
open PendingClaimBirth
open ParticleWaveFockPrimePairActuality

noncomputable section

/-- The unresolved state stores no witness.  A settled state retains the
actual prime-pair receipt which discharged this exact occurrence's claim. -/
inductive StateAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) : Type
  | pending
  | settled (receipt : PrimePairActualitySettlementAt actuality)

def budget
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange} :
    StateAt actuality → Nat
  | .pending => 1
  | .settled _ => 0

/-- The only currently generated strict payment is the actual prime-pair
settlement itself.  It preserves the fixed actuality claim and spends the
single pending unit. -/
structure StrictPaymentAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    (source target : StateAt actuality) : Type where
  private mk ::
  receipt : PrimePairActualitySettlementAt actuality
  source_eq : source = .pending
  target_eq : target = .settled receipt

def StrictPaymentAt.ofSettlement
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    (receipt : PrimePairActualitySettlementAt actuality) :
    StrictPaymentAt (StateAt.pending : StateAt actuality)
      (.settled receipt) :=
  ⟨receipt, rfl, rfl⟩

theorem StrictPaymentAt.budget_lt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    {source target : StateAt actuality}
    (payment : StrictPaymentAt source target) :
    budget target < budget source := by
  rw [payment.source_eq, payment.target_eq]
  exact Nat.zero_lt_one

inductive SettlementAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange} :
    StateAt actuality → Type
  | actual (receipt : PrimePairActualitySettlementAt actuality) :
      SettlementAt (.settled receipt)

theorem SettlementAt.budget_zero
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    {state : StateAt actuality}
    (_settlement : SettlementAt state) : budget state = 0 := by
  cases _settlement
  rfl

inductive ExactObstructionAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange} :
    StateAt actuality → Type
  | residual (blocked : PrimePairActualityObstructionAt actuality) :
      ExactObstructionAt .pending

inductive DebtId
  | primePairActuality

/-- The debt claim is literally the zero-field claim already emitted by the
actuality face.  It is not a factor-process or residual-observer claim. -/
def activationLaw
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) : DebtActivationLaw where
  DebtState := StateAt actuality
  DebtId := DebtId
  DebtClaim := PrimePairActualityClaimAt actuality.exactEvenOccurrence
  debtId := .primePairActuality
  debtClaim := actuality.claim
  budget := budget
  StepAt := StrictPaymentAt
  step_budget_lt := StrictPaymentAt.budget_lt
  SettlementAt := SettlementAt
  settlement_budget_zero := SettlementAt.budget_zero
  supportTerminalLaw? := some
    { EventAt := SettlementAt
      settles := id }
  ObstructionAt := ExactObstructionAt

theorem activationLaw_claim_eq_generated
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :
    (activationLaw actuality).debtClaim =
      PrimePairActualityClaimAt.generate actuality.exactEvenOccurrence :=
  actuality.claim_eq

inductive GeneratedDispositionAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    (state : StateAt actuality) : Type
  | settlement (settled : SettlementAt state)
  | payment {target : StateAt actuality}
      (paid : StrictPaymentAt state target)
  | obstruction (blocked : ExactObstructionAt state)

/-- The existing effective-fibre classifier drives the exact actuality debt.
The positive branch emits the settlement payment; the faithful residual is
kept as an obstruction. -/
def generateDisposition
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    {actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange}
    (state : StateAt actuality) : GeneratedDispositionAt state := by
  cases state with
  | settled receipt => exact .settlement (.actual receipt)
  | pending =>
      cases generatePrimePairActualityDisposition actuality with
      | settlement settled =>
          exact .payment (StrictPaymentAt.ofSettlement settled)
      | obstruction blocked =>
          exact .obstruction (.residual blocked)

theorem transportAt_isEmpty
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange)
    (source target : (activationLaw actuality).DebtState) :
    IsEmpty ((activationLaw actuality).TransportAt source target) :=
  ⟨fun transport => nomatch transport⟩

/-! ## Installed package-valued pending face -/

/-- The exact actuality payload itself fixes its debt law, pending state and
positive budget.  `PayloadAt` is definitionally the generic pending package;
there is no external payload-to-claim mapper. -/
def actualityPendingClaimProjectionLaw :
    SourceNativePendingClaimProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift
    (1 ≤ CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)
  InactiveAt := fun _ {current} _occurrence => PLift
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current = 0)
  classify := ParticleWaveFockPrimePairActuality.actualityProjectionLaw.classify
  lawAt := fun _ {current} occurrence active =>
    activationLaw (generatePrimePairActuality current occurrence active.down)
  project := fun _ {_current} _occurrence _active =>
    { initial := StateAt.pending
      initialBudget_positive := Nat.zero_lt_one }

end

end ParticleWaveFockPrimePairActualityDebt
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
