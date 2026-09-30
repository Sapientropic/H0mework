import H0mework.Foundation.Responsibility.DebtWorldReadback
import H0mework.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Settlement.ClozelBurnolSpectralActualitySettlement

/-!
# One-unit spectral actuality debt

An unresolved zero-field claim has budget one.  Its only payment contains an
actual normalized physical kernel settlement and reaches budget zero.  No
negative classifier or characteristic obstruction is available from the
current source, so the obstruction fibre is empty rather than fabricated.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace SpectralActualityDebt

open DebtActivationWorld
open SpectralActuality

noncomputable section

inductive StateAt
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial) : Type
  | pending
  | settled (receipt : SpectralActualitySettlementAt event)

def budget
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial} :
    StateAt event → Nat
  | .pending => 1
  | .settled _ => 0

/-- The only strict payment literally contains the characteristic
settlement. -/
structure StrictPaymentAt
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial}
    (source target : StateAt event) : Type where
  private mk ::
  receipt : SpectralActualitySettlementAt event
  source_eq : source = .pending
  target_eq : target = .settled receipt

def StrictPaymentAt.ofSettlement
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial}
    (receipt : SpectralActualitySettlementAt event) :
    StrictPaymentAt (StateAt.pending : StateAt event) (.settled receipt) :=
  ⟨receipt, rfl, rfl⟩

theorem StrictPaymentAt.budget_lt
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial}
    {source target : StateAt event}
    (payment : StrictPaymentAt source target) :
    budget target < budget source := by
  rw [payment.source_eq, payment.target_eq]
  exact Nat.zero_lt_one

inductive SettlementAt
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial} :
    StateAt event → Type
  | actual (receipt : SpectralActualitySettlementAt event) :
      SettlementAt (.settled receipt)

theorem SettlementAt.budget_zero
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    {event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial}
    {state : StateAt event}
    (_settlement : SettlementAt state) : budget state = 0 := by
  cases _settlement
  rfl

inductive DebtId
  | spectralActuality

def activationLaw
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial) :
    DebtActivationLaw where
  DebtState := StateAt event
  DebtId := DebtId
  DebtClaim := SpectralActualityClaimAt event
  debtId := .spectralActuality
  debtClaim := SpectralActualityClaimAt.generate event
  budget := budget
  StepAt := StrictPaymentAt
  step_budget_lt := StrictPaymentAt.budget_lt
  SettlementAt := SettlementAt
  settlement_budget_zero := SettlementAt.budget_zero
  supportTerminalLaw? := some
    { EventAt := SettlementAt
      settles := id }
  ObstructionAt := fun _state => PEmpty

theorem activationLaw_claim_eq_generated
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial) :
    (activationLaw event).debtClaim = SpectralActualityClaimAt.generate event :=
  rfl

theorem obstructionAt_isEmpty
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial)
    (state : (activationLaw event).DebtState) :
    IsEmpty ((activationLaw event).ObstructionAt state) :=
  ⟨fun obstruction => nomatch obstruction⟩

theorem transportAt_isEmpty
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial)
    (source target : (activationLaw event).DebtState) :
    IsEmpty ((activationLaw event).TransportAt source target) :=
  ⟨fun transport => nomatch transport⟩

theorem pendingPayment_nonempty_iff_settlement
    {coordinate : ℂ}
    {zero : generatedRiemannZeta AnalyticOwner coordinate = 0}
    {nontrivial : NontrivialZeroTag coordinate}
    (event : GeneratedNontrivialZeroEventAt coordinate zero nontrivial) :
    Nonempty (Σ target : StateAt event,
      StrictPaymentAt (StateAt.pending : StateAt event) target) ↔
      Nonempty (SpectralActualitySettlementAt event) := by
  constructor
  · rintro ⟨⟨target, payment⟩⟩
    exact ⟨payment.receipt⟩
  · rintro ⟨settlement⟩
    exact ⟨⟨StateAt.settled settlement,
      StrictPaymentAt.ofSettlement settlement⟩⟩

end
end SpectralActualityDebt
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
