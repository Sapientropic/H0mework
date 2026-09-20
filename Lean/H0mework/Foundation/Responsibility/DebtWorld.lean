import H0mework.Foundation.Source.Root

/-!
# Source-neutral debt activation in a world relation network

This kernel extends an arbitrary world network by a single law-owned debt row
at each active support.  Old rows embed literally.  The activation state only
changes the law-owned progress budget: debt identity and claim stay fixed.

No root compiler or Noetherian closure is installed here.  Steps,
transports and obstructions remain law-indexed world receipts.  A settlement
certifies only that the tracked debt has reached zero; whole-support terminal
authority must come from either the base world or an independently installed
source-generated phase-terminal event.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DebtActivationWorld

universe u

/-- Optional source family for whole-phase terminal events.  Every event
contains the local debt settlement it discharges; the converse is absent. -/
structure DebtSupportTerminalLaw
    (DebtState : Type u) (SettlementAt : DebtState → Type u) : Type (u + 1) where
  EventAt : DebtState → Type u
  settles : {state : DebtState} → EventAt state → SettlementAt state

/-- Optional same-debt transport family.  A transport may preserve budget but
may never refill it; strict payment remains the separate `StepAt` branch. -/
structure DebtTransportLaw
    (DebtState : Type u) (budget : DebtState → Nat) : Type (u + 1) where
  EventAt : DebtState → DebtState → Type u
  budget_le : {source target : DebtState} →
    EventAt source target → budget target ≤ budget source

/-- Source-neutral data which may activate one persistent debt identity at a
world support.  `StepAt` is deliberately indexed by both states, so an actual
receipt—not a caller-selected update—determines which transition exists. -/
structure DebtActivationLaw : Type (u + 1) where
  DebtState : Type u
  DebtId : Type u
  DebtClaim : Type u
  debtId : DebtId
  debtClaim : DebtClaim
  budget : DebtState → Nat
  StepAt : DebtState → DebtState → Type u
  step_budget_lt : {source target : DebtState} →
    StepAt source target → budget target < budget source
  /-- Optional actual transport at the same debt identity.  Omission makes
  the added transport event fibre definitionally empty. -/
  transportLaw? : Option (DebtTransportLaw DebtState budget) := none
  SettlementAt : DebtState → Type u
  settlement_budget_zero : {state : DebtState} →
    SettlementAt state → budget state = 0
  /-- Absence is definitionally the former base-only ABI.  Presence installs
  an independent phase-event family, not a Boolean permission bit. -/
  supportTerminalLaw? : Option (DebtSupportTerminalLaw DebtState SettlementAt) :=
    none
  ObstructionAt : DebtState → Type u

/-- Phase-terminal event family.  It is definitionally empty for every
pre-existing activation law which omits `supportTerminalLaw?`. -/
def DebtActivationLaw.SupportTerminalAt
    (law : DebtActivationLaw.{u}) (state : law.DebtState) : Type u :=
  match law.supportTerminalLaw? with
  | none => PEmpty
  | some terminalLaw => terminalLaw.EventAt state

/-- Same-debt transport event.  The default family is empty. -/
def DebtActivationLaw.TransportAt
    (law : DebtActivationLaw.{u})
    (source target : law.DebtState) : Type u :=
  match law.transportLaw? with
  | none => PEmpty
  | some transportLaw => transportLaw.EventAt source target

/-- Every installed transport is budget non-refilling. -/
theorem DebtActivationLaw.transport_budget_le
    (law : DebtActivationLaw.{u}) {source target : law.DebtState} :
    law.TransportAt source target → law.budget target ≤ law.budget source := by
  intro transport
  unfold DebtActivationLaw.TransportAt at transport
  cases transportLaw_eq : law.transportLaw? with
  | none =>
      rw [transportLaw_eq] at transport
      exact nomatch transport
  | some transportLaw =>
      rw [transportLaw_eq] at transport
      exact transportLaw.budget_le transport

/-- Every phase-terminal event exposes its contained local settlement. -/
def DebtActivationLaw.supportTerminal_settles
    (law : DebtActivationLaw.{u}) {state : law.DebtState} :
    law.SupportTerminalAt state → law.SettlementAt state := by
  intro terminal
  unfold DebtActivationLaw.SupportTerminalAt at terminal
  cases terminalLaw_eq : law.supportTerminalLaw? with
  | none =>
      rw [terminalLaw_eq] at terminal
      exact nomatch terminal
  | some terminalLaw =>
      rw [terminalLaw_eq] at terminal
      exact terminalLaw.settles terminal

def ActiveAt
    (law : DebtActivationLaw.{u})
    (state? : Option law.DebtState)
    (Family : law.DebtState → Type u) : Type u :=
  match state? with
  | none => PEmpty
  | some state => Family state

/-- One generated step receipt retains its target state in the receipt type. -/
abbrev GeneratedStepAt
    (law : DebtActivationLaw.{u}) (state : law.DebtState) : Type u :=
  Sigma fun target => law.StepAt state target

abbrev GeneratedTransportAt
    (law : DebtActivationLaw.{u}) (state : law.DebtState) : Type u :=
  Sigma fun target => law.TransportAt state target

def DebtOpenAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u}) :
    (N.Support × Option law.DebtState) →
      (N.Responsibility ⊕ law.DebtId) → Type u
  | ⟨support, _⟩, .inl responsibility => N.OpenAt support responsibility
  | ⟨_, none⟩, .inr _ => PEmpty
  | ⟨_, some _⟩, .inr debtId =>
      ULift.{u, 0} (PLift (debtId = law.debtId))

def DebtOpenClaimAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u}) :
    {support : N.Support × Option law.DebtState} →
      {responsibility : N.Responsibility ⊕ law.DebtId} →
        DebtOpenAt N law support responsibility →
          (N.Claim ⊕ law.DebtClaim)
  | ⟨_, _⟩, .inl _, opened => .inl (N.openClaimAt opened)
  | ⟨_, none⟩, .inr _, opened => nomatch opened
  | ⟨_, some _⟩, .inr _, _ => .inr law.debtClaim

def DebtOpenBudgetAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u}) :
    {support : N.Support × Option law.DebtState} →
      {responsibility : N.Responsibility ⊕ law.DebtId} →
        DebtOpenAt N law support responsibility → Nat
  | ⟨_, _⟩, .inl _, opened => N.openProgressBudgetAt opened
  | ⟨_, none⟩, .inr _, opened => nomatch opened
  | ⟨_, some state⟩, .inr _, _ => law.budget state

def DebtHoldsAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u}) :
    (N.Support × Option law.DebtState) →
      (N.Claim ⊕ law.DebtClaim) → Type u
  | ⟨support, _⟩, .inl claim => N.HoldsAt support claim
  | ⟨_, none⟩, .inr _ => PEmpty
  | ⟨_, some _⟩, .inr claim =>
      ULift.{u, 0} (PLift (claim = law.debtClaim))

def DebtObstructionAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u})
    (support : N.Support × Option law.DebtState) : Type u :=
  N.ObstructionAt support.1 ⊕
    ActiveAt law support.2 law.ObstructionAt

def DebtSemanticChangeAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u})
    (support : N.Support × Option law.DebtState) :
    (N.Claim ⊕ law.DebtClaim) →
      (N.Claim ⊕ law.DebtClaim) → Type u
  | .inl oldClaim, .inl newClaim =>
      N.SemanticChangeAt support.1 oldClaim newClaim
  | _, _ => PEmpty

def DebtDispositionAt
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u})
    (support : N.Support × Option law.DebtState) :
    WorldDispositionKind → Type u
  | .supportSettlement =>
      match law.supportTerminalLaw? with
      | none => N.DispositionAt support.1 .supportSettlement
      | some terminalLaw =>
          N.DispositionAt support.1 .supportSettlement ⊕
            ActiveAt law support.2 terminalLaw.EventAt
  | .transfer =>
      N.DispositionAt support.1 .transfer ⊕
        ActiveAt law support.2 (fun state =>
          GeneratedStepAt law state ⊕ GeneratedTransportAt law state)
  | .lawSurfaceExtension =>
      N.DispositionAt support.1 .lawSurfaceExtension ⊕
        ActiveAt law support.2 law.ObstructionAt

/-- The canonical world extension.  Support-local coordinates remain those of
the base occurrence; `Option DebtState` records whether its debt row is live. -/
def extendedNetwork
    (N : WorldRelationNetwork.{u})
    (law : DebtActivationLaw.{u}) : WorldRelationNetwork.{u} where
  Support := N.Support × Option law.DebtState
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  Responsibility := N.Responsibility ⊕ law.DebtId
  Claim := N.Claim ⊕ law.DebtClaim
  anchorAt := fun support => N.anchorAt support.1
  incidenceAt := fun support => N.incidenceAt support.1
  lineageAt := fun support => N.lineageAt support.1
  OpenAt := DebtOpenAt N law
  openClaimAt := DebtOpenClaimAt N law
  openProgressBudgetAt := DebtOpenBudgetAt N law
  HoldsAt := DebtHoldsAt N law
  ObstructionAt := DebtObstructionAt N law
  obstructionClaim := by
    intro support obstruction
    cases obstruction with
    | inl old => exact .inl (N.obstructionClaim old)
    | inr _ => exact .inr law.debtClaim
  SemanticChangeAt := DebtSemanticChangeAt N law
  DispositionAt := DebtDispositionAt N law

abbrev ExtendedNetwork
    (N : WorldRelationNetwork.{u}) (law : DebtActivationLaw.{u}) :=
  extendedNetwork N law

end DebtActivationWorld
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
