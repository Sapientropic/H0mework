import H0mework.Foundation.Responsibility.DebtWorld

/-!
# Readback and finite inventory for debt activation

The constructors below expose old and debt rows, law-owned step/obstruction
receipts, debt-zero settlement readback, and an exact finite inventory
presentation for an active support.  They do not mint base terminal authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DebtActivationWorld

universe u

variable {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}

def oldEntry
    {support : N.Support} {state? : Option law.DebtState} :
    OpenResponsibilityAt N support →
      OpenResponsibilityAt (ExtendedNetwork N law) ⟨support, state?⟩
  | ⟨responsibility, opened⟩ => ⟨.inl responsibility, opened⟩

/-- The debt-inactive face is exactly the base responsibility fibre.  This
presentation preserves every proof-relevant old row and has no coordinate for
the absent debt summand. -/
def inactiveInventoryPresentation
    {support : N.Support} {Index : Type u}
    (base : ConstructivePresentation Index
      (OpenResponsibilityAt N support)) :
    ConstructivePresentation Index
      (OpenResponsibilityAt (ExtendedNetwork N law) ⟨support, none⟩) where
  forward := fun index =>
    oldEntry (law := law) (state? := none) (base.forward index)
  backward := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        exact base.backward ⟨oldResponsibility, opened⟩
    | inr _ => exact nomatch opened
  backward_forward := fun index => base.backward_forward index
  forward_backward := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        exact congrArg (oldEntry (law := law) (state? := none))
          (base.forward_backward ⟨oldResponsibility, opened⟩)
    | inr _ => exact nomatch opened

def debtEntry
    (support : N.Support) (state : law.DebtState) :
    OpenResponsibilityAt (ExtendedNetwork N law) ⟨support, some state⟩ :=
  ⟨.inr law.debtId, ULift.up (PLift.up rfl)⟩

@[simp] theorem oldEntry_claim
    {support : N.Support} {state? : Option law.DebtState}
    (entry : OpenResponsibilityAt N support) :
    (oldEntry (law := law) (state? := state?) entry).claim =
      .inl entry.claim :=
  rfl

@[simp] theorem oldEntry_budget
    {support : N.Support} {state? : Option law.DebtState}
    (entry : OpenResponsibilityAt N support) :
    (oldEntry (law := law) (state? := state?) entry).progressBudget =
      entry.progressBudget :=
  rfl

@[simp] theorem debtEntry_claim
    (support : N.Support) (state : law.DebtState) :
    (debtEntry (N := N) support state).claim = .inr law.debtClaim :=
  rfl

@[simp] theorem debtEntry_budget
    (support : N.Support) (state : law.DebtState) :
    (debtEntry (N := N) support state).progressBudget = law.budget state :=
  rfl

/-- At an active support the new side of the responsibility sum contains
exactly the law's fixed debt identity. -/
theorem active_debt_row_unique
    (support : N.Support) (state : law.DebtState) :
    Nonempty ((ExtendedNetwork N law).OpenAt
        ⟨support, some state⟩ (.inr law.debtId)) ∧
      ∀ debtId : law.DebtId,
        (ExtendedNetwork N law).OpenAt
          ⟨support, some state⟩ (.inr debtId) →
            debtId = law.debtId := by
  refine ⟨⟨ULift.up (PLift.up rfl)⟩, ?_⟩
  intro debtId opened
  rcases opened with ⟨⟨equality⟩⟩
  exact equality

/-- No new debt responsibility can be opened at an inactive support. -/
theorem inactive_no_debt
    (support : N.Support) (debtId : law.DebtId) :
    ¬ Nonempty ((ExtendedNetwork N law).OpenAt
      ⟨support, none⟩ (.inr debtId)) := by
  rintro ⟨opened⟩
  exact nomatch opened

def oldObstruction
    {support : N.Support} {state? : Option law.DebtState}
    (obstruction : N.ObstructionAt support) :
    (ExtendedNetwork N law).ObstructionAt ⟨support, state?⟩ :=
  .inl obstruction

/-- Base whole-support settlement authority lifts literally.  Debt-zero
evidence is deliberately absent from this constructor. -/
def baseSettlementReceipt
    (support : N.Support) {state? : Option law.DebtState}
    (receipt : N.DispositionAt support .supportSettlement) :
    (ExtendedNetwork N law).DispositionAt
      ⟨support, state?⟩ .supportSettlement := by
  change (match law.supportTerminalLaw? with
    | none => N.DispositionAt support .supportSettlement
    | some terminalLaw => N.DispositionAt support .supportSettlement ⊕
        ActiveAt law state? terminalLaw.EventAt)
  cases law.supportTerminalLaw? with
  | none => exact receipt
  | some _terminalLaw => exact Sum.inl receipt

/-- A source-generated phase terminal supplies whole-support settlement on
the active face without being retyped from local debt-zero evidence. -/
def debtSupportTerminalReceipt
    (support : N.Support) {state : law.DebtState}
    (terminal : law.SupportTerminalAt state) :
    (ExtendedNetwork N law).DispositionAt
      ⟨support, some state⟩ .supportSettlement := by
  unfold DebtActivationLaw.SupportTerminalAt at terminal
  cases terminalLaw_eq : law.supportTerminalLaw? with
  | none =>
      rw [terminalLaw_eq] at terminal
      exact nomatch terminal
  | some terminalLaw =>
      rw [terminalLaw_eq] at terminal
      change (match law.supportTerminalLaw? with
        | none => N.DispositionAt support .supportSettlement
        | some terminalLaw => N.DispositionAt support .supportSettlement ⊕
            terminalLaw.EventAt state)
      rw [terminalLaw_eq]
      exact Sum.inr terminal

def debtObstruction
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    (ExtendedNetwork N law).ObstructionAt ⟨support, some state⟩ :=
  .inr obstruction

@[simp] theorem debtObstruction_claim
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    (ExtendedNetwork N law).obstructionClaim
      (debtObstruction (N := N) support obstruction) =
        .inr law.debtClaim :=
  rfl

def debtStepReceipt
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target) :
    (ExtendedNetwork N law).DispositionAt
      ⟨support, some source⟩ .transfer :=
  .inr (.inl ⟨target, step⟩)

/-- Actual same-debt transport receipt.  It is disjoint from strict payment
and carries the target selected by the installed transport law. -/
def debtTransportReceipt
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target) :
    (ExtendedNetwork N law).DispositionAt
      ⟨support, some source⟩ .transfer :=
  .inr (.inr ⟨target, transport⟩)

def debtObstructionReceipt
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    (ExtendedNetwork N law).DispositionAt
      ⟨support, some state⟩ .lawSurfaceExtension :=
  .inr obstruction

/-- A generated step changes activation state without laundering the debt's
fixed semantic claim. -/
theorem debtStep_claim_invariant
    (support : N.Support) {source target : law.DebtState}
    (_step : law.StepAt source target) :
    (debtEntry (N := N) support source).claim =
      (debtEntry (N := N) support target).claim :=
  rfl

/-- Budget descent is source-owned by the same generated step receipt. -/
theorem debtStep_budget_lt
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target) :
    (debtEntry (N := N) support target).progressBudget <
      (debtEntry (N := N) support source).progressBudget :=
  law.step_budget_lt step

/-- Same-debt transport may preserve budget but cannot refill it. -/
theorem debtTransport_budget_le
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target) :
    (debtEntry (N := N) support target).progressBudget ≤
      (debtEntry (N := N) support source).progressBudget :=
  law.transport_budget_le transport

/-- A settlement receipt is available only at a law-certified zero budget. -/
theorem debtSettlement_budget_zero
    (support : N.Support) {state : law.DebtState}
    (settlement : law.SettlementAt state) :
    (debtEntry (N := N) support state).progressBudget = 0 :=
  law.settlement_budget_zero settlement

/-- Phase-terminal authority contains a settlement and therefore certifies
zero debt budget, but zero debt alone cannot construct the phase event. -/
theorem debtSupportTerminal_budget_zero
    (support : N.Support) {state : law.DebtState}
    (terminal : law.SupportTerminalAt state) :
    (debtEntry (N := N) support state).progressBudget = 0 :=
  debtSettlement_budget_zero support (law.supportTerminal_settles terminal)

/-- The same generated step also preserves root debt lineage. -/
def debtStep_lineage
    (support : N.Support) {source target : law.DebtState}
    (_step : law.StepAt source target) :
    RootDebtLineageAt (ExtendedNetwork N law)
      (debtEntry (N := N) support source)
      (debtEntry (N := N) support target) where
  lineage_eq := rfl
  claim_eq := rfl

/-- Same-debt transport preserves the exact rooted debt identity. -/
def debtTransport_lineage
    (support : N.Support) {source target : law.DebtState}
    (_transport : law.TransportAt source target) :
    RootDebtLineageAt (ExtendedNetwork N law)
      (debtEntry (N := N) support source)
      (debtEntry (N := N) support target) where
  lineage_eq := rfl
  claim_eq := rfl

/-- Add the unique active debt row to any constructive presentation of the
base inventory.  `none` indexes the debt row; `some i` indexes old row `i`. -/
def activeInventoryPresentation
    {support : N.Support} {Index : Type u}
    (state : law.DebtState)
    (base : ConstructivePresentation Index (OpenResponsibilityAt N support)) :
    ConstructivePresentation (Option Index)
      (OpenResponsibilityAt (ExtendedNetwork N law)
        ⟨support, some state⟩) where
  forward
    | none => debtEntry (N := N) support state
    | some index => oldEntry (state? := some state) (base.forward index)
  backward
    | ⟨.inl responsibility, opened⟩ =>
        some (base.backward ⟨responsibility, opened⟩)
    | ⟨.inr _, _⟩ => none
  backward_forward := by
    intro index?
    cases index? with
    | none => rfl
    | some index =>
        exact congrArg some (base.backward_forward index)
  forward_backward := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl responsibility =>
        exact congrArg
          (oldEntry (law := law) (state? := some state))
          (base.forward_backward ⟨responsibility, opened⟩)
    | inr debtId =>
        rcases opened with ⟨⟨equality⟩⟩
        subst debtId
        rfl

end DebtActivationWorld
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
