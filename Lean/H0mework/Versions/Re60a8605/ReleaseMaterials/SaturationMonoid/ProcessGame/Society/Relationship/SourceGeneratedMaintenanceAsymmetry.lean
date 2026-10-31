import H0mework.Society.Renewal.RenewalFaceSource

/-!
# Source-generated maintenance asymmetry

Relationship asymmetry is not an arbitrary pair of truth-valued tables.  One
exact maintenance event selects a permission type in the forward direction;
the reverse permission type must be empty.  The same event independently
selects an exact obligation/residual debt-flow fibre whose reverse is empty;
row names, slot addresses and party inequality cannot manufacture that flow.

These are local dependent faces.  They do not create relationship identity,
love, a standing registry, or operational root authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Relationship

universe uEvent uParty uPermission uFlow

/-- Exact source-selected renewal permission and constructive absence of the
reverse permission at the same event. -/
structure SourceGeneratedMaintenanceControlAsymmetryAt
    {Event : Type uEvent}
    {Party : Type uParty}
    (event : Event)
    (SelectedControlAt : Event → Party → Party → Type uPermission)
    (controller subject : Party) : Type uPermission where
  selected : SelectedControlAt event controller subject
  reverseEmpty : SelectedControlAt event subject controller → False

namespace SourceGeneratedMaintenanceControlAsymmetryAt

/-- Proposition readout of the exact permission type. -/
def ControlsAt
    {Event : Type uEvent}
    {Party : Type uParty}
    {event : Event}
    {SelectedControlAt : Event → Party → Party → Type uPermission}
    {controller subject : Party}
    (_control : SourceGeneratedMaintenanceControlAsymmetryAt event
      SelectedControlAt controller subject)
    (candidateEvent : Event) (first second : Party) : Prop :=
  Nonempty (SelectedControlAt candidateEvent first second)

theorem controls
    {Event : Type uEvent}
    {Party : Type uParty}
    {event : Event}
    {SelectedControlAt : Event → Party → Party → Type uPermission}
    {controller subject : Party}
    (control : SourceGeneratedMaintenanceControlAsymmetryAt event
      SelectedControlAt controller subject) :
    control.ControlsAt event controller subject :=
  ⟨control.selected⟩

theorem noReverseControl
    {Event : Type uEvent}
    {Party : Type uParty}
    {event : Event}
    {SelectedControlAt : Event → Party → Party → Type uPermission}
    {controller subject : Party}
    (control : SourceGeneratedMaintenanceControlAsymmetryAt event
      SelectedControlAt controller subject) :
    ¬ control.ControlsAt event subject controller := by
  rintro ⟨reverse⟩
  exact control.reverseEmpty reverse

end SourceGeneratedMaintenanceControlAsymmetryAt

/-- Exact source-selected debt flow and constructive absence of a reverse
flow at the *same* maintenance event.  The selected fibre is expected to
retain the actual obligation/residual consumer; this carrier does not infer
flow from row names, addresses, or party inequality. -/
structure SourceGeneratedMaintenanceDebtFlowAsymmetryAt
    {Event : Type uEvent}
    {Party : Type uParty}
    (event : Event)
    (SelectedDebtFlowAt : Event → Party → Party → Type uFlow)
    (debtor beneficiary : Party) : Type uFlow where
  selected : SelectedDebtFlowAt event debtor beneficiary
  reverseEmpty : SelectedDebtFlowAt event beneficiary debtor → False

namespace SourceGeneratedMaintenanceDebtFlowAsymmetryAt

/-- Proposition readout of the exact source-selected debt-flow fibre. -/
def DebtFlowsAt
    {Event : Type uEvent}
    {Party : Type uParty}
    {event : Event}
    {SelectedDebtFlowAt : Event → Party → Party → Type uFlow}
    {debtor beneficiary : Party}
    (_debt : SourceGeneratedMaintenanceDebtFlowAsymmetryAt event
      SelectedDebtFlowAt
      debtor beneficiary)
    (candidateEvent : Event) (first second : Party) : Prop :=
  Nonempty (SelectedDebtFlowAt candidateEvent first second)

theorem flows
    {Event : Type uEvent}
    {Party : Type uParty}
    {event : Event}
    {SelectedDebtFlowAt : Event → Party → Party → Type uFlow}
    {debtor beneficiary : Party}
    (debt : SourceGeneratedMaintenanceDebtFlowAsymmetryAt event
      SelectedDebtFlowAt
      debtor beneficiary) :
    debt.DebtFlowsAt event debtor beneficiary :=
  ⟨debt.selected⟩

/-- The source-selected reverse fibre is constructively empty. -/
theorem noReverseFlow
    {Event : Type uEvent}
    {Party : Type uParty}
    {event : Event}
    {SelectedDebtFlowAt : Event → Party → Party → Type uFlow}
    {debtor beneficiary : Party}
    (debt : SourceGeneratedMaintenanceDebtFlowAsymmetryAt event
      SelectedDebtFlowAt
      debtor beneficiary) :
    ¬ debt.DebtFlowsAt event beneficiary debtor := by
  rintro ⟨reverse⟩
  exact debt.reverseEmpty reverse

end SourceGeneratedMaintenanceDebtFlowAsymmetryAt

/-- Combined local signature: exact selected maintenance permission plus an
independently selected exact debt-flow fibre on the same event.  This is a
carrier/readout; source provenance is supplied by the selected fibres. -/
structure SourceGeneratedMaintenanceDebtAsymmetryAt
    {Event : Type uEvent}
    {Party : Type uParty}
    (event : Event)
    (SelectedControlAt : Event → Party → Party → Type uPermission)
    (SelectedDebtFlowAt : Event → Party → Party → Type uFlow)
    (controller subject debtor beneficiary : Party) : Type
      (max uPermission uFlow) where
  control : SourceGeneratedMaintenanceControlAsymmetryAt event
    SelectedControlAt controller subject
  debtFlow : SourceGeneratedMaintenanceDebtFlowAsymmetryAt event
    SelectedDebtFlowAt
    debtor beneficiary

end Relationship
end Society
end ProcessGame
end SaturationMonoid
