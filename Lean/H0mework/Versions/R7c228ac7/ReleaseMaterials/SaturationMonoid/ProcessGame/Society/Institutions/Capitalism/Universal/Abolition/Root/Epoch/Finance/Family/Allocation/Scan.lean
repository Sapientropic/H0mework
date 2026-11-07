import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Allocation.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

def allocateAt (origin : ActualItem sources depths counts) (state : (process sources depths counts).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) : Allocation sources depths counts state available :=
  if within : position < state.current.slots.length then
    match present : state.current.slots.get ⟨position, within⟩ with
    | .terminal _ => Allocation.idle sources depths counts state available nonnegative
    | .live obligation =>
        match readReview sources depths counts obligation.content origin with
        | none => Allocation.idle sources depths counts state available nonnegative
        | some review => allocateLive sources depths counts state ⟨position, within⟩ obligation present review available nonnegative
  else Allocation.idle sources depths counts state available nonnegative

def allocateFrom (origin : ActualItem sources depths counts) (position : Nat) :
    (fuel : Nat) → (state : (process sources depths counts).GeneratedState) →
    (available : ℚ) → 0 ≤ available → Allocation sources depths counts state available
  | 0, state, available, nonnegative => Allocation.idle sources depths counts state available nonnegative
  | fuel + 1, state, available, nonnegative =>
      let first := allocateAt sources depths counts origin state position available nonnegative
      let rest := allocateFrom origin (position + 1) fuel first.after first.remaining first.remaining_nonnegative
      first.append sources depths counts rest

/-- Consume one source movement once in original slot order, including
all inherited canonical and actual micro claims. The leftover quota is visible. -/
def allocate (origin : ActualItem sources depths counts)
    (movement : Finance.Movement (sources origin.1) (depths origin.1) (counts origin.1) origin.2)
    (state : (process sources depths counts).GeneratedState) : Allocation sources depths counts state movement.quantity :=
  allocateFrom sources depths counts origin 0 state.current.slots.length state movement.quantity
    (movement.quantity_nonnegative (sources origin.1) (depths origin.1) (counts origin.1))

theorem every_actual_movement_has_only_its_original_quota (origin : ActualItem sources depths counts)
    (movement : Finance.Movement (sources origin.1) (depths origin.1) (counts origin.1) origin.2)
    (state : (process sources depths counts).GeneratedState) :
    (allocate sources depths counts origin movement state).used sources depths counts +
      (allocate sources depths counts origin movement state).remaining = movement.quantity :=
  Allocation.whole_quota sources depths counts _

#print axioms allocate
#print axioms every_actual_movement_has_only_its_original_quota

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
