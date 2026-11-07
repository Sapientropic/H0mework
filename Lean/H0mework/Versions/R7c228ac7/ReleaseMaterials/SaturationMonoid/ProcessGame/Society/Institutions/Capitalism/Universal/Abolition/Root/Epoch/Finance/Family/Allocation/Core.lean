import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Payment.Boundary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

structure Allocation (before : (process sources depths counts).GeneratedState) (available : ℚ) where
  private mk ::
  after : (process sources depths counts).GeneratedState
  transition : (process sources depths counts).Run before.current after.current
  remaining : ℚ
  remaining_nonnegative : 0 ≤ remaining
  remaining_le : remaining ≤ available
  original_claims : after.current.slots.map (slotClaim sources depths counts) =
    before.current.slots.map (slotClaim sources depths counts)

namespace Allocation

def idle (state : (process sources depths counts).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation sources depths counts state available := ⟨state, .nil, available, nonnegative, le_refl _, rfl⟩

def used {state : (process sources depths counts).GeneratedState} {available : ℚ}
    (result : Allocation sources depths counts state available) : ℚ := available - result.remaining

theorem whole_quota {state : (process sources depths counts).GeneratedState} {available : ℚ}
    (result : Allocation sources depths counts state available) : result.used sources depths counts + result.remaining = available :=
  sub_add_cancel _ _

def append {state : (process sources depths counts).GeneratedState} {available : ℚ}
    (first : Allocation sources depths counts state available)
    (second : Allocation sources depths counts first.after first.remaining) : Allocation sources depths counts state available where
  after := second.after
  transition := first.transition.concatRuns (process sources depths counts) second.transition
  remaining := second.remaining
  remaining_nonnegative := second.remaining_nonnegative
  remaining_le := second.remaining_le.trans first.remaining_le
  original_claims := second.original_claims.trans first.original_claims

end Allocation

def allocateLive (state : (process sources depths counts).GeneratedState)
    (position : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources depths counts))
    (present : state.current.slots.get position = .live obligation)
    (receipt : Review sources depths counts obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation sources depths counts state available := by
  let cap := min available receipt.movement.quantity
  have cap_nonnegative : 0 ≤ cap := le_min nonnegative (receipt.quantity_nonnegative sources depths counts)
  let used := min cap (obligation.residual receipt.movement.sender)
  have sound := live_sound sources depths counts state position obligation present
  have used_nonnegative : 0 ≤ used := le_min cap_nonnegative (sound.2 _)
  have used_le : used ≤ available := (min_le_left _ _).trans (min_le_left _ _)
  let boundary := reviewBoundary sources depths counts obligation sound.1 receipt cap sound.2 cap_nonnegative (min_le_right _ _)
  let edge : (process sources depths counts).Edge state.current := .cross position obligation present boundary
  refine ⟨state.step (process sources depths counts) edge, .step .nil edge, available - used,
    sub_nonneg.mpr used_le, sub_le_self available used_nonnegative, ?_⟩
  exact cross_retains_all_claims sources depths counts state position obligation present boundary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
