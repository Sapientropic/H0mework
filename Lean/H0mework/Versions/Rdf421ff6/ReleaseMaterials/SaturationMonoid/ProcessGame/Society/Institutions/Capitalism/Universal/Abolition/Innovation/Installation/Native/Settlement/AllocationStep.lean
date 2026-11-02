import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Instruction

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

private def originalAllocationIdentifier (suffix : String) : Lean.Elab.Tactic.TacticM (Lean.TSyntax `ident) := do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.startsWith "_private.H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation." &&
        name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure (Lean.mkIdent name)
  | _ => throwError "The unique original allocation equation was not found"

noncomputable section

variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

/-- This is the existing private allocator, exposed without changing its body. -/
def nativeAt (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    Epoch.Finance.Allocation source depth count state available := by
  run_tac do
    let original ← originalAllocationIdentifier ".allocateAt"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $original:ident $(Lean.mkIdent `source):ident $(Lean.mkIdent `depth):ident
        $(Lean.mkIdent `count):ident $(Lean.mkIdent `origin):ident $(Lean.mkIdent `state):ident
        $(Lean.mkIdent `position):ident $(Lean.mkIdent `available):ident $(Lean.mkIdent `nonnegative):ident))

/-- The same boundary used inside the original live-slot allocation. -/
def nativeReviewBoundary
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Epoch.Finance.Review source depth count obligation.content)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Epoch.Finance.Boundary source depth count obligation :=
  Epoch.Finance.reviewBoundary source depth count obligation
    (Epoch.Finance.live_sound source depth count state index obligation present).1 receipt
    (min available receipt.quantity)
    (Epoch.Finance.live_sound source depth count state index obligation present).2
    (le_min nonnegative (receipt.quantity_nonnegative source depth count)) (min_le_right _ _)

theorem nativeAt_live
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Epoch.Finance.Review source depth count obligation.content)
    (read : Epoch.Finance.readReview source depth count obligation.content origin = some receipt)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (nativeAt source depth count origin state index available nonnegative).after.current.slots =
      state.current.slots.set index
        (Epoch.Finance.boundaryDisposition source depth count
          (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative)).targetSlot ∧
    (nativeAt source depth count origin state index available nonnegative).remaining =
      available - min (min available receipt.quantity)
        (obligation.residual (receipt.fromHolder source depth count)) := by
  rcases index with ⟨position,inRange⟩
  run_tac do
    let original ← originalAllocationIdentifier ".allocateAt"
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [nativeAt,$original:ident]))
  rw [dif_pos inRange]
  split
  · rename_i archive observed
    cases observed.symm.trans present
  · rename_i actual observed
    have same := ObligationSlot.live.inj (observed.symm.trans present)
    subst actual
    rw [read]
    run_tac do
      let original ← originalAllocationIdentifier ".allocateLive"
      Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [$original:ident]))
    exact ⟨rfl,rfl⟩

theorem nativeAt_none
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .live obligation)
    (read : Epoch.Finance.readReview source depth count obligation.content origin = none)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (nativeAt source depth count origin state index available nonnegative).after = state ∧
      (nativeAt source depth count origin state index available nonnegative).remaining = available := by
  rcases index with ⟨position,inRange⟩
  run_tac do
    let original ← originalAllocationIdentifier ".allocateAt"
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [nativeAt,$original:ident]))
  rw [dif_pos inRange]
  split
  · rename_i archive observed
    cases observed.symm.trans present
  · rename_i actual observed
    have same := ObligationSlot.live.inj (observed.symm.trans present)
    subst actual
    rw [read]
    exact ⟨rfl,rfl⟩

theorem nativeAt_terminal
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (archive : TerminalArchive (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .terminal archive)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (nativeAt source depth count origin state index available nonnegative).after = state ∧
      (nativeAt source depth count origin state index available nonnegative).remaining = available := by
  rcases index with ⟨position,inRange⟩
  run_tac do
    let original ← originalAllocationIdentifier ".allocateAt"
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [nativeAt,$original:ident]))
  rw [dif_pos inRange]
  split
  · exact ⟨rfl,rfl⟩
  · rename_i actual observed
    cases observed.symm.trans present

theorem the_original_three_slot_allocation_is_three_original_steps
    (origin : Epoch.Finance.ActualItem source depth count)
    (movement : Epoch.Finance.Movement source depth count origin)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (three : state.current.slots.length = 3) :
    let first := nativeAt source depth count origin state 0 movement.quantity (movement.quantity_nonnegative source depth count)
    let second := nativeAt source depth count origin first.after 1 first.remaining first.remaining_nonnegative
    let third := nativeAt source depth count origin second.after 2 second.remaining second.remaining_nonnegative
    (Epoch.Finance.allocate source depth count origin movement state).after = third.after ∧
      (Epoch.Finance.allocate source depth count origin movement state).remaining = third.remaining := by
  dsimp only
  unfold Epoch.Finance.allocate
  rw [three]
  run_tac do
    let recursive ← originalAllocationIdentifier ".allocateFrom"
    let append ← originalAllocationIdentifier ".Allocation.append"
    let idle ← originalAllocationIdentifier ".Allocation.idle"
    Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$recursive:ident,$append:ident,$idle:ident,nativeAt]))
  trivial

variable (state : (Epoch.Finance.process source depth count).GeneratedState)
  (index : Fin state.current.slots.length)
  (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
  (present : state.current.slots.get index = .live obligation)
  (receipt : Epoch.Finance.Review source depth count obligation.content)
  (available : ℚ) (nonnegative : 0 ≤ available)

theorem nativeReviewBoundary_event :
    (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative).event =
      .review obligation.content receipt obligation.residual (min available receipt.quantity) := rfl

theorem nativeReviewBoundary_balance :
    Epoch.Finance.slotBalance source depth count
      (Epoch.Finance.boundaryDisposition source depth count
        (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative)).targetSlot =
      receipt.after source depth count obligation.residual (min available receipt.quantity) :=
  Epoch.Finance.boundary_balance source depth count _

theorem nativeReviewBoundary_claim :
    Epoch.Finance.slotClaim source depth count
      (Epoch.Finance.boundaryDisposition source depth count
        (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative)).targetSlot =
      obligation.content := Epoch.Finance.boundary_claim source depth count _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
