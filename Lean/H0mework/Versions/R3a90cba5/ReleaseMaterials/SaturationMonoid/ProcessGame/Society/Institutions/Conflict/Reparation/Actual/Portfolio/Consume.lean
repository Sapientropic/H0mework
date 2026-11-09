import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Spine
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Transport (sourceSupport)
open Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {N J : WorldRelationNetwork}

namespace Stack

structure Applied (prior : Stack seed community N J) (changes : Changes prior.balances) where
  next : Stack seed community N J
  motion : Move prior next
  exactRows : next.balances = changes.result

/-- Use the allocator's change at each existing address as the motion of
that very ledger layer. This adds no claim and creates no further receipt. -/
def applyChanges : {J : WorldRelationNetwork} → (prior : Stack seed community N J) →
    (changes : Changes prior.balances) → Applied prior changes
  | _, .base _, changes => ⟨.base _, .base, by cases changes; rfl⟩
  | _, .add prior origin balance view, changes =>
    let parts := Changes.unsnoc prior.balances (origin, balance) changes
    let old := applyChanges prior parts.1
    ⟨.add old.next origin parts.2.after view, .add old.motion origin view parts.2.motion,
      (congrArg (fun rows => rows ++ [(origin, parts.2.after)]) old.exactRows).trans
        (Changes.result_unsnoc prior.balances (origin, balance) changes).symm⟩

end Stack

namespace StateAt

variable (state : StateAt seed community cut) (changes : Changes state.stack.balances)

def moveFirst {target : Stack seed community cut.native.frame.N state.world}
    (move : Stack.Move state.stack target) (writes : Bool) : First state.world :=
  let support := sourceSupport cut.native
  let finite := cut.native.frame.entries_finite cut.native.visit.current
  { before := state.stack.support support
    after := target.support support
    whole := move.lift (identityWhole support) (cut.native.frame.entry cut.native.visit.current)
    beforeFinite := state.stack.finite _ finite
    afterFinite := target.finite _ finite
    openFibres := state.stack.fibres cut.native.frame.family.open_fibres
    writes := writes }

def receiptFirst : First state.world :=
  let applied := state.stack.applyChanges changes
  moveFirst state applied.motion (decide (0 < changes.assignedWhere (fun _ => True)))

def receiptDraft := (receiptFirst state changes).prepare state.resident state.exactSupport.symm

def receiptPrepared : Prepared seed community cut.native.frame.N (sourceSupport cut.native) :=
  ⟨state.world, (state.stack.applyChanges changes).next, receiptDraft state changes,
    (receiptFirst state changes).first_support⟩

def consumeMotion {target : Stack seed community cut.native.frame.N state.world}
    (move : Stack.Move state.stack target) (writes : Bool) : StateAt seed community cut :=
  let first := moveFirst state move writes
  let draft := first.prepare state.resident state.exactSupport.symm
  fromPrepared ⟨state.world, target, draft, first.first_support⟩ rfl rfl

theorem consumeMotion_balances {target : Stack seed community cut.native.frame.N state.world}
    (move : Stack.Move state.stack target) (writes : Bool) :
    (state.consumeMotion move writes).stack.balances = target.balances := by
  unfold consumeMotion
  rw [fromPrepared_balances]

theorem the_motion_is_the_original_visit_write {target : Stack seed community cut.native.frame.N state.world}
    (move : Stack.Move state.stack target) (writes : Bool) :
    (⟨state.world, ((state.moveFirst move writes).sequential state.resident
      state.exactSupport.symm).target.targetAnswerAndNext.nextCurrent⟩ :
        RootInquiryCompletion.AnyAuthoritativeRootCurrent) =
      (state.consumeMotion move writes).resident.erase :=
  (state.moveFirst move writes).sequential_reaches_its_first_write state.resident state.exactSupport.symm

def consume : StateAt seed community cut :=
  fromPrepared (receiptPrepared state changes) rfl rfl

theorem consume_balances : (consume state changes).stack.balances = changes.result := by
  unfold consume
  rw [fromPrepared_balances]
  exact (state.stack.applyChanges changes).exactRows

theorem the_allocation_is_the_original_visit_write :
    (⟨state.world, ((receiptFirst state changes).sequential state.resident
      state.exactSupport.symm).target.targetAnswerAndNext.nextCurrent⟩ :
      RootInquiryCompletion.AnyAuthoritativeRootCurrent) = (consume state changes).resident.erase :=
  (receiptFirst state changes).sequential_reaches_its_first_write state.resident state.exactSupport.symm

end StateAt

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
