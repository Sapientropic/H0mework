import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Consumer

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action

noncomputable section

namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (entry debtCurrent debtStep)
end P

/-- The initial bind is already paid before the actor's source pulse. -/
def activeIndex (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    Fin (SourceOperationExecution.remaining
      (RootGeneratedDebtActivationJointSource.OwnerFree.raw (R.old depth) (R.origin depth) (R.reader depth)).expression) :=
  ⟨count + 1, by
    change count + 1 < SourceOperationExecution.remaining
      (sourceProgramme (R.index depth) (R.active depth) (emitted depth))
    rw [sourceProgramme_budget]
    change count < sourceFuel (sourceAt (R.index depth) (R.active depth) (emitted depth)) at within
    omega⟩

def continuation (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :=
  Registered.activeContinuation depth (activeIndex depth count within)

private theorem debt_state (depth count : Nat) :
    (P.debtCurrent (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).state =
      (C.mathRuntime depth (count + 1)).state := by
  apply ULift.ext
  exact (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime_depth
    (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).symm

theorem continuation_literal_next (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    (continuation depth count within).target.state =
      (C.mathRuntime depth (count + 1)).tick.next.state := by
  change (process depth).successor
    (P.debtCurrent (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).state =
      (process depth).successor (C.mathRuntime depth (count + 1)).state
  exact congrArg (process depth).successor (debt_state depth count)

/-- The inverse/action pair and the paying continuation use the original whole
ledger's literal destination row, including the old complete remainder. -/
theorem continuation_whole_row (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    (continuation depth count within).target.entry =
      ((RootGeneratedDebtActivationJointSource.OwnerFree.whole
        (R.old depth) (R.origin depth) (R.reader depth)
        (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit
          (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).current).destination
        (P.entry (R.old depth) (R.origin depth) (R.reader depth) (count + 1))).1 := by
  have paidRow : (continuation depth count within).target.entry =
      (P.debtStep (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).targetEntry :=
    (P.debtStep (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).sameDebtTarget_unique _
      (continuation depth count within).payment.step.sameDebt
  exact paidRow.trans (congrArg
    (fun write => (write.destination (P.entry (R.old depth) (R.origin depth) (R.reader depth) (count + 1))).1)
    (RootGeneratedDebtActivationJointSource.OwnerFree.patch_fold
      (R.old depth) (R.origin depth) (R.reader depth)
      (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit
        (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).current))

theorem continuation_strict (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    (continuation depth count within).target.budget <
      (P.debtCurrent (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).budget :=
  (continuation depth count within).strictDebit

/-- Actual source action, complete coimage inverse, whole-ledger destination,
paid inventory and literal next are consumed together at the same pulse. -/
theorem paid_action_inverse (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    let runtime := C.mathRuntime depth (count + 1)
    let paying := continuation depth count within
    actualAction depth (count + 1) (canonical depth (count + 1) (SourceOperationNative.point runtime)) =
      canonical depth ((count + 1) + 1) (SourceOperationNative.point runtime.tick.next) ∧
    coimageBackward depth (count + 1)
        (actualAction depth (count + 1) (canonical depth (count + 1) (SourceOperationNative.point runtime))) =
      canonical depth (count + 1) (SourceOperationNative.point runtime) ∧
    recover depth (count + 1)
        (coimageBackward depth (count + 1)
          (canonical depth ((count + 1) + 1) (SourceOperationNative.point runtime.tick.next))) =
      SourceOperationNative.point runtime ∧
    paying.target.state = runtime.tick.next.state ∧
    type_of% (continuation_whole_row depth count within) ∧
    paying.target.budget <
      (P.debtCurrent (R.old depth) (R.origin depth) (R.reader depth) (count + 1)).budget ∧
    type_of% (SourceOperationNative.point_factorizes runtime) ∧
    type_of% ((OF.facade (R.old depth) (R.origin depth) (R.reader depth)).readoutAt_factorizes
      runtime (OF.mathFace (R.old depth) (R.origin depth) (R.reader depth) runtime).projection) ∧
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Relations.coversAt_factorizes
      (R.old depth) (R.origin depth) (R.reader depth) runtime) ∧
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Relations.tick_paid_exposure
      (R.old depth) (R.origin depth) (R.reader depth) runtime) ∧
    type_of% (SourceOperationNative.Context.literalnext_pair (readEnv depth) (physicalExpr depth) runtime) ∧
    cursorRestriction depth (recover depth (count + 1)
      (coimageBackward depth (count + 1)
        (canonical depth ((count + 1) + 1) (SourceOperationNative.point runtime.tick.next)))) =
      S.readMaterial depth runtime.state := by
  dsimp only
  exact ⟨actual_literal_next depth (count + 1),
    coimage_backward_action depth (count + 1) _, previous_full_source depth (count + 1),
    continuation_literal_next depth count within, continuation_whole_row depth count within,
    continuation_strict depth count within,
    SourceOperationNative.point_factorizes (C.mathRuntime depth (count + 1)),
    (OF.facade (R.old depth) (R.origin depth) (R.reader depth)).readoutAt_factorizes
      (C.mathRuntime depth (count + 1))
      (OF.mathFace (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth (count + 1))).projection,
    RootGeneratedDebtActivationJointSource.OwnerFree.Relations.coversAt_factorizes
      (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth (count + 1)),
    RootGeneratedDebtActivationJointSource.OwnerFree.Relations.tick_paid_exposure
      (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth (count + 1)),
    SourceOperationNative.Context.literalnext_pair (readEnv depth) (physicalExpr depth)
      (C.mathRuntime depth (count + 1)),
    previous_cursor depth (count + 1)⟩


/-- The complete coimage action recovers the literal original actor action
before its final cursor restriction. -/
theorem acted_actor_cursor (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    cursorRestriction depth (recover depth (count + 1)
      (actualAction depth (count + 1) (canonical depth (count + 1)
        (SourceOperationNative.point (C.mathRuntime depth (count + 1)))))) =
      Cursor.Source.someLift depth (action (R.index depth) (R.active depth) (Finsupp.single
        (runPoint (R.index depth) (R.active depth) count
          (initialPoint (R.index depth) (R.active depth) (emitted depth))) 1)) :=
  (acted_cursor depth (count + 1)).trans (Cursor.Source.material_literal_next depth count within)

theorem paid_actor_action_inverse (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    type_of% (paid_action_inverse depth count within) ∧
      type_of% (acted_actor_cursor depth count within) :=
  ⟨paid_action_inverse depth count within, acted_actor_cursor depth count within⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
