import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Consumer
import H0mework.Versions.R2.Arithmetic.FockResponsibility.DebtU7Admission
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Carried

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source
open SourceOperationEffects SourceOperationExecution
namespace S
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
  (R.old R.origin R.reader C.mathRuntime Coimage canonical)
end S
namespace A
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action
  (actualAction actualEffect coimageBackward coimage_backward_action actual_literal_next)
end A
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (law Raw)
end O
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (frame residual_first_receipt residual_frame_next activated_next)
end I
abbrev C (depth count : Nat) := S.Coimage depth count
abbrev Values (depth count : Nat) : Bool → Type
  | false => C depth count
  | true => C depth count × (C depth count × C depth count)
instance (depth count : Nat) (sort : Bool) : AddCommGroup (Values depth count sort) := by
  cases sort <;> dsimp only [Values] <;> infer_instance
abbrev Vars (_ : Bool) := Unit
def intoFirst (depth count : Nat) : C depth count →+ Values depth count true where
  toFun value := (value, 0, 0)
  map_zero' := rfl
  map_add' := by intro _ _; ext <;> simp
def intoSecond (depth count : Nat) : C depth count →+ Values depth count true where
  toFun value := (0, value, 0)
  map_zero' := rfl
  map_add' := by intro _ _; ext <;> simp
def intoThird (depth count : Nat) : C depth count →+ Values depth count true where
  toFun value := (0, 0, value)
  map_zero' := rfl
  map_add' := by intro _ _; ext <;> simp
def programme (depth count : Nat) : Expr (Values depth count) Vars true :=
  .add (.linear (s := false) (t := true) (intoFirst depth count)
      (.linear (s := false) (t := false) (A.actualAction depth count).toAddMonoidHom (.var Unit.unit)))
    (.add (.linear (s := false) (t := true) (intoSecond depth count)
        (.linear (s := false) (t := false) (A.actualEffect depth count).toAddMonoidHom (.var Unit.unit)))
      (.linear (s := false) (t := true) (intoThird depth count)
        (.linear (s := false) (t := false) (A.coimageBackward depth count).toAddMonoidHom
          (.linear (s := false) (t := false) (A.actualAction depth count).toAddMonoidHom (.var Unit.unit)))))
def environment (depth count : Nat) : Env (Values depth count) Vars :=
  fun sort _ => match sort with
    | false => S.canonical depth count (SourceOperationNative.point (S.C.mathRuntime depth count))
    | true => 0
def raw (depth count : Nat) : O.Raw (Value := Values depth count) (Var := Vars) (sort := true) :=
  ⟨environment depth count, programme depth count⟩
theorem programme_eval (depth count : Nat) :
    (programme depth count).eval (environment depth count) =
      let source := S.canonical depth count (SourceOperationNative.point (S.C.mathRuntime depth count))
      (A.actualAction depth count source, A.actualEffect depth count source, source) := by
  simp only [programme, Expr.eval, environment, intoFirst, intoSecond, intoThird,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Prod.mk_add_mk, zero_add, add_zero]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact A.coimage_backward_action depth count (SourceOperationNative.point (S.C.mathRuntime depth count))

abbrev sourceRoot (depth count : Nat) := (S.C.mathRuntime depth count).current.root
abbrev sourceVisit (depth count : Nat) := (S.C.mathRuntime depth count).current.visit
abbrev sourceU7 (depth : Nat) := RootGeneratedDebtActivationU7.extendU7
  (law := O.law (S.R.old depth) (S.R.origin depth) (S.R.reader depth))
  NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOccurrenceDebtU7Admission.oldU7
abbrev sourceCalculus (depth : Nat) := RootGeneratedDebtActivationU7.extendU7Calculus
  (law := O.law (S.R.old depth) (S.R.origin depth) (S.R.reader depth))
  NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOccurrenceDebtU7Admission.oldU7
  NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOccurrenceDebtU7Admission.oldU7Calculus
def reader (depth count : Nat)
    (_ : (sourceRoot depth count).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (sourceVisit depth count).current) := raw depth count
abbrev feed (depth count : Nat) := I.frame (sourceRoot depth count) (sourceVisit depth count)
  (sourceU7 depth) (sourceCalculus depth) (reader depth count)
abbrev paidTrace (depth count : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
  (sourceRoot depth count).toAuthoritativeRoot (sourceVisit depth count).current (reader depth count)
abbrev paidInventory (depth count : Nat) := SourceOperationPaidRelations.exposure (paidTrace depth count)
abbrev computed (depth count : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot depth count).toAuthoritativeRoot (sourceVisit depth count).current (reader depth count)
theorem computed_value (depth count : Nat) : computed depth count =
    let source := S.canonical depth count (SourceOperationNative.point (S.C.mathRuntime depth count))
    (A.actualAction depth count source, A.actualEffect depth count source, source) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source
    (sourceRoot depth count).toAuthoritativeRoot (sourceVisit depth count).current (reader depth count)).trans
    (programme_eval depth count)
/-- The actual executor's first generated coordinate supplies the update.
The source action is recognized afterward, rather than recomputed as input. -/
def updatedEnvironment (depth count : Nat) : Env (Values depth count) Vars :=
  fun sort _ => match sort with
    | false => (computed depth count).1
    | true => 0

theorem updated_source_is_action (depth count : Nat) :
    updatedEnvironment depth count false Unit.unit =
      A.actualAction depth count (environment depth count false Unit.unit) :=
  congrArg Prod.fst (computed_value depth count)

theorem updated_source_is_literal_next (depth count : Nat) :
    updatedEnvironment depth count false Unit.unit =
      S.canonical depth (count + 1) (SourceOperationNative.point (S.C.mathRuntime depth count).tick.next) :=
  (updated_source_is_action depth count).trans (A.actual_literal_next depth count)

/-- The inherited frame receives both the source-generated update and the
entire new source trace. Its original root, registration and packet are reused. -/
def dynamicFeed (depth count : Nat) := { feed depth count with
  environment := fun {_current} _occurrence => updatedEnvironment depth count
  inventory := some (paidInventory depth count) }
theorem feed_has_complete_new_trace (depth count : Nat) :
    (dynamicFeed depth count).inventory = some (SourceOperationPaidRelations.exposure (paidTrace depth count)) := rfl
theorem feed_has_actual_update (depth count : Nat) :
    (dynamicFeed depth count).activeEnvironment = updatedEnvironment depth count := rfl
abbrev configuration (depth count : Nat) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
    (PhysicalValue := Values depth count) (PhysicalVar := Vars) (sort := true)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
