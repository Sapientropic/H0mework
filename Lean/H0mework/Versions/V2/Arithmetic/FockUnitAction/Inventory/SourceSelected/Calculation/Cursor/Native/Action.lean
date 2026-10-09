import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Source
import H0mework.Versions.V2.Foundation.Responsibility.JointSource.OwnerFree.Native.Inverse

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source

noncomputable section

abbrev fullBackward (depth : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Native.backward
    (R.old depth) (R.origin depth) (R.reader depth)

/-- The generated coimage acts only by recovering its full source, applying the
original native successor, then using the generated canonical map. -/
def actualAction (depth count : Nat) : Coimage depth count →ₗ[ℤ] Coimage depth count :=
  (canonical depth count).comp
    ((SourceOperationNative.sourceAction (process depth)).comp (recover depth count))

def coimageBackward (depth count : Nat) : Coimage depth count →ₗ[ℤ] Coimage depth count :=
  (canonical depth count).comp ((fullBackward depth).comp (recover depth count))

def actualEffect (depth count : Nat) : Coimage depth count →ₗ[ℤ] Coimage depth count :=
  actualAction depth count - LinearMap.id

theorem actualAction_source (depth count : Nat) (word : FullCarrier depth) :
    actualAction depth count (canonical depth count word) =
      canonical depth count (SourceOperationNative.sourceAction (process depth) word) := by
  change canonical depth count
    (SourceOperationNative.sourceAction (process depth)
      (recover depth count (canonical depth count word))) = _
  rw [complete_inverse]

theorem coimageBackward_source (depth count : Nat) (word : FullCarrier depth) :
    coimageBackward depth count (canonical depth count word) =
      canonical depth count (fullBackward depth word) := by
  change canonical depth count (fullBackward depth
    (recover depth count (canonical depth count word))) = _
  rw [complete_inverse]

/-- Full inverse recovery holds on the complete actual source-action image. -/
theorem coimage_backward_action (depth count : Nat) (word : FullCarrier depth) :
    coimageBackward depth count (actualAction depth count (canonical depth count word)) =
      canonical depth count word := by
  rw [actualAction_source, coimageBackward_source]
  exact congrArg (canonical depth count)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Native.backward_source
      (R.old depth) (R.origin depth) (R.reader depth) word)

theorem actual_literal_next (depth count : Nat) :
    actualAction depth count (canonical depth count
      (SourceOperationNative.point (C.mathRuntime depth count))) =
      canonical depth (count + 1)
        (SourceOperationNative.point (C.mathRuntime depth count).tick.next) := by
  rw [actualAction_source, SourceOperationNative.sourceAction_point]
  rfl

theorem actual_effect_point (depth count : Nat) :
    actualEffect depth count (canonical depth count
      (SourceOperationNative.point (C.mathRuntime depth count))) =
      canonical depth count
        (SourceOperationNative.point (C.mathRuntime depth count).tick.next -
          SourceOperationNative.point (C.mathRuntime depth count)) := by
  change actualAction depth count (canonical depth count
    (SourceOperationNative.point (C.mathRuntime depth count))) -
      canonical depth count (SourceOperationNative.point (C.mathRuntime depth count)) = _
  rw [actual_literal_next, map_sub]
  rfl

/-- The inverse returns the full native word before any cursor restriction. -/
theorem previous_full_source (depth count : Nat) :
    recover depth count
      (coimageBackward depth count (canonical depth (count + 1)
        (SourceOperationNative.point (C.mathRuntime depth count).tick.next))) =
      SourceOperationNative.point (C.mathRuntime depth count) := by
  rw [← actual_literal_next, coimage_backward_action, complete_inverse]

theorem previous_runtime_unique (depth count : Nat)
    (prior : OF.Runtime (R.old depth) (R.origin depth) (R.reader depth))
    (same : SourceOperationNative.point prior = recover depth count
      (coimageBackward depth count (canonical depth (count + 1)
        (SourceOperationNative.point (C.mathRuntime depth count).tick.next)))) :
    prior = C.mathRuntime depth count :=
  SourceOperationNative.point_injective (process depth) (same.trans (previous_full_source depth count))

theorem previous_cursor (depth count : Nat) :
    cursorRestriction depth (recover depth count
      (coimageBackward depth count (canonical depth (count + 1)
        (SourceOperationNative.point (C.mathRuntime depth count).tick.next)))) =
      S.readMaterial depth (C.mathRuntime depth count).state := by
  rw [previous_full_source]
  exact cursor_restriction depth count

theorem acted_cursor (depth count : Nat) :
    cursorRestriction depth (recover depth count
      (actualAction depth count (canonical depth count
        (SourceOperationNative.point (C.mathRuntime depth count))))) =
      S.readMaterial depth (C.mathRuntime depth count).tick.next.state := by
  rw [actualAction_source, complete_inverse, SourceOperationNative.sourceAction_point]
  exact SourceOperationNative.observer_point _ _

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
