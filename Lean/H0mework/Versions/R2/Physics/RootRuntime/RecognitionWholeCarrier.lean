import H0mework.Versions.R2.Physics.RootRuntime.RecognitionNativeOccurrence
import H0mework.Physics.Actual.FieldsFaithful

/-! The provenance fold uses the original constructor and complete nine-field
carrier. Qualification proofs add no data. No separate premise inventory can
omit a field or supply a new center, branch, normalizer or successor. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Recognition

open Stage9C.Revision StageNineHolonomicField StageNineEnrichedProofFreeSource
open Stage9CU.Fields

noncomputable section

theorem materialState_eq_of_current_eq {left right : MaterialState}
    (same : left.current = right.current) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- Retain the source constructor as well as every physical coordinate. -/
def isRunning : SpinPair.Current → Bool
  | .ingress => false
  | .running _ => true

def wholeField (current : SpinPair.Current) : StageNineHolonomicConfiguration :=
  materialConfiguration (SpinPair.support current)

theorem reverseFaithful {left right : SpinPair.Current}
    (constructor : isRunning left = isRunning right)
    (coordinates : ∀ coordinate point,
      realCoordinate (wholeField left) coordinate point =
        realCoordinate (wholeField right) coordinate point) : left = right := by
  cases left with
  | ingress =>
      cases right with
      | ingress => rfl
      | running state => cases constructor
  | running left =>
      cases right with
      | ingress => cases constructor
      | running right =>
          exact congrArg SpinPair.Current.running
            (materialState_eq_of_current_eq (configuration_eq_of_realCoordinate_eq coordinates))

theorem native_initial_fold :
    SpinPair.next .ingress = .running SpinPair.initialState := rfl

/-- All inputs to the current physical writer: fixed source, full current and
the source-fixed origin. The residual, safe step and Cartan write are computed. -/
theorem native_running_fold (state : MaterialState) :
    wholeField (SpinPair.next (.running state)) =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource state.current
        state.smooth state.nondegenerate 0 := rfl

/-- Constructor elimination covers the actual writer and *all* installed
outputs together, including dependent compilation and consumer tokens. -/
theorem completeInput_determines_entireStep {left right : SpinPair.Current}
    (constructor : isRunning left = isRunning right)
    (coordinates : ∀ coordinate point,
      realCoordinate (wholeField left) coordinate point =
        realCoordinate (wholeField right) coordinate point) :
    left = right ∧
    SpinPair.next left = SpinPair.next right ∧
    HEq (SpinPair.generatedEvolution (SpinPair.emitted left))
      (SpinPair.generatedEvolution (SpinPair.emitted right)) ∧
    ∀ projection : SpinPair.Projection,
      HEq (SpinPair.authoritativeRoot.projectionOutcomeAt projection left)
        (SpinPair.authoritativeRoot.projectionOutcomeAt projection right) := by
  cases reverseFaithful constructor coordinates
  exact ⟨rfl, rfl, HEq.rfl, fun _ => HEq.rfl⟩

/-- A changed full physical carrier cannot be hidden by the registered read.
This is a separation theorem, not admission of a hypothetical configuration. -/
theorem distinctCurrent_detected {left right : SpinPair.Current} (distinct : left ≠ right) :
    ¬ (isRunning left = isRunning right ∧
      ∀ coordinate point, realCoordinate (wholeField left) coordinate point =
        realCoordinate (wholeField right) coordinate point) :=
  fun same => distinct (reverseFaithful same.1 same.2)

end
end SaturationMonoid.PhysicsCore.Stage10.Recognition
