import H0mework.Physics.SpinRuntime.Native
import H0mework.Physics.SpinPair.GaugeEquation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Dynamics

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineFormNativeP286GaugePointwiseEquation
open StageNineP286SourceNativeReducedEntropyDescent
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeCenteredReducedEntropyIteration
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open Stage9C Stage9C.Reduction

noncomputable section

theorem accepted_reducedBase :
    p286ReducedEntropyBase positiveSmoothUnifiedSource Material.SpinPair.actual =
      Material.SpinPair.actual :=
  Revision.SpinPair.initialState.reducedBase_eq

theorem accepted_p286Next (center : BasePoint) :
    p286CenteredReducedNext positiveSmoothUnifiedSource Material.SpinPair.actual
      Material.SpinPair.actual_smooth Material.SpinPair.actual_nondegenerate center =
      Material.SpinPair.actual := by
  have equations :
      FormNativeP286GaugeConnectionPointwiseEquation positiveSmoothUnifiedSource
        Material.SpinPair.actual :=
    (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_pointwiseEquation _ _).1
      (funext Material.SpinPair.actual_gaugeEuler_zero)
  have step :=
    (p286CenteredReducedNext_all_eq_base_iff_masterEquations
      positiveSmoothUnifiedSource Material.SpinPair.actual Material.SpinPair.actual_smooth
      Material.SpinPair.actual_nondegenerate).2
        ⟨p286ReducedEntropyBase_auxiliaryEquation _ _ Material.SpinPair.actual_nondegenerate,
          by simpa only [accepted_reducedBase] using equations⟩ center
  simpa only [accepted_reducedBase] using step

theorem accepted_cartanNext (center : BasePoint) :
    p286CartanNext positiveSmoothUnifiedSource Material.SpinPair.actual
      Material.SpinPair.actual_smooth Material.SpinPair.actual_nondegenerate center =
      Material.SpinPair.actual := by
  unfold p286CartanNext
  rw [accepted_p286Next]
  exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_idempotent _ _

private theorem state_eq_of_current_eq
    {source : SmoothUnifiedSource}
    {left right : P286CenteredReducedEntropyStateAt source}
    (same : left.current = right.current) : left = right := by
  cases left
  cases right
  cases same
  rfl

theorem accepted_materialStateNext :
    Revision.materialStateNext Revision.SpinPair.initialState =
      Revision.SpinPair.initialState := by
  apply state_eq_of_current_eq
  exact accepted_cartanNext 0

end
end SaturationMonoid.PhysicsCore.Stage9CU.Dynamics
