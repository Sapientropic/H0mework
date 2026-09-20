import H0mework.Physics.QuantumFoundation.FoundationNativeAction
import H0mework.Physics.DualVariation.HolonomicSpinCovariance
import H0mework.Physics.Geometry.LocalFrameInvariance

/-! The current action retains physical local-Spin invariance and the full
moving-frame Spin/SU7 presentation law. Only the frame reduction is reused
from the older module; every density here is Dirac-dual and form-native. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Foundation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineGlobalBundle StageNineHolonomicField
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeLocalSpinAction
open StageNineDiracDualFormNativeHolonomicSpinCovariance StageNineDiracKineticLocalSpinDifferential
open StageNineLocalFrameInvariance Stage9C.Material.SpinPair

noncomputable section

theorem actualLocalSpin_invariant (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13) (spinSmooth : LocalSpinFieldSmooth spinField) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction positiveSmoothUnifiedSource chart
        (localSpinDiracDualFormNativeAction spinField actual) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction positiveSmoothUnifiedSource chart actual :=
  holonomicDiracDualFormNativeIntegratedUnifiedAction_localSpin_invariant
    positiveSmoothUnifiedSource chart spinField actual spinSmooth actual_smooth
    actual_lorentzAdmissible actual_nondegenerate

def nativeActionInFrame (chart : StageNineChart) (frame : LocalTotalFrameSection)
    (field : StageNineContinuumFieldSection) : ℝ :=
  ∫ point : BasePoint,
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource chart point
      (reduceContinuumPointField (frame point) (field point))

theorem nativeActionInFrame_change (chart : StageNineChart)
    (change frame : LocalTotalFrameSection) (field : StageNineContinuumFieldSection) :
    nativeActionInFrame chart (multiplyLocalFrameSections change frame)
        (transformContinuumFieldSection change field) = nativeActionInFrame chart frame field := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  change sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource chart point
    (reduceContinuumPointField (change point * frame point)
      (transformContinuumPointField (change point) (field point))) = _
  rw [reduce_transform_mul]

theorem nativeActionInFrame_actual (chart : StageNineChart) :
    nativeActionInFrame chart identityLocalTotalFrameSection (actualChartField chart) =
      actualAction chart := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  simp only [identityLocalTotalFrameSection, reduceContinuumPointField_one]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9G.Foundation
