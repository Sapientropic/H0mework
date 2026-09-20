import H0mework.Physics.CartanAction.CartanReactionCurrentRestartGlobalRegularity
import H0mework.Physics.CartanAction.CartanP286CriticalPair
import H0mework.Physics.GaugeAction.P286JointYangMillsGradientFlowRegularity

/-! Whole-field algebraic/Cartan reduction of the original nine-channel
action. The two existing source-native writes commute and form one
idempotent reduction. Its five remaining equations use the unchanged joint
residual on the generated actual; the acceptance boundary is not weakened. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Reduction

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGravityBianchi
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCartanP286CriticalPair
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryVariation

noncomputable section

/-- The two whole-field writes commute on the actual configuration. -/
theorem cartan_constitutive_commute
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration) :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
        (formNativeP286GaugeConstitutiveReadout source current) =
      formNativeP286GaugeConstitutiveReadout source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current) := by
  apply StageNineHolonomicConfiguration.ext <;> rfl

/-- Eliminate the action's two auxiliaries, multiplier, and Cartan connection
on one whole field. All derivatives remain derivatives of that actual field. -/
def algebraicCartanReduction
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
    (formNativeP286GaugeConstitutiveReadout source current)

theorem algebraicCartanReduction_idempotent
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration) :
    algebraicCartanReduction source (algebraicCartanReduction source current) =
      algebraicCartanReduction source current := by
  unfold algebraicCartanReduction
  rw [← cartan_constitutive_commute,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_idempotent]
  rfl

theorem algebraicCartanReduction_smooth
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) (nondegenerate : current.Nondegenerate) :
    (algebraicCartanReduction source current).Smooth :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth source _
    (formNativeP286GaugeConstitutiveReadout_smooth source current smooth nondegenerate)
    nondegenerate

theorem algebraicCartanReduction_nondegenerate
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (algebraicCartanReduction source current).Nondegenerate :=
  nondegenerate

theorem algebraicCartanReduction_lorentzAdmissible
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    GravityConnectionLorentzAdmissible (algebraicCartanReduction source current) :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzAdmissible
    source _ nondegenerate

theorem algebraicCartanReduction_gravityMultiplier_zero
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (algebraicCartanReduction source current) point).gravityMultiplier = 0 := by
  change formNativeGravityMultiplierEulerResidual _ = 0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  rfl

theorem algebraicCartanReduction_gravityAuxiliary_zero
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (algebraicCartanReduction source current) point).gravityAuxiliary = 0 :=
  congrFun
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
      source (formNativeP286GaugeConstitutiveReadout source current)) point

theorem algebraicCartanReduction_p286Auxiliary_zero
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (algebraicCartanReduction source current) point).p286GaugeAuxiliary = 0 := by
  change (diracDualFormNativePointwiseJointResidual source
    (formNativeP286GaugeConstitutiveReadout source current) point).p286GaugeAuxiliary = 0
  apply (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).2
  exact formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation
    source current nondegenerate point

theorem algebraicCartanReduction_lorentz_zero
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) (nondegenerate : current.Nondegenerate)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (algebraicCartanReduction source current) point).lorentzConnection = 0 :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at
    source (formNativeP286GaugeConstitutiveReadout source current)
    (formNativeP286GaugeConstitutiveReadout_smooth source current smooth nondegenerate)
    point (nondegenerate point)

/-- The complete residual of the generated actual has five differential
channels. The four eliminated equations have been paid by the same write. -/
theorem algebraicCartanReduction_jointZero_iff
    (source : SmoothUnifiedSource) (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) (nondegenerate : current.Nondegenerate) :
    DiracDualFormNativeJointZeroFiber source (algebraicCartanReduction source current) ↔
      ∀ point,
        let residual := diracDualFormNativePointwiseJointResidual source
          (algebraicCartanReduction source current) point
        residual.p286GaugeConnection = 0 ∧ residual.scalar = 0 ∧
          residual.matter = 0 ∧ residual.conjugateMatter = 0 ∧ residual.coframe = 0 := by
  rw [diracDualFormNativeJointZeroFiber_iff_pointwise]
  constructor
  · intro zero point
    exact ⟨congrArg (·.p286GaugeConnection) (zero point),
      congrArg (·.scalar) (zero point), congrArg (·.matter) (zero point),
      congrArg (·.conjugateMatter) (zero point), congrArg (·.coframe) (zero point)⟩
  · intro equations point
    exact DiracDualFormNativePointwiseJointResidualCarrier.ext _ _
      (algebraicCartanReduction_gravityMultiplier_zero source current point)
      (algebraicCartanReduction_gravityAuxiliary_zero source current point)
      (algebraicCartanReduction_p286Auxiliary_zero source current nondegenerate point)
      (algebraicCartanReduction_lorentz_zero source current smooth nondegenerate point)
      (equations point).1 (equations point).2.1 (equations point).2.2.1
      (equations point).2.2.2.1 (equations point).2.2.2.2

end
end SaturationMonoid.PhysicsCore.Stage9C.Reduction
