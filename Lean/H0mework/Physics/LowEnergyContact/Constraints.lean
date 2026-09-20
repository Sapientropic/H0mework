import H0mework.Physics.LowEnergyContact.Profile
import H0mework.Physics.CartanReduction.AlgebraicCartan

/-! The original four algebraic/Cartan equations on the actual radial
family, without replacing the remaining five differential equations. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Contact.Constraints
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
open Stage9C.Reduction StageNineDiracDualFormNativeJointResidualCarrier
open Response.Radial
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicGravityCurvatureVarianceNormalization
open scoped ContDiff
noncomputable section

private theorem curvature_congr (first second : StageNineHolonomicConfiguration)
    (connection : first.gravityConnection = second.gravityConnection) (point : BasePoint) :
    holonomicGravityCurvature first point = holonomicGravityCurvature second point := by
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connection]

private theorem reduction_scalar (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (scalar : BasePoint → ScalarCoordinateCarrier) :
    algebraicCartanReduction source { configuration with scalar := scalar } =
      { algebraicCartanReduction source configuration with scalar := scalar } := by
  have connection :
      (algebraicCartanReduction source { configuration with scalar := scalar }).gravityConnection =
        (algebraicCartanReduction source configuration).gravityConnection := by
    funext point
    change diracDualFormNativeActionCartanConnectionAt source
      (formNativeP286GaugeConstitutiveReadout source { configuration with scalar := scalar }) point =
      diracDualFormNativeActionCartanConnectionAt source
        (formNativeP286GaugeConstitutiveReadout source configuration) point
    unfold diracDualFormNativeActionCartanConnectionAt
      diracDualFormNativeActionCartanContorsionAt diracDualFormNativeActionCartanTorsionAt
    rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at source
      (formNativeP286GaugeConstitutiveReadout source { configuration with scalar := scalar })
      (formNativeP286GaugeConstitutiveReadout source configuration) point rfl rfl rfl]
    rfl
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · exact connection
  · rfl
  · change formNativeGravityReactionField
      (algebraicCartanReduction source { configuration with scalar := scalar }) =
        formNativeGravityReactionField (algebraicCartanReduction source configuration)
    unfold formNativeGravityReactionField holonomicContravariantGravityCurvature
    funext point
    apply congrArg₂ (· - ·)
    · rfl
    · exact congrArg gravityInternalPairVarianceNormalization
        (curvature_congr _ _ connection point)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem reduction_fixed (parameter : ℝ) :
    algebraicCartanReduction positiveSmoothUnifiedSource (Profile.testField parameter) =
      Profile.testField parameter := by
  unfold Profile.testField
  rw [reduction_scalar]
  have fixed : algebraicCartanReduction positiveSmoothUnifiedSource actual = actual :=
    algebraicCartanReduction_idempotent positiveSmoothUnifiedSource seed
  rw [fixed]

theorem smooth (parameter : ℝ) : (Profile.testField parameter).Smooth := by
  have scalarSmooth : ContDiff ℝ ∞ (Profile.testField parameter).scalar := by
    rw [show (Profile.testField parameter).scalar = fun p =>
      direction + (parameter * Profile.wave p) • direction by
      funext p; rw [Profile.testField, actual_scalar]; rfl]
    have waveSmooth : ContDiff ℝ ∞ Profile.wave := by
      unfold Profile.wave
      exact (contDiff_const.mul (EuclideanSpace.proj (0 : Fin 4)).contDiff).sinh
    exact contDiff_const.add ((contDiff_const.mul waveSmooth).smul contDiff_const)
  exact ⟨actual_smooth.1, actual_smooth.2.1, actual_smooth.2.2.1,
    actual_smooth.2.2.2.1, actual_smooth.2.2.2.2.1, actual_smooth.2.2.2.2.2.1,
    scalarSmooth, actual_smooth.2.2.2.2.2.2.2⟩

theorem nondegenerate (parameter : ℝ) : (Profile.testField parameter).Nondegenerate := by
  intro point
  change Matrix.det (actual.coframe point) ≠ 0
  exact actual_nondegenerate point

theorem four_constraints (parameter : ℝ) (point : BasePoint) :
    let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (Profile.testField parameter) point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 := by
  have g := algebraicCartanReduction_gravityMultiplier_zero positiveSmoothUnifiedSource
    (Profile.testField parameter) point
  have b := algebraicCartanReduction_gravityAuxiliary_zero positiveSmoothUnifiedSource
    (Profile.testField parameter) point
  have a := algebraicCartanReduction_p286Auxiliary_zero positiveSmoothUnifiedSource
    (Profile.testField parameter) (nondegenerate parameter) point
  have l := algebraicCartanReduction_lorentz_zero positiveSmoothUnifiedSource
    (Profile.testField parameter) (smooth parameter) (nondegenerate parameter) point
  rw [reduction_fixed] at g b a l
  exact ⟨g, b, a, l⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Contact.Constraints
