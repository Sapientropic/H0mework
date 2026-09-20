import H0mework.Physics.LowEnergyEvolution.Geometry

/-! The original four algebraic/Cartan channels hold locally on the generated
strip. Pointwise coframe differentiability suffices for the computed II+ jet. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineCoframeFirstJet Stage9C.Reduction
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineIIPlusRestriction StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeLorentzGeometricKinematics StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineLorentzConnectionExteriorActionZeroFiber StageNineFormNativeMatterSpinThreeForm
open StageNineCartanTorsionThreeFormCoordinates StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormEquiv StageNineResidualLinearPlebanskiTorsionReduction
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGaugeAuxiliaryVariation StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section

theorem Solution.coframe_differentiable {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (row col : LorentzianIndex) :
    DifferentiableAt ℝ (fun p => flow.configuration.coframe p row col) point := by
  have dn := (flow.clock_derivative (point 0) inside).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  have da := (flow.coordinate_derivative (point 0) inside 0).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  simp_rw [flow.coframe, diagonalCoframe_apply]
  by_cases same : row = col
  · simp only [if_pos same]
    by_cases temporal : row = 0
    · simp only [if_pos temporal]
      exact dn.differentiableAt
    · simp only [if_neg temporal]
      exact da.differentiableAt
  · simp only [if_neg same]
    exact differentiableAt_const _

theorem computedAuxiliaryJet (current : StageNineHolonomicConfiguration) (point : BasePoint)
    (computed : current.gravityAuxiliary = fun p => physicalIIPlusBivector (current.coframe p))
    (differentiable : ∀ row col, DifferentiableAt ℝ (fun p => current.coframe p row col) point) :
    holonomicGravityAuxiliaryJet current point =
      pointwisePhysicalIIPlusJet (holonomicCoframeFirstJetAt current.coframe point) := by
  let jet := holonomicCoframeFirstJetAt current.coframe point
  let affine : StageNineHolonomicConfiguration :=
    { current with coframe := affineCoframeFieldOfJet jet }
  let reference := restrictHolonomicConfigurationToIIPlus affine
  have smooth : ContDiff ℝ ∞ affine.coframe := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro col
    exact affineCoframeFieldOfJet_componentwiseSmooth jet row col
  have jetEqual : holonomicCoframeFirstJetAt current.coframe point =
      holonomicCoframeFirstJetAt reference.coframe 0 :=
    (holonomicCoframeFirstJetAt_affine_origin jet).symm
  have equal := holonomicGravityAuxiliaryJet_eq_of_iiPlus_of_coframeFirstJet_eq
    current reference point 0 computed rfl differentiable
    (fun row col => (affineCoframeFieldOfJet_componentwiseSmooth jet row col).differentiable
      (by simp) |>.differentiableAt) jetEqual
  rw [equal]
  change holonomicGravityAuxiliaryJet (restrictHolonomicConfigurationToIIPlus affine) 0 = _
  rw [holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff affine smooth 0]
  exact congrArg pointwisePhysicalIIPlusJet (holonomicCoframeFirstJetAt_affine_origin jet)

theorem Solution.lorentz_euler_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0 flow.configuration point = 0 := by
  have currentNonzero :
      ((formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource flow.raw).coframe point).det ≠ 0 :=
    flow.nondegenerate_at point inside
  have torsion := sourceActionGeneratedDiracDualCartanReactionCurrentRestart_typedTorsionSpinAt
    positiveSmoothUnifiedSource (formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource flow.raw)
    point currentNonzero
  change cartanTorsionThreeForm (flow.configuration.coframe point)
      (actualPointwiseCartanTorsionTwoForm (holonomicCoframeFirstJetAt flow.configuration.coframe point)
        (flow.configuration.gravityConnection point)) =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource flow.configuration point at torsion
  have skew : LorentzSkew (flow.configuration.gravityConnection point) :=
    diracDualFormNativeActionCartanConnectionAt_lorentzSkew positiveSmoothUnifiedSource
      (formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource flow.raw) point currentNonzero
  have fixed : restrictHolonomicConfigurationToIIPlus flow.configuration = flow.configuration := by
    apply StageNineHolonomicConfiguration.ext <;> rfl
  apply (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current positiveSmoothUnifiedSource 0
    flow.configuration point).2
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
  rw [computedAuxiliaryJet flow.configuration point rfl (flow.coframe_differentiable point inside),
    pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe _ _ skew,
    ← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  exact torsion.trans (by unfold diracDualFormNativeActionSpinResponseAt; rw [fixed])

private theorem reductionP286Auxiliary_zero (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) (point : BasePoint)
    (nonzero : (current.coframe point).det ≠ 0) :
    (diracDualFormNativePointwiseJointResidual source (algebraicCartanReduction source current) point).p286GaugeAuxiliary = 0 := by
  change (diracDualFormNativePointwiseJointResidual source
    (formNativeP286GaugeConstitutiveReadout source current) point).p286GaugeAuxiliary = 0
  apply (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).2
  apply (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
    (sourceGeneratedUnifiedCouplings source)
    (toContinuumPointField (formNativeP286GaugeConstitutiveReadout source current) point) nonzero).2
  rfl

theorem Solution.p286_auxiliary_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource flow.configuration point).p286GaugeAuxiliary = 0 :=
  reductionP286Auxiliary_zero positiveSmoothUnifiedSource flow.raw point (flow.nondegenerate_at point inside)

theorem Solution.four_constraints {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource flow.configuration point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 := by
  exact ⟨algebraicCartanReduction_gravityMultiplier_zero positiveSmoothUnifiedSource flow.raw point,
    algebraicCartanReduction_gravityAuxiliary_zero positiveSmoothUnifiedSource flow.raw point,
    flow.p286_auxiliary_zero point inside, flow.lorentz_euler_zero point inside⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
