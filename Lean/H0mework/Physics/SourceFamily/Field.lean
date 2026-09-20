import H0mework.Physics.SourceFamily.Parameters
import H0mework.Physics.SpinPair.Acceptance
import H0mework.Physics.SourceFormation.AuxiliaryFields

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation StageNineFormNativeGaugeWedge
open StageNineFormNativeP286GaugeConstitutiveElimination StageNineFormNativeP286GaugeYangMillsReadout
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeMotherAction
open StageNineBlockwiseConstitutive Stage9C.Reduction Stage9C.Dynamics.Homogeneous
open Stage9C.Material.SpinPair SU7MotherLieAlgebra DiracExteriorMatterAction
open scoped ContDiff

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _

/-- The original field supplies its carried materials. Only the source-
computed clock, vacuum and paired temporal phases are changed before the
existing joint action generates the auxiliary and Cartan fields. -/
def seedAt (step : ℕ) : StageNineHolonomicConfiguration :=
  { Runtime.configuration with
    coframe := fun _ => homogeneousCoframe (clock step)
    gaugeConnection := fun _ => gaugePotential gaugeScale
    scalar := fun _ => sourceGeneratedVacuumCoordinates (sourceAt step)
    matter := fun point => spinPairMatter (phase (phaseRate step) point) (phase (-phaseRate step) point)
    conjugateMatter := fun point => spinPairDual
      ((spinScale : ℂ) * phase (phaseRate step) point)
      ((spinScale : ℂ) * phase (-phaseRate step) point) }

def fieldAt (step : ℕ) : StageNineHolonomicConfiguration :=
  algebraicCartanReduction (sourceAt step) (seedAt step)

private theorem coefficients_smooth (rate : ℝ) :
    ContDiff ℝ ∞ (fun point => spinPairCoefficients (phase rate point) (phase (-rate) point)) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;> simp only [spinPairCoefficients]
  all_goals first
    | exact phase_smooth _
    | exact (phase_smooth _).neg
    | exact contDiff_const

private theorem seed_dual_smooth (step : ℕ) (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ (fun point => (seedAt step).conjugateMatter point
      (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) := by
  have upper : ContDiff ℝ ∞ (fun point => (spinScale : ℂ) * phase (phaseRate step) point) :=
    contDiff_const.mul (phase_smooth _)
  have lower : ContDiff ℝ ∞ (fun point => (spinScale : ℂ) * phase (-phaseRate step) point) :=
    contDiff_const.mul (phase_smooth _)
  change ContDiff ℝ ∞ (fun point => ∑ spin, ∑ state,
    spinPairCoefficients ((spinScale : ℂ) * phase (phaseRate step) point)
      ((spinScale : ℂ) * phase (-phaseRate step) point) spin state *
      sourceColorDoubletDual state
        (matterCoordinateEquiv.symm (EuclideanSpace.single index 1) spin))
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, spinPairCoefficients,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zero_mul, zero_add, add_zero]
  fun_prop

theorem seed_smooth (step : ℕ) : (seedAt step).Smooth := by
  have originalSmooth : Runtime.configuration.Smooth := by
    rw [Runtime.configuration_eq]
    exact actual_smooth
  obtain ⟨_, connection, gravityAuxiliary, multiplier, _, gaugeAuxiliary, _, _, _⟩ :=
    originalSmooth
  have gauge (direction : LorentzianIndex) : ContDiff ℝ ∞
      (fun _ : BasePoint => p286CoordinateEquiv (gaugePotential gaugeScale direction)) := contDiff_const
  refine ⟨fun _ _ => contDiff_const, connection, gravityAuxiliary, multiplier,
    gauge, gaugeAuxiliary, contDiff_const, ?_, seed_dual_smooth step⟩
  let linear := (sourceColorMatterCoordinateLinear.restrictScalars ℝ).toContinuousLinearMap
  exact linear.contDiff.comp (coefficients_smooth (phaseRate step))

theorem seed_nondegenerate (step : ℕ) : (seedAt step).Nondegenerate :=
  fun _ => homogeneousCoframe_nondegenerate (clock step) (clock_pos step)

theorem field_smooth (step : ℕ) : (fieldAt step).Smooth :=
  algebraicCartanReduction_smooth _ _ (seed_smooth step) (seed_nondegenerate step)

theorem field_nondegenerate (step : ℕ) : (fieldAt step).Nondegenerate :=
  algebraicCartanReduction_nondegenerate _ _ (seed_nondegenerate step)

theorem field_coframe (step : ℕ) :
    (fieldAt step).coframe = fun _ => homogeneousCoframe (clock step) := rfl

theorem field_connection (step : ℕ) :
    (fieldAt step).gaugeConnection = fun _ => gaugePotential gaugeScale := rfl

theorem field_curvature (step : ℕ) (point : BasePoint) :
    holonomicGaugeCurvature (fieldAt step) point = magneticCurvature gaugeScale :=
  constantGauge_curvature _ _ (field_connection step) point

theorem field_auxiliary_equation (step : ℕ) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation (sourceAt step) (fieldAt step) := by
  intro point
  apply (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).1
  exact algebraicCartanReduction_p286Auxiliary_zero _ _ (seed_nondegenerate step) point

/-- Four complete Euler channels are generated by the original joint writer,
independently of the remaining differential balances. -/
theorem algebraic_channels (step : ℕ) (point : BasePoint) :
    let residual := diracDualFormNativePointwiseJointResidual (sourceAt step) (fieldAt step) point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 :=
  ⟨algebraicCartanReduction_gravityMultiplier_zero _ _ point,
    algebraicCartanReduction_gravityAuxiliary_zero _ _ point,
    algebraicCartanReduction_p286Auxiliary_zero _ _ (seed_nondegenerate step) point,
    algebraicCartanReduction_lorentz_zero _ _ (seed_smooth step) (seed_nondegenerate step) point⟩

theorem generated_phase_derivative (step : ℕ) (point : BasePoint) :
    fieldDirectionalDerivative (phase (phaseRate step)) point 0 =
      phase (phaseRate step) point * (((3 * clock step / 2 * (spinScale - gaugeScale) : ℝ) : ℂ) * Complex.I) := by
  rw [phase_directionalDerivative]
  rfl

theorem field_source_action (step : ℕ) (chart : StageNineChart) (point : BasePoint)
    (variation : FormNativeP286GaugeTwoForm) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (sourceAt step) chart point
      (withFormNativeP286GaugeAuxiliary (toContinuumPointField (fieldAt step) point)
        ((fieldAt step).gaugeAuxiliary point + variation)) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (sourceAt step) chart point
        (toContinuumPointField (fieldAt step) point) -
      (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient variation
        (formNativeP286BlockwiseConstitutive ((fieldAt step).coframe point)
          (coupling step) (coupling step) (coupling step) variation) := by
  have zeroResidual : formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
      (sourceGeneratedUnifiedCouplings (sourceAt step))
      (toContinuumPointField (fieldAt step) point) = 0 :=
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).2
      (field_auxiliary_equation step point)
  have expansion := FullAuxiliary.current_auxiliary_quadratic (sourceAt step)
    (sourceGeneratedUnifiedCouplings (sourceAt step)) chart point
    (toContinuumPointField (fieldAt step) point) (field_nondegenerate step point) variation 1
  unfold formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary at expansion
  rw [zeroResidual, formNativeP286GaugeWedgeCoefficient_zero_right] at expansion
  unfold formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary at expansion
  rw [(source_couplings step).1, (source_couplings step).2.1,
    (source_couplings step).2.2] at expansion
  simpa only [sourceGeneratedDiracDualFormNativeUnifiedLocalDensity, one_smul, mul_zero, add_zero,
    one_pow, one_mul, toContinuumPointField,
    neg_mul, sub_eq_add_neg] using expansion

theorem seed_zero : seedAt 0 = Runtime.configuration := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  · change (fun _ => homogeneousCoframe (clock 0)) = Runtime.configuration.coframe
    rw [Runtime.configuration_eq, actual_coframe, clock_zero]
  · rw [Runtime.configuration_eq, actual_gaugeConnection]
    rfl
  · change (fun _ => sourceGeneratedVacuumCoordinates Runtime.source) = Runtime.configuration.scalar
    rw [Runtime.configuration_eq, actual_scalar, Runtime.source_eq]
  · change (fun point => spinPairMatter (phase (phaseRate 0) point) (phase (-phaseRate 0) point)) = _
    rw [Runtime.configuration_eq, actual_matter, phaseRate_zero]
    rfl
  · change (fun point => spinPairDual ((spinScale : ℂ) * phase (phaseRate 0) point)
      ((spinScale : ℂ) * phase (-phaseRate 0) point)) = _
    rw [Runtime.configuration_eq, actual_conjugateMatter, phaseRate_zero]
    rfl

theorem field_zero : fieldAt 0 = Runtime.configuration := by
  rw [fieldAt, seed_zero, Runtime.configuration_eq]
  change algebraicCartanReduction positiveSmoothUnifiedSource
    (algebraicCartanReduction positiveSmoothUnifiedSource Stage9C.Material.SpinPair.seed) = _
  exact algebraicCartanReduction_idempotent _ _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily
