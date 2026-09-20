import H0mework.Physics.MotherSource.GroundedRealization
import H0mework.Physics.SpinPair.KineticLoad
import H0mework.Physics.Homogeneous.GaugeBalance
import H0mework.Physics.MotherProgrammesFormationClockBF.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeVariation
open StageNineFormNativeMotherAction StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge StageNineTopologicalFourFormPairing
open StageNineP286ActionCauchySplit StageNineCartanTangentSimplicityResponse
open Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open scoped Matrix.Norms.Elementwise

noncomputable section

def motherSource : SmoothUnifiedSource := Runtime.source

/-- Two primitive variations of the original complete field. Coordinate time
is unchanged; `u` varies the physical coframe's time column. -/
def clockBFConfiguration (u b : ℝ) : StageNineHolonomicConfiguration :=
  { Runtime.configuration with
    coframe := fun x a c =>
      if c = canonicalLorentzianTimeDirection
      then (1 + u) * Runtime.configuration.coframe x a c
      else Runtime.configuration.coframe x a c
    gaugeAuxiliary := fun x => (1 + b) • Runtime.configuration.gaugeAuxiliary x }

def clockBFAction (u b : ℝ) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource 0 0
    (toContinuumPointField (clockBFConfiguration u b) 0)

theorem original_configuration : clockBFConfiguration 0 0 = Runtime.configuration := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  · funext x a c
    simp [clockBFConfiguration]
  · funext x
    simp [clockBFConfiguration]

theorem pointField (u b : ℝ) :
    toContinuumPointField (clockBFConfiguration u b) 0 =
      withFormNativeP286GaugeAuxiliary
        (withCoframe (toContinuumPointField actual 0) (homogeneousCoframe ((1 + u) * lapse)))
        ((1 + b) • actual.gaugeAuxiliary 0) := by
  unfold clockBFConfiguration
  rw [Runtime.configuration_eq]
  apply StageNineContinuumPointField.ext <;> try rfl
  funext a c
  rw [actual_coframe]
  fin_cases a <;> fin_cases c <;>
    simp [withFormNativeP286GaugeAuxiliary, withCoframe, toContinuumPointField,
      homogeneousCoframe, canonicalLorentzianTimeDirection]

def gaugeCoefficient : ℝ :=
  sourceCoupling * (gaugeScale ^ 2 / (sourceCoupling * lapse)) ^ 2 / 4

def responseScale : ℝ := 3 * gaugeCoefficient * lapse

theorem responseScale_value : responseScale = 9 * lapse / 5 := by
  unfold responseScale gaugeCoefficient gaugeScale
  rw [sourceCoupling_eq]
  have l := lapse_sq
  have s := spinScale_sq
  field_simp [ne_of_gt lapse_pos]
  nlinarith [sq_nonneg (spinScale ^ 2 - 2)]

theorem matter_clock (u : ℝ) (positive : 0 < 1 + u) :
    diracDualFormNativeCoframeMatterDensity motherSource 0 (toContinuumPointField actual 0)
      (homogeneousCoframe ((1 + u) * lapse)) =
      -6 * lapse * u * spinScale * (spinScale - gaugeScale) := by
  change diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource 0 _ _ = _
  rw [actual_frozenMatterDensity, homogeneousCoframe_det,
    abs_of_pos (mul_pos positive lapse_pos),
    homogeneousCoframe_inv _ (ne_of_gt (mul_pos positive lapse_pos)), actualKineticLoad_diagonal]
  simp [homogeneousCoframe, Fin.sum_univ_four]
  unfold frequency
  field_simp [ne_of_gt positive, ne_of_gt lapse_pos]
  ring

private theorem auxiliary_quadratic (u : ℝ) (positive : 0 < 1 + u) :
    formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary 0)
      (formNativeP286BlockwiseConstitutive (homogeneousCoframe ((1 + u) * lapse))
        sourceCoupling sourceCoupling sourceCoupling (actual.gaugeAuxiliary 0)) =
      -2 * responseScale * (1 + u) := by
  have paid := ClockBFMaterial.origin_auxiliary_quadratic (homogeneousCoframe ((1 + u) * lapse))
  unfold ClockBFMaterial.origin at paid
  rw [Runtime.configuration_eq,
    ClockBFMaterial.homogeneous_magnetic_trace _ (ne_of_gt (mul_pos positive lapse_pos))] at paid
  simp only [toContinuumPointField] at paid
  rw [paid]
  dsimp [responseScale, gaugeCoefficient]
  ring

private theorem original_BF :
    formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary 0)
      (holonomicGaugeCurvature actual 0) = -2 * responseScale := by
  have equation := Stage9C.Revision.SpinPair.initialState.auxiliaryEquation 0
  change holonomicGaugeCurvature actual 0 =
    formNativeP286BlockwiseConstitutive (homogeneousCoframe lapse)
      sourceCoupling sourceCoupling sourceCoupling (actual.gaugeAuxiliary 0) at equation
  rw [equation]
  simpa using auxiliary_quadratic 0 (by norm_num)

theorem gauge_clock (u b : ℝ) (positive : 0 < 1 + u) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings motherSource)
      (withFormNativeP286GaugeAuxiliary
        (withCoframe (toContinuumPointField actual 0) (homogeneousCoframe ((1 + u) * lapse)))
        ((1 + b) • actual.gaugeAuxiliary 0)) =
      responseScale * ((1 + u) * (1 + b)^2 - 2 * (1 + b)) := by
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  change formNativeP286GaugeWedgeCoefficient ((1 + b) • actual.gaugeAuxiliary 0)
      (holonomicGaugeCurvature actual 0) - (1/2 : ℝ) *
      formNativeP286GaugeWedgeCoefficient ((1 + b) • actual.gaugeAuxiliary 0)
        (formNativeP286BlockwiseConstitutive (homogeneousCoframe ((1 + u) * lapse))
          sourceCoupling sourceCoupling sourceCoupling ((1 + b) • actual.gaugeAuxiliary 0)) = _
  simp only [formNativeP286BlockwiseConstitutive_smul,
    formNativeP286GaugeWedgeCoefficient_smul_left, formNativeP286GaugeWedgeCoefficient_smul_right]
  rw [original_BF, auxiliary_quadratic u positive]
  ring

set_option maxHeartbeats 2000000 in
theorem gravity_clock (u : ℝ) :
    generatedFormNativeGravityConstraintDensity
      (withCoframe (toContinuumPointField actual 0) (homogeneousCoframe ((1 + u) * lapse))) =
      generatedFormNativeGravityConstraintDensity (toContinuumPointField actual 0) + 3 * lapse * u := by
  have frame : homogeneousCoframe ((1 + u) * lapse) =
      homogeneousCoframe lapse + (u * lapse) • Matrix.single 0 0 1 := by
    ext a c
    fin_cases a <;> fin_cases c <;> simp [homogeneousCoframe]
    ring
  have rankOne : physicalIIPlusBivector (Matrix.single 0 0 1) = 0 := by
    ext a c
    fin_cases a <;> fin_cases c <;>
      simp [physicalIIPlusBivector, coframeWedge, internalBivectorDual,
        lorentzianCoframeHodge, pairFirst, pairSecond]
  have reaction := actual_gravityReaction_coordinates (0 : BasePoint) 0 0
  change gravityTopologicalWedgeCoefficient (actual.gravitySimplicityMultiplier 0)
    (physicalIIPlusCoframeTangent (homogeneousCoframe lapse) (Matrix.single 0 0 1)) = -3 at reaction
  change gravityTopologicalWedgeCoefficient (actual.gravitySimplicityMultiplier 0)
      (actual.gravityAuxiliary 0 - physicalIIPlusBivector (homogeneousCoframe ((1 + u) * lapse))) =
    gravityTopologicalWedgeCoefficient (actual.gravitySimplicityMultiplier 0)
      (actual.gravityAuxiliary 0 - physicalIIPlusBivector (homogeneousCoframe lapse)) + 3 * lapse * u
  rw [frame, physicalIIPlusBivector_affine_expansion, rankOne, smul_zero, add_zero]
  rw [show actual.gravityAuxiliary 0 - (physicalIIPlusBivector (homogeneousCoframe lapse) +
      (u * lapse) • physicalIIPlusCoframeTangent (homogeneousCoframe lapse) (Matrix.single 0 0 1)) =
      (actual.gravityAuxiliary 0 - physicalIIPlusBivector (homogeneousCoframe lapse)) +
        (-(u * lapse)) • physicalIIPlusCoframeTangent (homogeneousCoframe lapse) (Matrix.single 0 0 1) by
      module]
  rw [gravityTopologicalWedgeCoefficient_add_right, gravityTopologicalWedgeCoefficient_smul_right, reaction]
  ring

private theorem action_parts (u b : ℝ) :
    clockBFAction u b =
      generatedFormNativeGravityBFDensity (toContinuumPointField actual 0) +
      generatedFormNativeGravityConstraintDensity
        (withCoframe (toContinuumPointField actual 0) (homogeneousCoframe ((1 + u) * lapse))) +
      generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings motherSource)
        (withFormNativeP286GaugeAuxiliary
          (withCoframe (toContinuumPointField actual 0) (homogeneousCoframe ((1 + u) * lapse)))
          ((1 + b) • actual.gaugeAuxiliary 0)) +
      diracDualFormNativeCoframeMatterDensity motherSource 0 (toContinuumPointField actual 0)
        (homogeneousCoframe ((1 + u) * lapse)) := by
  rw [clockBFAction, pointField]
  rfl

/-- Exact complete action, including the cubic remainder beyond the Hessian. -/
theorem action_normalForm (u b : ℝ) (positive : 0 < 1 + u) :
    clockBFAction u b = clockBFAction 0 0 + responseScale * (b^2 + 2*u*b + u*b^2) := by
  rw [action_parts u b, action_parts 0 0,
    gravity_clock u, gravity_clock 0, gauge_clock u b positive, gauge_clock 0 0 (by norm_num),
    matter_clock u positive, matter_clock 0 (by norm_num), responseScale_value]
  have load : spinScale * (spinScale - gaugeScale) = 4 / 5 := by
    nlinarith [spin_gauge_product, spinScale_sq]
  have matter : -6 * lapse * u * spinScale * (spinScale - gaugeScale) =
      -(24 / 5 : ℝ) * lapse * u := by
    linear_combination (-6 * lapse * u) * load
  rw [matter]
  ring

theorem responseScale_pos : 0 < responseScale := by
  rw [responseScale_value]
  exact div_pos (mul_pos (by norm_num) lapse_pos) (by norm_num)

def generatedB (u : ℝ) : ℝ := -u / (1 + u)
def effectiveClockAction (u : ℝ) : ℝ := clockBFAction 0 0 - responseScale * u^2 / (1 + u)

/-- The complete action generates its hidden B displacement, while the square
retains the full hidden coordinate and every cubic/higher rational effect. -/
theorem action_elimination (u b : ℝ) (positive : 0 < 1 + u) :
    clockBFAction u b = effectiveClockAction u +
      responseScale * (1 + u) * (b - generatedB u)^2 := by
  rw [action_normalForm u b positive]
  unfold effectiveClockAction generatedB
  field_simp [ne_of_gt positive]
  ring

theorem generatedB_action (u : ℝ) (positive : 0 < 1 + u) :
    clockBFAction u (generatedB u) = effectiveClockAction u := by
  rw [action_elimination u (generatedB u) positive]
  simp

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF
