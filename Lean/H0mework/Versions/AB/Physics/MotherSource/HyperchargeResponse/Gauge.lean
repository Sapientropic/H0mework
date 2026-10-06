import H0mework.Versions.R2.Physics.RootRuntime.RecoveryConsumer
import H0mework.Versions.R2.Physics.SpinPair.GaugeField

/-! Subordinate source-action calculation for the original Stage-10 occurrence.
The temporal Abelian perturbation retains the original scalar, matter and
independent dual. The scalar response and full mother density are computed in the
downstream Scalar and Mother modules. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
namespace SaturationMonoid.PhysicsCore.Stage10.HyperchargeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGaugeWedge StageNineTopologicalFourFormPairing
open StageNineFormNativeGaugeAuxiliaryVariation StageNineFormNativeMotherAction
open Stage9C.Dynamics.Homogeneous EmpiricalReferenceScaleCouplingBoundary
open Stage9C.Material.SpinPair
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- Original Abelian generator in the full P286 connection. -/
def chargeDirection : P286LieBlockData := (0, 0, hyperchargeGenerator)

/-- An actual primitive connection variation of the complete U configuration. -/
def primitive (potential : BasePoint → ℝ) : StageNineHolonomicConfiguration :=
  { Stage10.Runtime.configuration with
    gaugeConnection := fun point direction =>
      Stage10.Runtime.configuration.gaugeConnection point direction +
        (if direction = 0 then potential point else 0) • chargeDirection }

/-- The same action's constitutive inverse regenerates its auxiliary field. -/
def configuration (potential : BasePoint → ℝ) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout Stage10.Runtime.source (primitive potential)

theorem retains_matter (potential : BasePoint → ℝ) :
    (primitive potential).scalar = Stage10.Runtime.configuration.scalar ∧
    (primitive potential).matter = Stage10.Runtime.configuration.matter ∧
    (primitive potential).conjugateMatter =
      Stage10.Runtime.configuration.conjugateMatter := by
  dsimp only [primitive]
  exact ⟨rfl, rfl, rfl⟩

theorem connection_bracket (potential : BasePoint → ℝ) (point : BasePoint)
    (first second : LorentzianIndex) :
    p286LieBracket ((primitive potential).gaugeConnection point first)
        ((primitive potential).gaugeConnection point second) =
      p286LieBracket (Stage10.Runtime.configuration.gaugeConnection point first)
        (Stage10.Runtime.configuration.gaugeConnection point second) := by
  by_cases hfirst : first = 0 <;> by_cases hsecond : second = 0 <;>
    simp [primitive, chargeDirection, p286LieBracket, hfirst, hsecond]

theorem connection_derivative (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286ConnectionDerivative (primitive potential) point derivativeDirection formDirection =
      (if formDirection = 0 then
        fieldDirectionalDerivative potential point derivativeDirection else 0) • chargeDirection := by
  have original : Stage10.Runtime.configuration.gaugeConnection = fun _ => gaugePotential gaugeScale := by
    rw [Stage10.Runtime.configuration_eq, actual_gaugeConnection]
  unfold p286ConnectionDerivative
  simp only [primitive, original, map_add, map_smul]
  by_cases zero : formDirection = 0
  · subst formDirection
    simp only [ite_true, gaugePotential, Matrix.cons_val_zero, map_zero, zero_add]
    unfold fieldDirectionalDerivative
    rw [fderiv_smul_const regular]
    simp
  · simp [zero, fieldDirectionalDerivative]

def electricCurvature (electric : Fin 3 → ℝ) : Fin 6 → P286LieBlockData :=
  ![-electric 0 • chargeDirection, -electric 1 • chargeDirection,
    -electric 2 • chargeDirection, 0, 0, 0]

/-- The full non-Abelian background is retained; the new curvature is generated
by differentiating the temporal potential, with no supplied inverse-distance kernel. -/
theorem curvature (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point) :
    holonomicGaugeCurvature (primitive potential) point =
      magneticCurvature gaugeScale +
        electricCurvature (fun axis => fieldDirectionalDerivative potential point axis.succ) := by
  have original : holonomicGaugeCurvature Stage10.Runtime.configuration point =
      magneticCurvature gaugeScale := by
    rw [Stage10.Runtime.configuration_eq, actual_gaugeCurvature]
  have originalDerivative (first second : LorentzianIndex) :
      p286ConnectionDerivative Stage10.Runtime.configuration point first second = 0 := by
    rw [Stage10.Runtime.configuration_eq]
    simp [p286ConnectionDerivative, actual_gaugeConnection, fieldDirectionalDerivative]
  rw [← original]
  funext pair
  simp only [holonomicGaugeCurvature, connection_derivative potential point regular,
    connection_bracket, originalDerivative, sub_self, zero_add, Pi.add_apply]
  fin_cases pair <;> simp [pairFirst, pairSecond, electricCurvature] <;> module

def splitCurvature (magnetic : Fin 3 → SU3BlockLieMatrix) (electric : Fin 3 → ℝ) :
    FormNativeP286GaugeTwoForm :=
  ![(0, 0, -electric 0 • hyperchargeGenerator),
    (0, 0, -electric 1 • hyperchargeGenerator),
    (0, 0, -electric 2 • hyperchargeGenerator),
    (magnetic 0, 0, 0), (magnetic 1, 0, 0), (magnetic 2, 0, 0)]

/-- The source's three-block constitutive inverse determines the stiffness;
the calculation retains the entire color magnetic contribution. -/
theorem reduced_density (boundary : EmpiricalReferenceScaleCouplings)
    (clock : ℝ) (nonzero : clock ≠ 0)
    (magnetic : Fin 3 → SU3BlockLieMatrix) (electric : Fin 3 → ℝ) :
    (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary
        (homogeneousCoframe clock) (splitCurvature magnetic electric))
      (splitCurvature magnetic electric) =
        -((boundary.strongCouplingSquared : ℝ)⁻¹ * clock⁻¹ / 2) *
          (∑ axis, specialUnitaryLiePairing (magnetic axis) (magnetic axis)) +
        ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹ * clock / 2) *
          (∑ axis, (electric axis)^2) := by
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary formNativeP286LiftedCoframeHodge
  rw [homogeneousHodge_lift clock nonzero]
  simp [formNativeP286GaugeWedgeCoefficient, generatedTwoFormWedgeCoefficient,
    formNativeP286BlockScale, formNativeP286LiePairing, splitCurvature,
    Fin.sum_univ_six, Fin.sum_univ_three, twoFormComplement,
    specialUnitaryLiePairing,
    hyperchargeLiePairing, hyperchargeGenerator, Complex.mul_re, Complex.mul_im]
  ring

theorem constitutive_gauge_density (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (nondegenerate : background.Nondegenerate)
    (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField (formNativeP286GaugeConstitutiveReadout source background) point) =
    (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source) (background.coframe point)
        (holonomicGaugeCurvature background point))
      (holonomicGaugeCurvature background point) := by
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  have equation := formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation
    source background nondegenerate point
  unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary at equation
  rw [← equation]
  simp only [toContinuumPointField,
    holonomicGaugeCurvature_formNativeP286GaugeConstitutiveReadout,
    formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary]
  ring

theorem split_source_curvature (electric : Fin 3 → ℝ) :
    magneticCurvature gaugeScale + electricCurvature electric =
      splitCurvature (fun axis => -(gaugeScale^2) • (sourceColorP286Generator axis).1)
        electric := by
  funext pair
  fin_cases pair <;>
    simp [magneticCurvature, electricCurvature, splitCurvature, chargeDirection]
  all_goals
    apply Prod.ext
    · rfl
    · apply Prod.ext <;>
        simp [sourceColorP286Generator_weak_zero, sourceColorP286Generator_hypercharge_zero]

/-- Spatial gradient coefficient generated by the original coupling and lapse. -/
def stiffness : ℝ :=
  ((sourceGeneratedUnifiedCouplings Stage10.Runtime.source).hyperchargeCouplingSquared : ℝ)⁻¹ *
    lapse

theorem stiffness_positive : 0 < stiffness :=
  mul_pos (inv_pos.mpr (sourceGeneratedUnifiedCouplings Stage10.Runtime.source).hypercharge_pos)
    lapse_pos

/-- Retained color magnetic contribution of the original configuration. -/
def magneticDensity : ℝ :=
  -(((sourceGeneratedUnifiedCouplings Stage10.Runtime.source).strongCouplingSquared : ℝ)⁻¹ *
    lapse⁻¹ / 2) *
    ∑ axis, specialUnitaryLiePairing
      (-(gaugeScale^2) • (sourceColorP286Generator axis).1)
      (-(gaugeScale^2) • (sourceColorP286Generator axis).1)

/-- Exact positive gradient term inside the original full-field mother action.
The retained scalar and independent-dual matter terms are separate action summands. -/
theorem actual_gauge_density (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings Stage10.Runtime.source)
      (toContinuumPointField (configuration potential) point) =
      magneticDensity + stiffness / 2 *
        ∑ axis : Fin 3, (fieldDirectionalDerivative potential point axis.succ)^2 := by
  have nondegenerate : (primitive potential).Nondegenerate := by
    intro p
    dsimp only [primitive]
    rw [Stage10.Runtime.configuration_eq]
    exact actual_nondegenerate p
  unfold configuration
  rw [constitutive_gauge_density Stage10.Runtime.source (primitive potential) nondegenerate point,
    curvature potential point regular, split_source_curvature]
  have coframe : (primitive potential).coframe point = homogeneousCoframe lapse := by
    dsimp only [primitive]
    rw [Stage10.Runtime.configuration_eq, actual_coframe]
  rw [coframe, reduced_density _ lapse (ne_of_gt lapse_pos)]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.HyperchargeResponse
