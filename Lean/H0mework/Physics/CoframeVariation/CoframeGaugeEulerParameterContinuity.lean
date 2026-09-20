import H0mework.Physics.Coframe.CoframeJointCalculus
import H0mework.Physics.CoframeVariation.CoframeLocalVariation
import H0mework.Physics.Gauge.GaugeAuxiliaryIntegratedVariation
import H0mework.Physics.Coframe.LinearPlebanskiCoframeActionPrincipal

/-!
# Parameter regularity of the coframe gauge Euler read

The gauge coframe density depends on a point field only through the live
P286 auxiliary and curvature coordinates.  This module packages that finite
parameter dependence and proves both continuity and `C¹` regularity of the
coframe Euler coordinate from the corresponding regularity of those two
generated parameter fields and the live coframe.  It is a readout theorem:
no Euler value, residual, target, branch, or regularity certificate for the
output is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open StageNineCoframeJointCalculus
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineHolonomicField
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Module.Free.ChooseBasisIndex.fintype ℝ P286LieBlockData

/-- Exact finite parameter inventory read by the gauge coframe density:
auxiliary first, curvature second. -/
abbrev CoframeGaugeActionParameter :=
  FormNativeP286GaugeCoordinateTwoForm ×
    FormNativeP286GaugeCoordinateTwoForm

def coframeGaugeActionParameterOfField
    (field : StageNineContinuumPointField) :
    CoframeGaugeActionParameter :=
  (formNativeP286GaugeActualToCoordinateLinear field.gaugeAuxiliary,
    formNativeP286GaugeActualToCoordinateLinear field.gaugeCurvature)

@[simp] theorem
    coframeGaugeActionParameterOfField_restrictContinuumPointFieldToIIPlus
    (field : StageNineContinuumPointField) :
    coframeGaugeActionParameterOfField
        (StageNineIIPlusRestriction.restrictContinuumPointFieldToIIPlus field) =
      coframeGaugeActionParameterOfField field :=
  rfl

/-- Coordinate normal form of the gauge density with its coframe argument
kept live. -/
def coframeGaugeActionCoordinateDensity
    (source : SmoothUnifiedSource)
    (parameter : CoframeGaugeActionParameter)
    (coframe : LorentzianCoframe) : ℝ :=
  formNativeP286GaugeCoordinateWedgeCoefficient parameter.1 parameter.2 -
    (1 / 2 : ℝ) *
      formNativeP286GaugeCoordinateWedgeCoefficient parameter.1
        (formNativeP286CoordinateBlockwiseConstitutive coframe
          ((sourceGeneratedUnifiedCouplings
            source).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            source).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            source).hyperchargeCouplingSquared : ℝ)
          parameter.1)

theorem diracDualFormNativeCoframeGaugeDensity_eq_coordinateDensity
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeGaugeDensity source field =
      coframeGaugeActionCoordinateDensity source
        (coframeGaugeActionParameterOfField field) := by
  funext coframe
  unfold diracDualFormNativeCoframeGaugeDensity
    coframeGaugeActionCoordinateDensity
    coframeGaugeActionParameterOfField
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286,
    formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual,
    formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  simp [formNativeP286CoordinateBlockwiseConstitutive, withCoframe]

private theorem coordinateWedge_contDiffAt_of_components
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center : E)
    (first second : E → FormNativeP286GaugeCoordinateTwoForm)
    (firstRegular : ∀ pair : Fin 6,
      ContDiffAt ℝ ∞ (fun point => first point pair) center)
    (secondRegular : ∀ pair : Fin 6,
      ContDiffAt ℝ ∞ (fun point => second point pair) center) :
    ContDiffAt ℝ ∞
      (fun point =>
        formNativeP286GaugeCoordinateWedgeCoefficient
          (first point) (second point)) center := by
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro pair _
  exact
    (formNativeP286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.contDiff.contDiffAt.comp center (firstRegular pair)).clm_apply
      (secondRegular (twoFormComplement pair))

private theorem blockwiseConstitutive_contDiffAt
    (source : SmoothUnifiedSource)
    (center : CoframeGaugeActionParameter × LorentzianCoframe)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
        formNativeP286CoordinateBlockwiseConstitutive joint.2
          ((sourceGeneratedUnifiedCouplings
            source).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            source).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            source).hyperchargeCouplingSquared : ℝ)
          joint.1.1)
      center := by
  apply contDiffAt_pi'
  intro output
  rw [show
    (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
      formNativeP286CoordinateBlockwiseConstitutive joint.2
        ((sourceGeneratedUnifiedCouplings
          source).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          source).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          source).hyperchargeCouplingSquared : ℝ)
        joint.1.1 output) =
      fun joint =>
        ∑ input : Fin 6,
          gaugeOperatorCoefficient
              (coframeGaugeSpacetimeHodgeLinear joint.2) output input •
            formNativeP286BlockwiseCouplingCoordinateLinear
              ((sourceGeneratedUnifiedCouplings
                source).strongCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                source).weakCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                source).hyperchargeCouplingSquared : ℝ)
              (joint.1.1 input) by
    funext joint
    exact congrFun
      (formNativeP286CoordinateBlockwiseConstitutive_eq_sum joint.2
        ((sourceGeneratedUnifiedCouplings
          source).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          source).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          source).hyperchargeCouplingSquared : ℝ)
        joint.1.1) output]
  apply ContDiffAt.sum
  intro input _
  have coefficientRegular : ContDiffAt ℝ ∞
      (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
        gaugeOperatorCoefficient
          (coframeGaugeSpacetimeHodgeLinear joint.2) output input)
      center :=
    (coframeHodgeOperatorCoefficient_contDiffAt center.2 nondegenerate
      output input).of_le (by norm_num) |>.comp center contDiffAt_snd
  have inputRegular : ContDiffAt ℝ ∞
      (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
        joint.1.1 input) center := by
    fun_prop
  have coupledInputRegular : ContDiffAt ℝ ∞
      (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
        formNativeP286BlockwiseCouplingCoordinateLinear
          ((sourceGeneratedUnifiedCouplings
            source).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            source).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            source).hyperchargeCouplingSquared : ℝ)
          (joint.1.1 input)) center :=
    (formNativeP286BlockwiseCouplingCoordinateLinear
      ((sourceGeneratedUnifiedCouplings
        source).strongCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings
        source).weakCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings
        source).hyperchargeCouplingSquared : ℝ))
      |>.toContinuousLinearMap.contDiff.contDiffAt.comp center inputRegular
  exact coefficientRegular.smul coupledInputRegular

/-- Joint smoothness of the finite gauge-parameter/coframe density on the
nondegenerate coframe locus. -/
theorem coframeGaugeActionCoordinateDensity_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (center : CoframeGaugeActionParameter × LorentzianCoframe)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (Function.uncurry (coframeGaugeActionCoordinateDensity source))
      center := by
  have auxiliaryRegular : ∀ pair : Fin 6,
      ContDiffAt ℝ ∞
        (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
          joint.1.1 pair) center := fun pair => by fun_prop
  have curvatureRegular : ∀ pair : Fin 6,
      ContDiffAt ℝ ∞
        (fun joint : CoframeGaugeActionParameter × LorentzianCoframe =>
          joint.1.2 pair) center := fun pair => by fun_prop
  have constitutiveRegular :=
    blockwiseConstitutive_contDiffAt source center nondegenerate
  unfold Function.uncurry coframeGaugeActionCoordinateDensity
  exact
    (coordinateWedge_contDiffAt_of_components center
      (fun joint => joint.1.1) (fun joint => joint.1.2)
      auxiliaryRegular curvatureRegular).sub
      (contDiffAt_const.mul
        (coordinateWedge_contDiffAt_of_components center
          (fun joint => joint.1.1)
          (fun joint =>
            formNativeP286CoordinateBlockwiseConstitutive joint.2
              ((sourceGeneratedUnifiedCouplings
                source).strongCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                source).weakCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                source).hyperchargeCouplingSquared : ℝ)
              joint.1.1)
          auxiliaryRegular
          (fun pair => contDiffAt_pi.mp constitutiveRegular pair)))

theorem diracDualFormNativeCoframeGaugeEulerCovector_eq_coordinateFDeriv
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeEulerCovector source field variation =
      fderiv ℝ
          (coframeGaugeActionCoordinateDensity source
            (coframeGaugeActionParameterOfField field))
          field.coframe variation := by
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [diracDualFormNativeCoframeGaugeDensity_eq_coordinateDensity]

/-- A smooth finite parameter/coframe family transfers any requested common
differentiability order to the generated gauge Euler coordinate.  The output
is still read from the actual density derivative; no Euler receipt is supplied
at the theorem mouth. -/
theorem diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_of_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞}
    (source : SmoothUnifiedSource)
    (field : E → StageNineContinuumPointField)
    (center : E)
    (parameterRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun point => coframeGaugeActionParameterOfField (field point)) center)
    (coframeRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun point => (field point).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun point =>
        diracDualFormNativeCoframeGaugeEulerCovector source (field point)
          (coframeCoordinateDirection row column)) center := by
  let selected : E → CoframeGaugeActionParameter × LorentzianCoframe :=
    fun point =>
      (coframeGaugeActionParameterOfField (field point),
        (field point).coframe)
  let family :
      (CoframeGaugeActionParameter × LorentzianCoframe) →
        LorentzianCoframe → ℝ :=
    fun carrier candidate =>
      coframeGaugeActionCoordinateDensity source carrier.1 candidate
  have familyJointSmooth : ContDiffAt ℝ ∞ (Function.uncurry family)
      (selected center, (field center).coframe) := by
    have base :=
      coframeGaugeActionCoordinateDensity_joint_contDiffAt source
        (coframeGaugeActionParameterOfField (field center),
          (field center).coframe) nondegenerate
    have projectionRegular : ContDiffAt ℝ ∞
        (fun joint :
            (CoframeGaugeActionParameter × LorentzianCoframe) ×
              LorentzianCoframe => (joint.1.1, joint.2))
        (selected center, (field center).coframe) := by
      fun_prop
    exact base.comp
      (selected center, (field center).coframe) projectionRegular
  have outerRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun carrier : CoframeGaugeActionParameter × LorentzianCoframe =>
        fderiv ℝ (family carrier) carrier.2
          (coframeCoordinateDirection row column))
      (selected center) := by
    have familyJointNext : ContDiffAt ℝ ((n + 1 : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry family)
        (selected center, (field center).coframe) :=
      familyJointSmooth.of_le
        (show ((n + 1 : ℕ∞) : WithTop ℕ∞) ≤
            ((⊤ : ℕ∞) : WithTop ℕ∞) from
          WithTop.coe_le_coe.mpr le_top)
    exact
      (ContDiffAt.fderiv (m := (n : WithTop ℕ∞))
        (by simpa using familyJointNext) (by fun_prop)
        (by simp)).clm_apply contDiffAt_const
  have selectedRegular : ContDiffAt ℝ (n : WithTop ℕ∞)
      selected center :=
    parameterRegular.prodMk coframeRegular
  rw [show
    (fun point =>
      diracDualFormNativeCoframeGaugeEulerCovector source (field point)
        (coframeCoordinateDirection row column)) =
      ((fun carrier : CoframeGaugeActionParameter × LorentzianCoframe =>
        fderiv ℝ (family carrier) carrier.2
          (coframeCoordinateDirection row column)) ∘ selected) by
    funext point
    rw [diracDualFormNativeCoframeGaugeEulerCovector_eq_coordinateFDeriv]
    rfl]
  exact outerRegular.comp center selectedRegular

theorem diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource)
    (field : E → StageNineContinuumPointField)
    (center : E)
    (parameterRegular : ContDiffAt ℝ ∞
      (fun point => coframeGaugeActionParameterOfField (field point)) center)
    (coframeRegular : ContDiffAt ℝ ∞
      (fun point => (field point).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        diracDualFormNativeCoframeGaugeEulerCovector source (field point)
          (coframeCoordinateDirection row column)) center :=
  diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_of_order
    source field center parameterRegular coframeRegular nondegenerate row column

/-- A continuous live auxiliary/curvature/coframe family produces a
continuous gauge Euler coordinate.  Only the finite parameter inventory read
by the action density appears in the hypotheses. -/
theorem diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource)
    (field : E → StageNineContinuumPointField)
    (center : E)
    (parameterRegular : ContDiffAt ℝ 0
      (fun point => coframeGaugeActionParameterOfField (field point)) center)
    (coframeRegular : ContDiffAt ℝ 0
      (fun point => (field point).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun point =>
        diracDualFormNativeCoframeGaugeEulerCovector source (field point)
          (coframeCoordinateDirection row column)) center :=
  diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_of_order
    source field center parameterRegular coframeRegular nondegenerate row column

/-- A `C¹` live auxiliary/curvature/coframe family produces a `C¹` gauge
Euler coordinate.  The derivative is paid by the smooth finite action
density; no Euler output is supplied at the theorem mouth. -/
theorem diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : SmoothUnifiedSource)
    (field : E → StageNineContinuumPointField)
    (center : E)
    (parameterRegular : ContDiffAt ℝ 1
      (fun point => coframeGaugeActionParameterOfField (field point)) center)
    (coframeRegular : ContDiffAt ℝ 1
      (fun point => (field point).coframe) center)
    (nondegenerate : Matrix.det (field center).coframe ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun point =>
        diracDualFormNativeCoframeGaugeEulerCovector source (field point)
          (coframeCoordinateDirection row column)) center :=
  diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_of_order
    source field center parameterRegular coframeRegular nondegenerate row column

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
