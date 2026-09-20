import H0mework.Physics.GaugeSource.CompactEntropyDescent

/-!
# Source-native reduced P286 entropy descent

This module continues the compact primitive-connection descent through the
actual constitutive write.  At every parameter the primitive path recomputes
its curvature and then installs

`B(t) = K_e⁻¹(F(A(t)))`.

Because `F(A+t a)` is quadratic and the constitutive inverse is linear in
curvature at the fixed coframe, the reduced gauge density is quartic.  The
complete reduced relative action therefore has an exact quartic normal form.
Its first coefficient is still the compact negative-gradient defect; a step
computed from the absolute values of the other three coefficients yields
finite descent without a Hessian-sign or coercivity premise.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286SourceNativeReducedEntropyDescent

open MeasureTheory
open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineCoframeGravityGaugeRegularity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeMotherAction
open StageNineFormNativeP286GaugeConnectionIntegratedVariation
open StageNineFormNativeP286GaugeConnectionLocalVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineP286SourceNativeCompactEntropyDescent
open StageNinePlebanskiMultiplierVariation
open StageNineTopologicalFourFormPairing
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance reducedEntropyP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance reducedEntropyP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance reducedEntropyP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Linear constitutive response and quartic gauge polynomial -/

theorem p286EliminatedAuxiliaryCoordinate_add
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
        (first + second) =
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          coframe first +
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          coframe second := by
  rw [formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum,
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum,
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum]
  funext output
  simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  module

theorem p286EliminatedAuxiliaryCoordinate_smul
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (parameter : ℝ)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
        (parameter • curvature) =
      parameter •
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          coframe curvature := by
  rw [formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum,
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum]
  funext output
  ext index
  simp [smul_smul, Finset.smul_sum, mul_comm]

@[simp] theorem p286EliminatedAuxiliaryCoordinate_zero
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe) :
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
        0 = 0 := by
  rw [formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_neg_constitutive]
  simp

theorem p286CoordinateWedge_add_left
    (first second residual : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (first + second) residual =
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first residual +
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing second
          residual := by
  unfold generatedTwoFormWedgeCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  exact p286CoordinateLiePairing_add_left _ _ _

theorem p286CoordinateWedge_add_right
    (first second residual : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing residual
        (first + second) =
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing residual first +
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing residual
          second := by
  unfold generatedTwoFormWedgeCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  exact p286CoordinateLiePairing_add_right _ _ _

theorem p286CoordinateWedge_smul_left
    (parameter : ℝ)
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (parameter • first) second =
      parameter *
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first
          second := by
  unfold generatedTwoFormWedgeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  exact p286CoordinateLiePairing_smul_left _ _ _

theorem p286CoordinateWedge_smul_right
    (parameter : ℝ)
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first
        (parameter • second) =
      parameter *
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first
          second := by
  unfold generatedTwoFormWedgeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  exact p286CoordinateLiePairing_smul_right _ _ _

@[simp] theorem p286CoordinateWedge_zero_left
    (second : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing 0 second = 0 := by
  simpa using p286CoordinateWedge_smul_left 0 second second

@[simp] theorem p286CoordinateWedge_zero_right
    (first : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first 0 = 0 := by
  simpa using p286CoordinateWedge_smul_right 0 first first

theorem p286CoordinateWedge_eq_formNative
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first second =
      formNativeP286GaugeWedgeCoefficient
        (formNativeP286GaugeCoordinateToActualLinear first)
        (formNativeP286GaugeCoordinateToActualLinear second) := by
  unfold generatedTwoFormWedgeCoefficient
    formNativeP286GaugeWedgeCoefficient
    formNativeP286LiePairing p286CoordinateLiePairing p286LiePairing
    formNativeP286GaugeCoordinateToActualLinear
  unfold generatedTwoFormWedgeCoefficient
  simp

theorem p286EliminatedAuxiliaryCoordinate_continuous
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : BasePoint → LorentzianCoframe)
    (curvature : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (coframeContinuous : Continuous coframe)
    (nondegenerate : ∀ point, Matrix.det (coframe point) ≠ 0)
    (curvatureContinuous : Continuous curvature) :
    Continuous fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        (coframe point) (curvature point) := by
  rw [continuous_iff_continuousAt]
  intro point
  have composed := ContinuousAt.comp
    (f := fun candidate : BasePoint =>
      (coframe candidate, curvature candidate))
    (g := fun joint :
        LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        joint.1 joint.2)
    (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      boundary (coframe point) (nondegenerate point) (curvature point)
      ).continuousAt
    (coframeContinuous.prodMk curvatureContinuous).continuousAt
  simpa [Function.comp_def] using composed

theorem p286CoordinateWedge_continuous
    (first second : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (first point) (second point) := by
  unfold generatedTwoFormWedgeCoefficient
  apply continuous_finsetSum
  intro pair _
  exact p286CoordinateLiePairing_apply_continuous
    (fun point => first point pair)
    (fun point => second point (twoFormComplement pair))
    ((continuous_apply pair).comp firstContinuous)
    ((continuous_apply (twoFormComplement pair)).comp secondContinuous)

/-- Gauge action after exact algebraic elimination, in the faithful P286
coordinate carrier. -/
def p286ReducedGaugeDensity
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) : ℝ :=
  (1 / 2 : ℝ) *
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
      (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        coframe curvature)
      curvature

def p286ReducedGaugeFirstCoefficient
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature linear : FormNativeP286GaugeCoordinateTwoForm) : ℝ :=
  let baseAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      curvature
  let linearAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      linear
  (1 / 2 : ℝ) *
    (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing baseAuxiliary
        linear +
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        linearAuxiliary curvature)

def p286ReducedGaugeSecondCoefficient
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature linear quadratic : FormNativeP286GaugeCoordinateTwoForm) : ℝ :=
  let baseAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      curvature
  let linearAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      linear
  let quadraticAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      quadratic
  (1 / 2 : ℝ) *
    (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing baseAuxiliary
          quadratic +
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          linearAuxiliary linear +
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          quadraticAuxiliary curvature)

def p286ReducedGaugeThirdCoefficient
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (linear quadratic : FormNativeP286GaugeCoordinateTwoForm) : ℝ :=
  let linearAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      linear
  let quadraticAuxiliary :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary coframe
      quadratic
  (1 / 2 : ℝ) *
    (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing linearAuxiliary
          quadratic +
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        quadraticAuxiliary linear)

def p286ReducedGaugeFourthCoefficient
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (quadratic : FormNativeP286GaugeCoordinateTwoForm) : ℝ :=
  (1 / 2 : ℝ) *
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
      (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        coframe quadratic)
      quadratic

theorem p286ReducedGaugeDensity_quartic
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature linear quadratic : FormNativeP286GaugeCoordinateTwoForm)
    (parameter : ℝ) :
    p286ReducedGaugeDensity boundary coframe
        (curvature + parameter • linear + parameter ^ 2 • quadratic) =
      p286ReducedGaugeDensity boundary coframe curvature +
        parameter *
          p286ReducedGaugeFirstCoefficient boundary coframe curvature linear +
        parameter ^ 2 *
          p286ReducedGaugeSecondCoefficient boundary coframe curvature linear
            quadratic +
        parameter ^ 3 *
          p286ReducedGaugeThirdCoefficient boundary coframe linear quadratic +
        parameter ^ 4 *
          p286ReducedGaugeFourthCoefficient boundary coframe quadratic := by
  unfold p286ReducedGaugeDensity p286ReducedGaugeFirstCoefficient
    p286ReducedGaugeSecondCoefficient p286ReducedGaugeThirdCoefficient
    p286ReducedGaugeFourthCoefficient
  rw [p286EliminatedAuxiliaryCoordinate_add,
    p286EliminatedAuxiliaryCoordinate_add,
    p286EliminatedAuxiliaryCoordinate_smul,
    p286EliminatedAuxiliaryCoordinate_smul]
  simp only [p286CoordinateWedge_add_left,
    p286CoordinateWedge_add_right,
    p286CoordinateWedge_smul_left,
    p286CoordinateWedge_smul_right]
  ring

theorem p286ReducedGaugeFirstCoefficient_eq_connection
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature linear : FormNativeP286GaugeCoordinateTwoForm) :
    p286ReducedGaugeFirstCoefficient boundary coframe curvature linear =
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          coframe curvature)
        linear := by
  let baseAuxiliaryActual :=
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
      (formNativeP286GaugeCoordinateToActualLinear curvature)
  let linearAuxiliaryActual :=
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
      (formNativeP286GaugeCoordinateToActualLinear linear)
  have baseSolved :=
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves boundary coframe
      nondegenerate (formNativeP286GaugeCoordinateToActualLinear curvature)
  have linearSolved :=
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves boundary coframe
      nondegenerate (formNativeP286GaugeCoordinateToActualLinear linear)
  have selfAdjoint :=
    formNativeP286GaugeWedgeCoefficient_blockwiseConstitutive_symmetric
      coframe nondegenerate
      (boundary.strongCouplingSquared : ℝ)
      (boundary.weakCouplingSquared : ℝ)
      (boundary.hyperchargeCouplingSquared : ℝ)
      linearAuxiliaryActual baseAuxiliaryActual
  change
    formNativeP286BlockwiseConstitutive coframe
        (boundary.strongCouplingSquared : ℝ)
        (boundary.weakCouplingSquared : ℝ)
        (boundary.hyperchargeCouplingSquared : ℝ)
        baseAuxiliaryActual =
      formNativeP286GaugeCoordinateToActualLinear curvature at baseSolved
  change
    formNativeP286BlockwiseConstitutive coframe
        (boundary.strongCouplingSquared : ℝ)
        (boundary.weakCouplingSquared : ℝ)
        (boundary.hyperchargeCouplingSquared : ℝ)
        linearAuxiliaryActual =
      formNativeP286GaugeCoordinateToActualLinear linear at linearSolved
  rw [baseSolved, linearSolved] at selfAdjoint
  unfold p286ReducedGaugeFirstCoefficient
  have baseCoordinate :
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          coframe curvature =
        formNativeP286GaugeActualToCoordinateLinear baseAuxiliaryActual := rfl
  have linearCoordinate :
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          coframe linear =
        formNativeP286GaugeActualToCoordinateLinear linearAuxiliaryActual := rfl
  rw [baseCoordinate, linearCoordinate]
  dsimp only
  have firstActual := p286CoordinateWedge_eq_formNative
    (formNativeP286GaugeActualToCoordinateLinear baseAuxiliaryActual) linear
  have secondActual := p286CoordinateWedge_eq_formNative
    (formNativeP286GaugeActualToCoordinateLinear linearAuxiliaryActual)
    curvature
  simp only [formNativeP286GaugeActual_coordinate_actual]
    at firstActual secondActual
  rw [firstActual, secondActual]
  nlinarith [selfAdjoint]

/-! ## The actual constitutive readout is the reduced polynomial -/

theorem generatedFormNativeGaugeDensity_constitutiveReadout_eq_reduced
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (toContinuumPointField
          (formNativeP286GaugeConstitutiveReadout source configuration) point) =
      p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
        (configuration.coframe point)
        (holonomicP286GaugeCurvatureCoordinate configuration point) := by
  rw [toContinuumPointField_formNativeP286GaugeConstitutiveReadout]
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  have solved :=
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves
      (sourceGeneratedUnifiedCouplings source)
      (configuration.coframe point) (nondegenerate point)
      (holonomicGaugeCurvature configuration point)
  change
    formNativeP286GaugeWedgeCoefficient
          (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            (configuration.coframe point)
            (holonomicGaugeCurvature configuration point))
          (holonomicGaugeCurvature configuration point) -
        (1 / 2 : ℝ) *
          formNativeP286GaugeWedgeCoefficient
            (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
              (sourceGeneratedUnifiedCouplings source)
              (configuration.coframe point)
              (holonomicGaugeCurvature configuration point))
            (formNativeP286BlockwiseConstitutive
              (configuration.coframe point)
              ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared :
                ℝ)
              ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared :
                ℝ)
              ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared :
                ℝ)
              (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                (configuration.coframe point)
                (holonomicGaugeCurvature configuration point))) = _
  rw [solved]
  unfold p286ReducedGaugeDensity
  have coordinatePairing :=
    formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate
      (toContinuumPointField
        (formNativeP286GaugeConstitutiveReadout source configuration) point)
      (holonomicP286GaugeCurvatureCoordinate configuration point)
  unfold formNativeP286GaugeConnectionBFFirstVariationDensity
    p286AuxiliaryCoordinate at coordinatePairing
  rw [toContinuumPointField_formNativeP286GaugeConstitutiveReadout]
    at coordinatePairing
  have curvatureActual :=
    formNativeP286GaugeCurvatureCoordinateToActual_readout
      (toContinuumPointField configuration point)
  change
    formNativeP286GaugeCurvatureCoordinateToActual
        (holonomicP286GaugeCurvatureCoordinate configuration point) =
      holonomicGaugeCurvature configuration point at curvatureActual
  have curvatureActualLinear :
      formNativeP286GaugeCoordinateToActualLinear
          (holonomicP286GaugeCurvatureCoordinate configuration point) =
        holonomicGaugeCurvature configuration point := by
    funext pair
    simp [holonomicP286GaugeCurvatureCoordinate]
  rw [curvatureActual] at coordinatePairing
  have coordinatePairing' :
      formNativeP286GaugeWedgeCoefficient
            (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
              (sourceGeneratedUnifiedCouplings source)
              (configuration.coframe point)
              (holonomicGaugeCurvature configuration point))
            (holonomicGaugeCurvature configuration point) =
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            (configuration.coframe point)
            (holonomicP286GaugeCurvatureCoordinate configuration point))
          (holonomicP286GaugeCurvatureCoordinate configuration point) := by
    unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    rw [curvatureActualLinear]
    simpa [formNativeP286GaugeActualToCoordinateLinear]
      using coordinatePairing
  nlinarith [coordinatePairing']

theorem sourceGeneratedFormNativeLocalDensity_constitutiveReadout_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (point : BasePoint) :
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (formNativeP286GaugeConstitutiveReadout source configuration)
          point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField configuration point) -
        generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField configuration point) +
        p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
          (configuration.coframe point)
          (holonomicP286GaugeCurvatureCoordinate configuration point) := by
  unfold sourceGeneratedFormNativeUnifiedLocalDensity
    generatedFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedFormNativeGaugeDensity_constitutiveReadout_eq_reduced source
    configuration nondegenerate point]
  rw [toContinuumPointField_formNativeP286GaugeConstitutiveReadout]
  simp only [generatedFormNativeGravityBFDensity_withP286Auxiliary,
    generatedFormNativeGravityConstraintDensity_withP286Auxiliary,
    generatedFormNativeMatterDensity_withP286Auxiliary]
  ring

/-! ## Canonical reduced path generated from an arbitrary current -/

/-- Algebraically reduced base generated before the dynamical connection
leg. -/
def p286ReducedEntropyBase
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout source current

theorem p286ReducedEntropyBase_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (p286ReducedEntropyBase source current).Smooth :=
  formNativeP286GaugeConstitutiveReadout_smooth source current smooth
    nondegenerate

theorem p286ReducedEntropyBase_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (p286ReducedEntropyBase source current).Nondegenerate :=
  formNativeP286GaugeConstitutiveReadout_nondegenerate source current
    nondegenerate

theorem p286ReducedEntropyBase_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286ReducedEntropyBase source current) :=
  formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation source
    current nondegenerate

theorem p286ReducedEntropyBase_auxiliaryCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (p286ReducedEntropyBase source current) point =
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point) := by
  have coordinateActual :
      formNativeP286GaugeCoordinateToActualLinear
          (holonomicP286GaugeCurvatureCoordinate
            (p286ReducedEntropyBase source current) point) =
        holonomicGaugeCurvature (p286ReducedEntropyBase source current)
          point := by
    funext pair
    simp [holonomicP286GaugeCurvatureCoordinate]
  funext pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
  rw [coordinateActual]
  change
    p286CoordinateEquiv
        ((p286ReducedEntropyBase source current).gaugeAuxiliary point pair) =
      p286CoordinateEquiv
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          ((p286ReducedEntropyBase source current).coframe point)
          (holonomicGaugeCurvature (p286ReducedEntropyBase source current)
            point) pair)
  unfold p286ReducedEntropyBase
  rfl

def p286ReducedEntropyVariation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    CompactlySupportedSmoothVariation P286GaugeOneForm :=
  p286CompactNegativeGradientVariation source
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)

def p286ReducedEntropyRawPath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate (p286ReducedEntropyBase source current)
    (p286ReducedEntropyVariation source current smooth nondegenerate) parameter

/-- At every parameter the curvature-generated constitutive auxiliary is
recomputed; this is the reduced joint `A/F/B` material path. -/
def p286ReducedEntropyJointPath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout source
    (p286ReducedEntropyRawPath source current smooth nondegenerate parameter)

def p286ReducedEntropyLinearCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  p286GaugeConnectionLinearCurvatureVariation
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyVariation source current smooth nondegenerate) point

def p286ReducedEntropyQuadraticCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  p286GaugeConnectionQuadraticCurvatureVariation
    (p286ReducedEntropyVariation source current smooth nondegenerate) point

def p286ReducedEntropyLocalFirstCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) : ℝ :=
  holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyVariation source current smooth nondegenerate) point

def p286ReducedEntropyLocalSecondCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) : ℝ :=
  let base := p286ReducedEntropyBase source current
  let variation := p286ReducedEntropyVariation source current smooth
    nondegenerate
  let quadratic := p286ReducedEntropyQuadraticCurvature source current smooth
    nondegenerate point
  holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0 base
      variation point -
    formNativeP286GaugeConnectionBFFirstVariationDensity
      (toContinuumPointField base point) quadratic +
    p286ReducedGaugeSecondCoefficient (sourceGeneratedUnifiedCouplings source)
      (base.coframe point)
      (holonomicP286GaugeCurvatureCoordinate base point)
      (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
        point)
      quadratic

def p286ReducedEntropyLocalThirdCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) : ℝ :=
  p286ReducedGaugeThirdCoefficient (sourceGeneratedUnifiedCouplings source)
    ((p286ReducedEntropyBase source current).coframe point)
    (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
      point)
    (p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate
      point)

def p286ReducedEntropyLocalFourthCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) : ℝ :=
  p286ReducedGaugeFourthCoefficient (sourceGeneratedUnifiedCouplings source)
    ((p286ReducedEntropyBase source current).coframe point)
    (p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate
      point)

theorem p286ReducedEntropyRawPath_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ) :
    (p286ReducedEntropyRawPath source current smooth nondegenerate parameter
      ).Nondegenerate := by
  intro point
  change Matrix.det ((p286ReducedEntropyBase source current).coframe point) ≠ 0
  exact p286ReducedEntropyBase_nondegenerate source current nondegenerate point

theorem p286ReducedEntropyRawPath_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ) :
    (p286ReducedEntropyRawPath source current smooth nondegenerate parameter
      ).Smooth := by
  exact varyP286GaugeConnectionCoordinate_smooth_of_contDiff
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyVariation source current smooth nondegenerate)
    (p286ReducedEntropyVariation source current smooth nondegenerate).smooth
    parameter

theorem p286ReducedEntropyRawLocalDensity_quadratic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedEntropyRawPath source current smooth nondegenerate
            parameter) point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          p286ReducedEntropyLocalFirstCoefficient source current smooth
            nondegenerate point +
        parameter ^ 2 *
          holonomicFormNativeP286GaugeConnectionSecondVariationDensity source
            0 (p286ReducedEntropyBase source current)
            (p286ReducedEntropyVariation source current smooth nondegenerate)
            point := by
  exact holonomicFormNativeUnifiedLocalDensity_p286Connection_quadratic
    source 0 (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyVariation source current smooth nondegenerate)
    parameter point

theorem p286ReducedEntropyRawGaugeDensity_quadratic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ)
    (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (toContinuumPointField
          (p286ReducedEntropyRawPath source current smooth nondegenerate
            parameter) point) =
      generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          formNativeP286GaugeConnectionBFFirstVariationDensity
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point)
            (p286ReducedEntropyLinearCurvature source current smooth
              nondegenerate point) +
        parameter ^ 2 *
          formNativeP286GaugeConnectionBFFirstVariationDensity
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point)
            (p286ReducedEntropyQuadraticCurvature source current smooth
              nondegenerate point) := by
  rw [p286ReducedEntropyRawPath,
    toContinuumPointField_varyP286GaugeConnectionCoordinate
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
      (p286ReducedEntropyVariation source current smooth nondegenerate)
      parameter point]
  unfold variedP286CurvatureCoordinate p286ReducedEntropyLinearCurvature
    p286ReducedEntropyQuadraticCurvature
  exact generatedFormNativeGaugeDensityAtBoundary_connectionJets_quadratic
    (sourceGeneratedUnifiedCouplings source)
    (toContinuumPointField (p286ReducedEntropyBase source current) point)
    (p286GaugeConnectionLinearCurvatureVariation
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyVariation source current smooth nondegenerate) point)
    (p286GaugeConnectionQuadraticCurvatureVariation
      (p286ReducedEntropyVariation source current smooth nondegenerate) point)
    (variedP286ScalarCovariantDerivative
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyVariation source current smooth nondegenerate)
      parameter point)
    (variedP286MatterCovariantDerivative
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyVariation source current smooth nondegenerate)
      parameter point)
    parameter

theorem p286ReducedEntropyGaugeFirstCoefficient_eq_raw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) :
    p286ReducedGaugeFirstCoefficient
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point)
        (p286ReducedEntropyLinearCurvature source current smooth
          nondegenerate point) =
      formNativeP286GaugeConnectionBFFirstVariationDensity
        (toContinuumPointField (p286ReducedEntropyBase source current) point)
        (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
          point) := by
  rw [p286ReducedGaugeFirstCoefficient_eq_connection
    (sourceGeneratedUnifiedCouplings source)
    ((p286ReducedEntropyBase source current).coframe point)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate point)]
  rw [← p286ReducedEntropyBase_auxiliaryCoordinate source current point]
  exact
    (formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate
      (toContinuumPointField (p286ReducedEntropyBase source current) point)
      (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
        point)).symm

theorem p286ReducedEntropyJointLocalDensity_eq_raw_sub_gauge_add_reduced
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedEntropyJointPath source current smooth nondegenerate
            parameter) point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField
            (p286ReducedEntropyRawPath source current smooth nondegenerate
              parameter) point) -
        generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField
            (p286ReducedEntropyRawPath source current smooth nondegenerate
              parameter) point) +
        p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
          ((p286ReducedEntropyRawPath source current smooth nondegenerate
            parameter).coframe point)
          (holonomicP286GaugeCurvatureCoordinate
            (p286ReducedEntropyRawPath source current smooth nondegenerate
              parameter) point) := by
  exact sourceGeneratedFormNativeLocalDensity_constitutiveReadout_eq source
    (p286ReducedEntropyRawPath source current smooth nondegenerate parameter)
    (p286ReducedEntropyRawPath_nondegenerate source current smooth
      nondegenerate parameter) point

theorem p286ReducedEntropyBaseGaugeDensity_eq_reduced
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (toContinuumPointField (p286ReducedEntropyBase source current) point) =
      p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point) := by
  have fixed :
      p286ReducedEntropyBase source current =
        formNativeP286GaugeConstitutiveReadout source
          (p286ReducedEntropyBase source current) :=
    (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_nondegenerate source current nondegenerate)).1
      (p286ReducedEntropyBase_auxiliaryEquation source current nondegenerate)
  have actual :=
    generatedFormNativeGaugeDensity_constitutiveReadout_eq_reduced source
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_nondegenerate source current nondegenerate) point
  rw [← fixed] at actual
  exact actual

theorem p286ReducedEntropyJointGaugeDensity_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ)
    (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (toContinuumPointField
          (p286ReducedEntropyJointPath source current smooth nondegenerate
            parameter) point) =
      generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          formNativeP286GaugeConnectionBFFirstVariationDensity
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point)
            (p286ReducedEntropyLinearCurvature source current smooth
              nondegenerate point) +
        parameter ^ 2 *
          p286ReducedGaugeSecondCoefficient
            (sourceGeneratedUnifiedCouplings source)
            ((p286ReducedEntropyBase source current).coframe point)
            (holonomicP286GaugeCurvatureCoordinate
              (p286ReducedEntropyBase source current) point)
            (p286ReducedEntropyLinearCurvature source current smooth
              nondegenerate point)
            (p286ReducedEntropyQuadraticCurvature source current smooth
              nondegenerate point) +
        parameter ^ 3 *
          p286ReducedEntropyLocalThirdCoefficient source current smooth
            nondegenerate point +
        parameter ^ 4 *
          p286ReducedEntropyLocalFourthCoefficient source current smooth
            nondegenerate point := by
  unfold p286ReducedEntropyJointPath
  rw [generatedFormNativeGaugeDensity_constitutiveReadout_eq_reduced source
    (p286ReducedEntropyRawPath source current smooth nondegenerate parameter)
    (p286ReducedEntropyRawPath_nondegenerate source current smooth
      nondegenerate parameter) point]
  change
    p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyRawPath source current smooth nondegenerate
            parameter) point) = _
  have curvatureExpansion :=
    holonomicP286GaugeCurvatureCoordinate_expansion
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
      (p286ReducedEntropyVariation source current smooth nondegenerate)
      parameter point
  change
    holonomicP286GaugeCurvatureCoordinate
        (p286ReducedEntropyRawPath source current smooth nondegenerate
          parameter) point =
      holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point +
        parameter •
          p286ReducedEntropyLinearCurvature source current smooth
            nondegenerate point +
        parameter ^ 2 •
          p286ReducedEntropyQuadraticCurvature source current smooth
            nondegenerate point at curvatureExpansion
  rw [curvatureExpansion,
    p286ReducedGaugeDensity_quartic]
  rw [p286ReducedEntropyBaseGaugeDensity_eq_reduced source current
    nondegenerate point]
  rw [p286ReducedEntropyGaugeFirstCoefficient_eq_raw source current smooth
    nondegenerate point]
  rfl

theorem p286ReducedEntropyReducedGauge_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ)
    (point : BasePoint) :
    p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyRawPath source current smooth nondegenerate
          parameter).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyRawPath source current smooth nondegenerate
            parameter) point) =
      generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          formNativeP286GaugeConnectionBFFirstVariationDensity
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point)
            (p286ReducedEntropyLinearCurvature source current smooth
              nondegenerate point) +
        parameter ^ 2 *
          p286ReducedGaugeSecondCoefficient
            (sourceGeneratedUnifiedCouplings source)
            ((p286ReducedEntropyBase source current).coframe point)
            (holonomicP286GaugeCurvatureCoordinate
              (p286ReducedEntropyBase source current) point)
            (p286ReducedEntropyLinearCurvature source current smooth
              nondegenerate point)
            (p286ReducedEntropyQuadraticCurvature source current smooth
              nondegenerate point) +
        parameter ^ 3 *
          p286ReducedEntropyLocalThirdCoefficient source current smooth
            nondegenerate point +
        parameter ^ 4 *
          p286ReducedEntropyLocalFourthCoefficient source current smooth
            nondegenerate point := by
  calc
    _ = generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField
            (p286ReducedEntropyJointPath source current smooth nondegenerate
              parameter) point) := by
        exact
          (generatedFormNativeGaugeDensity_constitutiveReadout_eq_reduced
            source
            (p286ReducedEntropyRawPath source current smooth nondegenerate
              parameter)
            (p286ReducedEntropyRawPath_nondegenerate source current smooth
              nondegenerate parameter) point).symm
    _ = _ := p286ReducedEntropyJointGaugeDensity_quartic source current smooth
      nondegenerate parameter point

theorem p286ReducedEntropyJointLocalDensity_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedEntropyJointPath source current smooth nondegenerate
            parameter) point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          p286ReducedEntropyLocalFirstCoefficient source current smooth
            nondegenerate point +
        parameter ^ 2 *
          p286ReducedEntropyLocalSecondCoefficient source current smooth
            nondegenerate point +
        parameter ^ 3 *
          p286ReducedEntropyLocalThirdCoefficient source current smooth
            nondegenerate point +
        parameter ^ 4 *
          p286ReducedEntropyLocalFourthCoefficient source current smooth
            nondegenerate point := by
  rw [p286ReducedEntropyJointLocalDensity_eq_raw_sub_gauge_add_reduced source
    current smooth nondegenerate parameter point]
  rw [p286ReducedEntropyRawLocalDensity_quadratic source current smooth
    nondegenerate parameter point]
  rw [p286ReducedEntropyRawGaugeDensity_quadratic source current smooth
    nondegenerate parameter point]
  rw [p286ReducedEntropyReducedGauge_quartic source current smooth
    nondegenerate parameter point]
  unfold p286ReducedEntropyLocalSecondCoefficient
  dsimp only
  ring

/-! ## Compactness and integrability of the generated coefficients -/

theorem p286ReducedEntropyCoframe_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous (p286ReducedEntropyBase source current).coframe :=
  holonomicCoframe_continuous (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)

theorem p286ReducedEntropyCurvature_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous
      (holonomicP286GaugeCurvatureCoordinate
        (p286ReducedEntropyBase source current)) :=
  holonomicP286GaugeCurvatureCoordinate_continuous
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)

private theorem p286ReducedEntropyLinearCurvature_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous
      (p286ReducedEntropyLinearCurvature source current smooth nondegenerate) :=
  p286GaugeConnectionLinearCurvatureVariation_continuous
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyVariation source current smooth nondegenerate)

private theorem p286ReducedEntropyQuadraticCurvature_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous
      (p286ReducedEntropyQuadraticCurvature source current smooth
        nondegenerate) :=
  p286GaugeConnectionQuadraticCurvatureVariation_continuous
    (p286ReducedEntropyVariation source current smooth nondegenerate)

theorem p286ReducedEntropyEliminatedBase_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point) :=
  p286EliminatedAuxiliaryCoordinate_continuous
    (sourceGeneratedUnifiedCouplings source)
    (p286ReducedEntropyBase source current).coframe
    (holonomicP286GaugeCurvatureCoordinate
      (p286ReducedEntropyBase source current))
    (p286ReducedEntropyCoframe_continuous source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    (p286ReducedEntropyCurvature_continuous source current smooth
      nondegenerate)

private theorem p286ReducedEntropyEliminatedLinear_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
          point) :=
  p286EliminatedAuxiliaryCoordinate_continuous
    (sourceGeneratedUnifiedCouplings source)
    (p286ReducedEntropyBase source current).coframe
    (p286ReducedEntropyLinearCurvature source current smooth nondegenerate)
    (p286ReducedEntropyCoframe_continuous source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    (p286ReducedEntropyLinearCurvature_continuous source current smooth
      nondegenerate)

private theorem p286ReducedEntropyEliminatedQuadratic_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyQuadraticCurvature source current smooth
          nondegenerate point) :=
  p286EliminatedAuxiliaryCoordinate_continuous
    (sourceGeneratedUnifiedCouplings source)
    (p286ReducedEntropyBase source current).coframe
    (p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate)
    (p286ReducedEntropyCoframe_continuous source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    (p286ReducedEntropyQuadraticCurvature_continuous source current smooth
      nondegenerate)

theorem p286ReducedEntropyLocalThirdCoefficient_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous
      (p286ReducedEntropyLocalThirdCoefficient source current smooth
        nondegenerate) := by
  have firstWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
          point))
    (p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate)
    (p286ReducedEntropyEliminatedLinear_continuous source current smooth
      nondegenerate)
    (p286ReducedEntropyQuadraticCurvature_continuous source current smooth
      nondegenerate)
  have secondWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyQuadraticCurvature source current smooth
          nondegenerate point))
    (p286ReducedEntropyLinearCurvature source current smooth nondegenerate)
    (p286ReducedEntropyEliminatedQuadratic_continuous source current smooth
      nondegenerate)
    (p286ReducedEntropyLinearCurvature_continuous source current smooth
      nondegenerate)
  change Continuous fun point =>
    (1 / 2 : ℝ) *
      (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            ((p286ReducedEntropyBase source current).coframe point)
            (p286ReducedEntropyLinearCurvature source current smooth
              nondegenerate point))
          (p286ReducedEntropyQuadraticCurvature source current smooth
            nondegenerate point) +
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            ((p286ReducedEntropyBase source current).coframe point)
            (p286ReducedEntropyQuadraticCurvature source current smooth
              nondegenerate point))
          (p286ReducedEntropyLinearCurvature source current smooth
            nondegenerate point))
  exact continuous_const.mul (firstWedge.add secondWedge)

theorem p286ReducedEntropyLocalFourthCoefficient_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous
      (p286ReducedEntropyLocalFourthCoefficient source current smooth
        nondegenerate) := by
  have wedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyQuadraticCurvature source current smooth
          nondegenerate point))
    (p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate)
    (p286ReducedEntropyEliminatedQuadratic_continuous source current smooth
      nondegenerate)
    (p286ReducedEntropyQuadraticCurvature_continuous source current smooth
      nondegenerate)
  change Continuous fun point =>
    (1 / 2 : ℝ) *
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          ((p286ReducedEntropyBase source current).coframe point)
          (p286ReducedEntropyQuadraticCurvature source current smooth
            nondegenerate point))
        (p286ReducedEntropyQuadraticCurvature source current smooth
          nondegenerate point)
  exact continuous_const.mul wedge

theorem p286ReducedEntropyLocalSecondCoefficient_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Continuous
      (p286ReducedEntropyLocalSecondCoefficient source current smooth
        nondegenerate) := by
  let base := p286ReducedEntropyBase source current
  let variation := p286ReducedEntropyVariation source current smooth
    nondegenerate
  have rawSecond :=
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity_continuous
      source base (p286ReducedEntropyBase_smooth source current smooth
        nondegenerate)
      (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
      variation
  have rawGaugeQuadratic :=
    holonomicFormNativeP286GaugeConnectionBFSecondDensity_continuous base
      (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
      variation
  have baseQuadraticWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point))
    (p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate)
    (p286ReducedEntropyEliminatedBase_continuous source current smooth
      nondegenerate)
    (p286ReducedEntropyQuadraticCurvature_continuous source current smooth
      nondegenerate)
  have linearLinearWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyLinearCurvature source current smooth nondegenerate
          point))
    (p286ReducedEntropyLinearCurvature source current smooth nondegenerate)
    (p286ReducedEntropyEliminatedLinear_continuous source current smooth
      nondegenerate)
    (p286ReducedEntropyLinearCurvature_continuous source current smooth
      nondegenerate)
  have quadraticBaseWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedEntropyQuadraticCurvature source current smooth
          nondegenerate point))
    (holonomicP286GaugeCurvatureCoordinate
      (p286ReducedEntropyBase source current))
    (p286ReducedEntropyEliminatedQuadratic_continuous source current smooth
      nondegenerate)
    (p286ReducedEntropyCurvature_continuous source current smooth
      nondegenerate)
  have reducedSecond : Continuous fun point =>
      (1 / 2 : ℝ) *
        (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                ((p286ReducedEntropyBase source current).coframe point)
                (holonomicP286GaugeCurvatureCoordinate
                  (p286ReducedEntropyBase source current) point))
              (p286ReducedEntropyQuadraticCurvature source current smooth
                nondegenerate point) +
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                ((p286ReducedEntropyBase source current).coframe point)
                (p286ReducedEntropyLinearCurvature source current smooth
                  nondegenerate point))
              (p286ReducedEntropyLinearCurvature source current smooth
                nondegenerate point) +
            generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                ((p286ReducedEntropyBase source current).coframe point)
                (p286ReducedEntropyQuadraticCurvature source current smooth
                  nondegenerate point))
              (holonomicP286GaugeCurvatureCoordinate
                (p286ReducedEntropyBase source current) point)) :=
    continuous_const.mul
      ((baseQuadraticWedge.add linearLinearWedge).add quadraticBaseWedge)
  change Continuous fun point =>
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
          base variation point -
        formNativeP286GaugeConnectionBFFirstVariationDensity
          (toContinuumPointField base point)
          (p286ReducedEntropyQuadraticCurvature source current smooth
            nondegenerate point) +
      (1 / 2 : ℝ) *
        (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                (base.coframe point)
                (holonomicP286GaugeCurvatureCoordinate base point))
              (p286ReducedEntropyQuadraticCurvature source current smooth
                nondegenerate point) +
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                (base.coframe point)
                (p286ReducedEntropyLinearCurvature source current smooth
                  nondegenerate point))
              (p286ReducedEntropyLinearCurvature source current smooth
                nondegenerate point) +
            generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source)
                (base.coframe point)
                (p286ReducedEntropyQuadraticCurvature source current smooth
                  nondegenerate point))
              (holonomicP286GaugeCurvatureCoordinate base point))
  exact (rawSecond.sub rawGaugeQuadratic).add reducedSecond

theorem p286ReducedEntropyLocalFirstCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    HasCompactSupport
      (p286ReducedEntropyLocalFirstCoefficient source current smooth
        nondegenerate) :=
  holonomicFormNativeP286GaugeConnectionFirstVariationDensity_compact source 0
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyVariation source current smooth nondegenerate)

theorem p286ReducedEntropyLocalSecondCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    HasCompactSupport
      (p286ReducedEntropyLocalSecondCoefficient source current smooth
        nondegenerate) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero
      (p286ReducedEntropyVariation source current smooth nondegenerate)] with
    point jetZero
  have linearZero :
      p286ReducedEntropyLinearCurvature source current smooth nondegenerate
          point = 0 :=
    p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyVariation source current smooth nondegenerate) point
      jetZero.1 jetZero.2
  have quadraticZero :
      p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate
          point = 0 :=
    p286GaugeConnectionQuadraticCurvatureVariation_eq_zero
      (p286ReducedEntropyVariation source current smooth nondegenerate) point
      jetZero.1
  unfold p286ReducedEntropyLocalSecondCoefficient
  dsimp only
  rw [holonomicFormNativeP286GaugeConnectionSecondVariationDensity_eq_zero
    source 0 (p286ReducedEntropyBase source current)
    (p286ReducedEntropyVariation source current smooth nondegenerate) point
    jetZero.1]
  rw [linearZero, quadraticZero]
  simp [p286ReducedGaugeSecondCoefficient,
    formNativeP286GaugeConnectionBFFirstVariationDensity]

theorem p286ReducedEntropyLocalThirdCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    HasCompactSupport
      (p286ReducedEntropyLocalThirdCoefficient source current smooth
        nondegenerate) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero
      (p286ReducedEntropyVariation source current smooth nondegenerate)] with
    point jetZero
  have linearZero :
      p286ReducedEntropyLinearCurvature source current smooth nondegenerate
          point = 0 :=
    p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyVariation source current smooth nondegenerate) point
      jetZero.1 jetZero.2
  have quadraticZero :
      p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate
          point = 0 :=
    p286GaugeConnectionQuadraticCurvatureVariation_eq_zero
      (p286ReducedEntropyVariation source current smooth nondegenerate) point
      jetZero.1
  unfold p286ReducedEntropyLocalThirdCoefficient
  rw [linearZero, quadraticZero]
  simp [p286ReducedGaugeThirdCoefficient]

theorem p286ReducedEntropyLocalFourthCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    HasCompactSupport
      (p286ReducedEntropyLocalFourthCoefficient source current smooth
        nondegenerate) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero
      (p286ReducedEntropyVariation source current smooth nondegenerate)] with
    point jetZero
  have quadraticZero :
      p286ReducedEntropyQuadraticCurvature source current smooth nondegenerate
          point = 0 :=
    p286GaugeConnectionQuadraticCurvatureVariation_eq_zero
      (p286ReducedEntropyVariation source current smooth nondegenerate) point
      jetZero.1
  unfold p286ReducedEntropyLocalFourthCoefficient
  rw [quadraticZero]
  simp [p286ReducedGaugeFourthCoefficient]

theorem p286ReducedEntropyLocalFirstCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Integrable
      (p286ReducedEntropyLocalFirstCoefficient source current smooth
        nondegenerate) :=
  holonomicFormNativeP286GaugeConnectionFirstVariationDensity_integrable
    source (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    (p286ReducedEntropyVariation source current smooth nondegenerate)

theorem p286ReducedEntropyLocalSecondCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Integrable
      (p286ReducedEntropyLocalSecondCoefficient source current smooth
        nondegenerate) :=
  (p286ReducedEntropyLocalSecondCoefficient_continuous source current smooth
    nondegenerate).integrable_of_hasCompactSupport
      (p286ReducedEntropyLocalSecondCoefficient_compact source current smooth
        nondegenerate)

theorem p286ReducedEntropyLocalThirdCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Integrable
      (p286ReducedEntropyLocalThirdCoefficient source current smooth
        nondegenerate) :=
  (p286ReducedEntropyLocalThirdCoefficient_continuous source current smooth
    nondegenerate).integrable_of_hasCompactSupport
      (p286ReducedEntropyLocalThirdCoefficient_compact source current smooth
        nondegenerate)

theorem p286ReducedEntropyLocalFourthCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    Integrable
      (p286ReducedEntropyLocalFourthCoefficient source current smooth
        nondegenerate) :=
  (p286ReducedEntropyLocalFourthCoefficient_continuous source current smooth
    nondegenerate).integrable_of_hasCompactSupport
      (p286ReducedEntropyLocalFourthCoefficient_compact source current smooth
        nondegenerate)

/-! ## Integrated reduced entropy polynomial -/

def p286ReducedEntropyDefect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : ℝ :=
  p286CompactActionDefect source (p286ReducedEntropyBase source current)

def p286ReducedEntropyFirstCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedEntropyLocalFirstCoefficient source current smooth
      nondegenerate point

def p286ReducedEntropySecondCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedEntropyLocalSecondCoefficient source current smooth
      nondegenerate point

def p286ReducedEntropyThirdCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedEntropyLocalThirdCoefficient source current smooth
      nondegenerate point

def p286ReducedEntropyFourthCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedEntropyLocalFourthCoefficient source current smooth
      nondegenerate point

/-- Compact relative action of the fully reduced `A/F/B` path. -/
def p286ReducedEntropyRelativeAction
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ) : ℝ :=
  ∫ point : BasePoint,
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedEntropyJointPath source current smooth nondegenerate
            parameter) point) -
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField (p286ReducedEntropyBase source current) point)

theorem p286ReducedEntropyRelativeAction_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (parameter : ℝ) :
    p286ReducedEntropyRelativeAction source current smooth nondegenerate
        parameter =
      parameter *
          p286ReducedEntropyFirstCoefficient source current smooth
            nondegenerate +
        parameter ^ 2 *
          p286ReducedEntropySecondCoefficient source current smooth
            nondegenerate +
        parameter ^ 3 *
          p286ReducedEntropyThirdCoefficient source current smooth
            nondegenerate +
        parameter ^ 4 *
          p286ReducedEntropyFourthCoefficient source current smooth
            nondegenerate := by
  unfold p286ReducedEntropyRelativeAction
  rw [show (fun point : BasePoint =>
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField
            (p286ReducedEntropyJointPath source current smooth nondegenerate
              parameter) point) -
        sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point)) =
      fun point =>
        parameter *
            p286ReducedEntropyLocalFirstCoefficient source current smooth
              nondegenerate point +
          parameter ^ 2 *
            p286ReducedEntropyLocalSecondCoefficient source current smooth
              nondegenerate point +
          parameter ^ 3 *
            p286ReducedEntropyLocalThirdCoefficient source current smooth
              nondegenerate point +
          parameter ^ 4 *
            p286ReducedEntropyLocalFourthCoefficient source current smooth
              nondegenerate point by
    funext point
    rw [p286ReducedEntropyJointLocalDensity_quartic source current smooth
      nondegenerate parameter point]
    ring]
  have firstIntegrable :=
    p286ReducedEntropyLocalFirstCoefficient_integrable source current smooth
      nondegenerate
  have secondIntegrable :=
    p286ReducedEntropyLocalSecondCoefficient_integrable source current smooth
      nondegenerate
  have thirdIntegrable :=
    p286ReducedEntropyLocalThirdCoefficient_integrable source current smooth
      nondegenerate
  have fourthIntegrable :=
    p286ReducedEntropyLocalFourthCoefficient_integrable source current smooth
      nondegenerate
  let firstFunction := fun point : BasePoint => parameter *
    p286ReducedEntropyLocalFirstCoefficient source current smooth
      nondegenerate point
  let secondFunction := fun point : BasePoint => parameter ^ 2 *
    p286ReducedEntropyLocalSecondCoefficient source current smooth
      nondegenerate point
  let thirdFunction := fun point : BasePoint => parameter ^ 3 *
    p286ReducedEntropyLocalThirdCoefficient source current smooth
      nondegenerate point
  let fourthFunction := fun point : BasePoint => parameter ^ 4 *
    p286ReducedEntropyLocalFourthCoefficient source current smooth
      nondegenerate point
  have firstScaled : Integrable firstFunction := firstIntegrable.const_mul
    parameter
  have secondScaled : Integrable secondFunction := secondIntegrable.const_mul
    (parameter ^ 2)
  have thirdScaled : Integrable thirdFunction := thirdIntegrable.const_mul
    (parameter ^ 3)
  have fourthScaled : Integrable fourthFunction := fourthIntegrable.const_mul
    (parameter ^ 4)
  have firstSecond := firstScaled.add secondScaled
  have firstThird := firstSecond.add thirdScaled
  change integral volume
      (((firstFunction + secondFunction) + thirdFunction) + fourthFunction) = _
  calc
    _ = integral volume ((firstFunction + secondFunction) + thirdFunction) +
          integral volume fourthFunction := by
        change (∫ point : BasePoint,
          ((firstFunction + secondFunction) + thirdFunction) point +
            fourthFunction point) = _
        exact integral_add firstThird fourthScaled
    _ = (integral volume (firstFunction + secondFunction) +
          integral volume thirdFunction) + integral volume fourthFunction := by
        rw [show integral volume ((firstFunction + secondFunction) +
            thirdFunction) =
          integral volume (firstFunction + secondFunction) +
            integral volume thirdFunction by
          change (∫ point : BasePoint,
            (firstFunction + secondFunction) point + thirdFunction point) = _
          exact integral_add firstSecond thirdScaled]
    _ = ((integral volume firstFunction + integral volume secondFunction) +
          integral volume thirdFunction) + integral volume fourthFunction := by
        rw [show integral volume (firstFunction + secondFunction) =
          integral volume firstFunction + integral volume secondFunction by
          change (∫ point : BasePoint,
            firstFunction point + secondFunction point) = _
          exact integral_add firstScaled secondScaled]
    _ = _ := by
      unfold firstFunction secondFunction thirdFunction fourthFunction
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul]
      unfold p286ReducedEntropyFirstCoefficient
        p286ReducedEntropySecondCoefficient
        p286ReducedEntropyThirdCoefficient
        p286ReducedEntropyFourthCoefficient
      ring

theorem p286ReducedEntropyFirstCoefficient_eq_neg_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    p286ReducedEntropyFirstCoefficient source current smooth nondegenerate =
      -p286ReducedEntropyDefect source current := by
  exact p286CompactNegativeGradientFirstCoefficient_eq_neg_defect source
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)

theorem p286ReducedEntropyDefect_nonnegative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    0 ≤ p286ReducedEntropyDefect source current :=
  p286CompactActionDefect_nonnegative source
    (p286ReducedEntropyBase source current)

theorem p286ReducedEntropyDefect_pos_of_origin_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (originNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0
        (p286ReducedEntropyBase source current) 0 ≠ 0) :
    0 < p286ReducedEntropyDefect source current :=
  p286CompactActionDefect_pos_of_origin_euler_ne_zero source
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    originNonzero

end
end StageNineP286SourceNativeReducedEntropyDescent
end PhysicsCore
end SaturationMonoid
