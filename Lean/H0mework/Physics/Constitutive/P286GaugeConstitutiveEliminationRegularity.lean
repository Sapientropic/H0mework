import H0mework.Physics.Coframe.CoframeLocalDifferentiability
import H0mework.Physics.Gauge.GaugeAuxiliaryIntegratedVariation
import H0mework.Physics.Constitutive.P286GaugeConstitutiveElimination

/-!
# Regularity of the form-native P286 constitutive inverse

The authoritative algebraic action equivalence already generates the unique
three-block auxiliary

```text
B(e,F) = -diag(g_s^-2,g_w^-2,g_y^-2) (*_e F).
```

This module exposes that same operator in the faithful finite-dimensional
P286 coordinate chart and proves its joint local regularity in the live
coframe and curvature inputs.  It introduces no residual, target response,
branch, solution receipt, or new coupling.  The result is a producer API for
transporting first jets through the existing action-owned equivalence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeConstitutiveEliminationRegularity

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open StageNineBlockwiseConstitutive
open StageNineCoframeLocalDifferentiability
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance constitutiveRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance constitutiveRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance constitutiveRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Faithful coordinate presentation -/

/-- Coordinate presentation of the already authoritative constitutive
inverse.  The curvature input is a faithful coordinate two-form and is
converted to the actual Lie carrier before the action operator is applied. -/
def formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
      (formNativeP286GaugeCoordinateToActualLinear curvature))

/-- Explicit finite-dimensional normal form: the live Hodge coefficient acts
on spacetime indices, while the fixed source-owned inverse couplings act in
the P286 coordinate fiber. -/
theorem
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_neg_constitutive
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        coframe curvature =
      -formNativeP286CoordinateBlockwiseConstitutive coframe
        ((boundary.strongCouplingSquared : ℝ)⁻¹)
        ((boundary.weakCouplingSquared : ℝ)⁻¹)
        ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹)
        curvature := by
  unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
    formNativeP286CoordinateBlockwiseConstitutive
  rw [map_neg,
    formNativeP286BlockwiseConstitutive_eq_blockScale_hodge]

theorem formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        coframe curvature =
      fun output =>
        -∑ input : Fin 6,
          gaugeOperatorCoefficient
              (coframeGaugeSpacetimeHodgeLinear coframe) output input •
            formNativeP286BlockwiseCouplingCoordinateLinear
              ((boundary.strongCouplingSquared : ℝ)⁻¹)
              ((boundary.weakCouplingSquared : ℝ)⁻¹)
              ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹)
              (curvature input) := by
  rw [
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_neg_constitutive,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum]
  rfl

/-- Faithful-coordinate form of the already proved two-sided constitutive
equivalence.  In particular, applying the action-owned inverse to an actual
constitutive image returns the supplied primitive auxiliary coordinate; no
residual or solution receipt is involved. -/
theorem
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_constitutive
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (auxiliary : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        coframe
        (formNativeP286CoordinateBlockwiseConstitutive coframe
          (boundary.strongCouplingSquared : ℝ)
          (boundary.weakCouplingSquared : ℝ)
          (boundary.hyperchargeCouplingSquared : ℝ)
          auxiliary) =
      auxiliary := by
  unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    formNativeP286CoordinateBlockwiseConstitutive
  rw [formNativeP286GaugeActual_coordinate_actual]
  simpa only [formNativeP286GaugeCoordinate_actual_coordinate] using
    congrArg formNativeP286GaugeActualToCoordinateLinear
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary_constitutive
        boundary coframe nondegenerate
        (formNativeP286GaugeCoordinateToActualLinear auxiliary))

/-! ## Joint live-input regularity -/

/-- The action-owned inverse is jointly smooth at every nondegenerate live
coframe.  This is the exact regularity needed to transport a generated
coframe/curvature first jet through the constitutive write. -/
theorem
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    ContDiffAt ℝ ∞
      (fun joint :
          LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          joint.1 joint.2)
      (coframe, curvature) := by
  apply contDiffAt_pi'
  intro output
  rw [show
    (fun joint :
        LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
        joint.1 joint.2 output) =
      fun joint =>
        -∑ input : Fin 6,
          gaugeOperatorCoefficient
              (coframeGaugeSpacetimeHodgeLinear joint.1) output input •
            formNativeP286BlockwiseCouplingCoordinateLinear
              ((boundary.strongCouplingSquared : ℝ)⁻¹)
              ((boundary.weakCouplingSquared : ℝ)⁻¹)
              ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹)
              (joint.2 input) by
    funext joint
    exact congrFun
      (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_sum
        boundary joint.1 joint.2)
      output]
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro input _
  have coefficientSmooth :
      ContDiffAt ℝ ∞
        (fun joint :
            LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
          gaugeOperatorCoefficient
            (coframeGaugeSpacetimeHodgeLinear joint.1) output input)
        (coframe, curvature) :=
    (coframeHodgeOperatorCoefficient_contDiffAt coframe nondegenerate
      output input).comp (coframe, curvature) contDiffAt_fst
  have inputSmooth :
      ContDiffAt ℝ ∞
        (fun joint :
            LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
          joint.2 input)
        (coframe, curvature) := by
    fun_prop
  have coupledInputSmooth :
      ContDiffAt ℝ ∞
        (fun joint :
            LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
          formNativeP286BlockwiseCouplingCoordinateLinear
            ((boundary.strongCouplingSquared : ℝ)⁻¹)
            ((boundary.weakCouplingSquared : ℝ)⁻¹)
            ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹)
            (joint.2 input))
        (coframe, curvature) :=
    (formNativeP286BlockwiseCouplingCoordinateLinear
      ((boundary.strongCouplingSquared : ℝ)⁻¹)
      ((boundary.weakCouplingSquared : ℝ)⁻¹)
      ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹))
      |>.toContinuousLinearMap.contDiff.contDiffAt.comp
        (coframe, curvature) inputSmooth
  exact coefficientSmooth.smul coupledInputSmooth

theorem
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_differentiableAt
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    DifferentiableAt ℝ
      (fun joint :
          LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary boundary
          joint.1 joint.2)
      (coframe, curvature) :=
  (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
    boundary coframe nondegenerate curvature).differentiableAt (by simp)

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
