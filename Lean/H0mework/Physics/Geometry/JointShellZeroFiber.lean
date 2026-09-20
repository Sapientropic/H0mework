import H0mework.Physics.Admission.JointShellResidualCarrier

/-!
# S9-C3g2: strong-equation classification of the joint zero fiber

The residual carrier remains data-only.  This module classifies its global
zero fiber by the nine already named strong pointwise equations.  The result
does not assert smoothness, nondegeneracy, Bianchi compatibility,
integrability, stationarity, source reachability, or uniqueness.

The gravity ordering is part of the classification: simplicity is one
coordinate and `F - J B` is the next triangular coordinate.  Their joint
vanishing is the current strong algebraic gravity shell; no claim is made that
`F - J B` alone is the full off-shell auxiliary variation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineJointShellZeroFiber

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineBlockwiseConstitutive
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineLorentzConnectionPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineMatterPointwiseEquation
open StageNineScalarPointwiseEquation
open StageNineCoframeLocalDifferentiability
open StageNineCoframePointwiseEquation
open StageNineJointShellResidualCarrier
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false

/-- The nine named strong equations corresponding to the nine carrier
projections.  This is a zero-fiber classification predicate, not a source
credential and not a producer input. -/
structure CurrentStrongJointShellEquation
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  gravitySimplicity : GravitySimplicityEquation configuration
  gravityAuxiliary : GravityAuxiliaryEquation configuration
  p286GaugeAuxiliary : P286GaugeAuxiliaryEquation source configuration
  lorentzConnection :
    CanonicalLorentzConnectionPointwiseEquation source configuration
  p286GaugeConnection :
    CanonicalP286GaugeConnectionPointwiseEquation source configuration
  scalar : CanonicalScalarPointwiseEquation source configuration
  matter : CanonicalMatterPointwiseEquation source configuration
  conjugateMatter :
    CanonicalConjugateMatterPointwiseEquation source configuration
  coframe : CanonicalCoframePointwiseEquation source configuration

theorem gravitySimplicityResidual_eq_zero_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedGravitySimplicityResidual
        (toContinuumPointField configuration point) = 0 ↔
      configuration.gravityAuxiliary point =
        physicalIIPlusBivector (configuration.coframe point) := by
  simp [generatedGravitySimplicityResidual, toContinuumPointField, sub_eq_zero]

theorem gravityAuxiliaryResidual_eq_zero_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGravityAuxiliaryEquationResidual configuration point = 0 ↔
      holonomicGravityCurvature configuration point =
        gravityInternalDualEquiv (configuration.gravityAuxiliary point) := by
  simp [holonomicGravityAuxiliaryEquationResidual,
    gravityAuxiliaryEquationResidual, toContinuumPointField, sub_eq_zero]

theorem p286GaugeAuxiliaryResidual_eq_zero_iff
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryEquationResidual source configuration point =
        0 ↔
      holonomicGaugeCurvature configuration point =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (configuration.gaugeAuxiliary point) := by
  constructor
  · intro residualZero
    have coordinateEquation :
        holonomicP286GaugeCurvatureCoordinate configuration point =
          liftGaugeTwoFormOperator
            (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared :
                ℝ) •
              coframeGaugeSpacetimeHodgeLinear
                (configuration.coframe point))
            (holonomicP286GaugeAuxiliaryCoordinate configuration point) := by
      simpa [holonomicP286GaugeAuxiliaryEquationResidual,
        p286CoordinateGaugeAuxiliaryEquationResidual, sub_eq_zero] using
        residualZero
    funext pair
    apply p286CoordinateEquiv.injective
    rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]
    have coordinateComponent := congrFun coordinateEquation pair
    have auxiliaryCoordinateEquality :
        holonomicP286GaugeAuxiliaryCoordinate configuration point =
          fun input => p286CoordinateEquiv
            (configuration.gaugeAuxiliary point input) := by
      rfl
    rw [auxiliaryCoordinateEquality] at coordinateComponent
    simpa [holonomicP286GaugeCurvatureCoordinate,
      holonomicP286GaugeAuxiliaryCoordinate] using coordinateComponent
  · intro equation
    unfold holonomicP286GaugeAuxiliaryEquationResidual
      p286CoordinateGaugeAuxiliaryEquationResidual
    apply sub_eq_zero.mpr
    funext pair
    change p286CoordinateEquiv
        (holonomicGaugeCurvature configuration point pair) =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (fun input => p286CoordinateEquiv
          (configuration.gaugeAuxiliary point input)) pair
    rw [← p286CoordinateEquiv_liftGaugeTwoFormOperator]
    exact congrArg p286CoordinateEquiv (congrFun equation pair)

theorem currentJointShellZeroFiber_iff_strongEquation
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellZeroFiber source configuration ↔
      CurrentStrongJointShellEquation source configuration := by
  constructor
  · intro zeroFiber
    have pointwiseZero :=
      (currentJointShellZeroFiber_iff_pointwise source configuration).mp
        zeroFiber
    constructor
    · intro point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact (gravitySimplicityResidual_eq_zero_iff configuration point).mp
        components.1
    · intro point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact (gravityAuxiliaryResidual_eq_zero_iff configuration point).mp
        components.2.1
    · intro point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact (p286GaugeAuxiliaryResidual_eq_zero_iff source configuration
        point).mp components.2.2.1
    · intro direction
      funext point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact congrFun components.2.2.2.1 direction
    · intro direction
      funext point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact congrFun components.2.2.2.2.1 direction
    · intro direction
      funext point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact congrFun components.2.2.2.2.2.1 direction
    · intro direction
      funext point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact congrFun components.2.2.2.2.2.2.1 direction
    · intro direction
      funext point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact congrFun components.2.2.2.2.2.2.2.1 direction
    · intro point
      have components :=
        (onCurrentPointwiseJointShellZeroFiber_iff_components source
          configuration point).mp (pointwiseZero point)
      exact components.2.2.2.2.2.2.2.2
  · intro equations
    apply (currentJointShellZeroFiber_iff_pointwise source configuration).mpr
    intro point
    apply (onCurrentPointwiseJointShellZeroFiber_iff_components source
      configuration point).mpr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (gravitySimplicityResidual_eq_zero_iff configuration point).mpr
        (equations.gravitySimplicity point)
    · exact (gravityAuxiliaryResidual_eq_zero_iff configuration point).mpr
        (equations.gravityAuxiliary point)
    · exact (p286GaugeAuxiliaryResidual_eq_zero_iff source configuration
        point).mpr (equations.p286GaugeAuxiliary point)
    · funext direction
      exact congrFun (equations.lorentzConnection direction) point
    · funext direction
      exact congrFun (equations.p286GaugeConnection direction) point
    · funext direction
      exact congrFun (equations.scalar direction) point
    · funext direction
      exact congrFun (equations.matter direction) point
    · funext direction
      exact congrFun (equations.conjugateMatter direction) point
    · exact equations.coframe point

/-- Generic negative control: a nonzero EL layer cannot disappear merely
because the algebraic layer is zero. -/
theorem pointwiseJointResidual_ne_zero_of_eulerLagrange_ne_zero
    (residual : CurrentPointwiseJointShellResidualCarrier)
    (nonzero : residual.eulerLagrange ≠ 0) : residual ≠ 0 := by
  intro residualZero
  apply nonzero
  exact congrArg CurrentPointwiseJointShellResidualCarrier.eulerLagrange
    residualZero

/-- A pure carrier witness used to pin the separation between algebraic-shell
closure and full joint-shell closure.  It is not asserted to be generated by
a physical source. -/
def coframeOnlyPointwiseJointResidual
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    CurrentPointwiseJointShellResidualCarrier where
  algebraic := 0
  eulerLagrange :=
    { (0 : CurrentPointwiseEulerLagrangeResidualCarrier) with
      coframe := stress }

@[simp] theorem coframeOnlyPointwiseJointResidual_algebraic
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    (coframeOnlyPointwiseJointResidual stress).algebraic = 0 :=
  rfl

@[simp] theorem coframeOnlyPointwiseJointResidual_coframe
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    (coframeOnlyPointwiseJointResidual stress).eulerLagrange.coframe = stress :=
  rfl

/-- Negative regression: algebraic zero does not imply full joint zero. -/
theorem coframeOnlyPointwiseJointResidual_ne_zero
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (nonzero : stress ≠ 0) :
    coframeOnlyPointwiseJointResidual stress ≠ 0 := by
  intro residualZero
  apply nonzero
  have coframeZero := congrArg
    (fun residual => residual.eulerLagrange.coframe) residualZero
  simpa using coframeZero

end

end SaturationMonoid.PhysicsCore.StageNineJointShellZeroFiber
