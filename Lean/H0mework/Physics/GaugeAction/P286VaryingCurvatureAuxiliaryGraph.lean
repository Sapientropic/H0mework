import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryEquation

/-!
# S9-C3h67: exact P286 auxiliary graph at varying actual curvature

The P286 auxiliary is not a branch choice.  For every nondegenerate coframe
and every P286 curvature, the zero fiber of the complete constitutive
residual is exactly the graph of the existing source-generated solver.

The second theorem specializes this statement to the genuine
`dA + [A,A]` curvature of an arbitrary Stage-9 holonomic configuration.  It
does not freeze that curvature to a reference value and accepts no shell,
stationarity, or realization receipt.  Consequently a later state update may
derive the P286 auxiliary from its updated primitive connection without
introducing a free parameter.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286VaryingCurvatureAuxiliaryGraph

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation

noncomputable section

set_option autoImplicit false

/-- At arbitrary curvature, the coordinate residual vanishes exactly at the
source-generated constitutive auxiliary.  Invertibility uses both the
nondegenerate coframe Hodge operator and the already generated nonzero strong
coupling. -/
theorem p286CoordinateGaugeAuxiliaryResidual_eq_zero_iff_eq_constitutive
    (source : SmoothUnifiedSource)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature auxiliary : P286GaugeTwoForm) :
    p286CoordinateGaugeAuxiliaryEquationResidual
        (coframeGaugeSpacetimeHodgeLinear coframe)
        ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
        curvature auxiliary = 0 ↔
      auxiliary =
        p286GaugeConstitutiveAuxiliaryCoordinate source coframe curvature := by
  let couplingSquared : ℝ :=
    (sourceGeneratedUnifiedCouplings source).strongCouplingSquared
  have couplingNonzero : couplingSquared ≠ 0 :=
    ne_of_gt (sourceGeneratedUnifiedCouplings source).strong_pos
  constructor
  · intro residualZero
    have equation :
        curvature =
          liftGaugeTwoFormOperator
            (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            auxiliary := by
      exact sub_eq_zero.mp residualZero
    have solved :=
      p286GaugeConstitutiveAuxiliaryCoordinate_solves source coframe
        nondegenerate curvature
    have operatorEquality :
        liftGaugeTwoFormOperator
            (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            auxiliary =
          liftGaugeTwoFormOperator
            (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (p286GaugeConstitutiveAuxiliaryCoordinate source coframe
              curvature) :=
      equation.symm.trans solved.symm
    have scaledHodgeEquality :
        couplingSquared •
            liftGaugeTwoFormOperator
              (coframeGaugeSpacetimeHodgeLinear coframe) auxiliary =
          couplingSquared •
            liftGaugeTwoFormOperator
              (coframeGaugeSpacetimeHodgeLinear coframe)
              (p286GaugeConstitutiveAuxiliaryCoordinate source coframe
                curvature) := by
      simpa only [liftGaugeTwoFormOperator_smul_operator_p286] using
        operatorEquality
    have hodgeEquality :
        liftGaugeTwoFormOperator
            (coframeGaugeSpacetimeHodgeLinear coframe) auxiliary =
          liftGaugeTwoFormOperator
            (coframeGaugeSpacetimeHodgeLinear coframe)
            (p286GaugeConstitutiveAuxiliaryCoordinate source coframe
              curvature) := by
      apply sub_eq_zero.mp
      apply (smul_eq_zero.mp ?_).resolve_left couplingNonzero
      rw [smul_sub, scaledHodgeEquality, sub_self]
    exact (liftGaugeSpacetimeHodge_injective_p286 coframe nondegenerate)
      hodgeEquality
  · intro auxiliaryEquality
    subst auxiliary
    apply sub_eq_zero.mpr
    exact (p286GaugeConstitutiveAuxiliaryCoordinate_solves source coframe
      nondegenerate curvature).symm

/-- Field-level graph theorem for the actual non-Abelian P286 curvature of an
arbitrary holonomic configuration. -/
theorem holonomicP286GaugeAuxiliaryResidual_eq_zero_iff_eq_generated
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0) :
    holonomicP286GaugeAuxiliaryEquationResidual source configuration point = 0 ↔
      configuration.gaugeAuxiliary point =
        generatedP286GaugeConstitutiveAuxiliary source
          (configuration.coframe point)
          (holonomicGaugeCurvature configuration point) := by
  rw [holonomicP286GaugeAuxiliaryEquationResidual]
  constructor
  · intro residualZero
    have coordinateEquality :=
      (p286CoordinateGaugeAuxiliaryResidual_eq_zero_iff_eq_constitutive
        source (configuration.coframe point) nondegenerate
        (holonomicP286GaugeCurvatureCoordinate configuration point)
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)).mp
        residualZero
    funext pair
    apply p286CoordinateEquiv.injective
    have componentEquality := congrFun coordinateEquality pair
    simp only [generatedP286GaugeConstitutiveAuxiliary,
      p286CoordinateEquiv.apply_symm_apply]
    change p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) =
      p286GaugeConstitutiveAuxiliaryCoordinate source
        (configuration.coframe point)
        (fun candidate => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point candidate)) pair
    change p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) =
      p286GaugeConstitutiveAuxiliaryCoordinate source
        (configuration.coframe point)
        (fun candidate => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point candidate)) pair at componentEquality
    exact componentEquality
  · intro auxiliaryEquality
    apply
      (p286CoordinateGaugeAuxiliaryResidual_eq_zero_iff_eq_constitutive
        source (configuration.coframe point) nondegenerate
        (holonomicP286GaugeCurvatureCoordinate configuration point)
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)).mpr
    funext pair
    have componentEquality := congrArg p286CoordinateEquiv
      (congrFun auxiliaryEquality pair)
    simp only [generatedP286GaugeConstitutiveAuxiliary,
      p286CoordinateEquiv.apply_symm_apply] at componentEquality
    change p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) =
      p286GaugeConstitutiveAuxiliaryCoordinate source
        (configuration.coframe point)
        (fun candidate => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point candidate)) pair
    change p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) =
      p286GaugeConstitutiveAuxiliaryCoordinate source
        (configuration.coframe point)
        (fun candidate => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point candidate)) pair at componentEquality
    exact componentEquality

end

end SaturationMonoid.PhysicsCore.StageNineP286VaryingCurvatureAuxiliaryGraph
