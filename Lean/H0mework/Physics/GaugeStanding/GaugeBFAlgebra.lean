import H0mework.Physics.GaugeAction.P286GaugeConnectionActionVariation
import H0mework.Physics.GaugeStanding.Variation
import H0mework.Physics.GaugeAction.P286SourceRelativeWardAlgebra

/-!
# S9-C: linked active P286 gauge--BF algebra

The same infinitesimal P286 parameter acts on the curvature and auxiliary
two-form by the adjoint representation.  This module proves directly from
the trace pairing that the complete gauge--BF first-order coefficient
vanishes.  The result consumes the actual primitive connection tangent and
its generated curvature response; it does not assume action invariance,
stationarity, a Ward receipt, or an equation of motion.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveGaugeBFAlgebra

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286BracketCalculus
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveVariation
open StageNineP286SourceRelativeWardAlgebra
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype

/-! ## The adjoint action commutes with spacetime-only operators -/

def p286GaugeTwoFormAdjoint
    (generator : P286CoordinateCarrier)
    (form : P286GaugeTwoForm) : P286GaugeTwoForm :=
  fun pair => p286CoordinateLieBracket generator (form pair)

theorem p286CoordinateLieBracket_skew
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracket first second =
      -p286CoordinateLieBracket second first := by
  simpa only [p286CoordinateLieBracket_eq_coordinateBracket] using
    coordinateBracket_skew first second

/-- Infinitesimal invariance of the actual P286 trace pairing. -/
theorem p286CoordinateLiePairing_adjoint_skew
    (generator first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing
          (p286CoordinateLieBracket generator first) second +
        p286CoordinateLiePairing first
          (p286CoordinateLieBracket generator second) =
      0 := by
  calc
    p286CoordinateLiePairing
          (p286CoordinateLieBracket generator first) second +
        p286CoordinateLiePairing first
          (p286CoordinateLieBracket generator second) =
      p286CoordinateLiePairing generator
          (p286CoordinateLieBracket first second) +
        p286CoordinateLiePairing
          (p286CoordinateLieBracket generator second) first := by
            rw [p286CoordinateLiePairing_bracket_left,
              p286CoordinateLiePairing_symmetric first
                (p286CoordinateLieBracket generator second)]
    _ =
      p286CoordinateLiePairing generator
          (p286CoordinateLieBracket first second) +
        p286CoordinateLiePairing generator
          (p286CoordinateLieBracket second first) := by
            rw [p286CoordinateLiePairing_bracket_left]
    _ = 0 := by
      rw [p286CoordinateLieBracket_skew second first]
      rw [show -p286CoordinateLieBracket first second =
          (-1 : ℝ) • p286CoordinateLieBracket first second by simp,
        p286CoordinateLiePairing_smul_right]
      ring

theorem liftGaugeTwoFormOperator_p286GaugeTwoFormAdjoint
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (generator : P286CoordinateCarrier)
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator operator
        (p286GaugeTwoFormAdjoint generator form) =
      p286GaugeTwoFormAdjoint generator
        (liftGaugeTwoFormOperator operator form) := by
  funext output
  unfold liftGaugeTwoFormOperator p286GaugeTwoFormAdjoint
  change
    (∑ input : Fin 6,
        gaugeOperatorCoefficient operator output input •
          p286CoordinateLieBracket generator (form input)) =
      p286CoordinateLieBracketBilinear generator
        (∑ input : Fin 6,
          gaugeOperatorCoefficient operator output input • form input)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul]
  rfl

/-- The coframe-pulled two-form pairing inherits infinitesimal adjoint
invariance because the coframe operator acts only on spacetime indices. -/
theorem generatedGaugeTwoFormMetricPairing_p286_adjoint_skew
    (coframe : LorentzianCoframe)
    (generator : P286CoordinateCarrier)
    (first second : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          (p286GaugeTwoFormAdjoint generator first) second +
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          first (p286GaugeTwoFormAdjoint generator second) =
      0 := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro pair _
  rw [liftGaugeTwoFormOperator_p286GaugeTwoFormAdjoint,
    liftGaugeTwoFormOperator_p286GaugeTwoFormAdjoint]
  simp only [p286GaugeTwoFormAdjoint]
  rw [← mul_add, p286CoordinateLiePairing_adjoint_skew, mul_zero]

/-! ## Complete gauge--BF first coefficient -/

/-- The connection-curvature leg plus the auxiliary leg of the same
gauge--BF density under one adjoint parameter. -/
def p286LinkedActiveGaugeBFFirstVariationDensity
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : P286GaugeTwoForm)
    (generator : P286CoordinateCarrier) : ℝ :=
  p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
      (p286GaugeTwoFormAdjoint generator curvature) +
    p286CoordinateGaugeAuxiliaryFirstVariationDensity coframe
      spacetimeHodge operator curvature auxiliary
      (p286GaugeTwoFormAdjoint generator auxiliary)

theorem p286LinkedActiveGaugeBFFirstVariationDensity_eq_zero
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : P286GaugeTwoForm)
    (generator : P286CoordinateCarrier) :
    p286LinkedActiveGaugeBFFirstVariationDensity coframe spacetimeHodge
        operator curvature auxiliary generator =
      0 := by
  have curvaturePairing :=
    generatedGaugeTwoFormMetricPairing_p286_adjoint_skew coframe generator
      auxiliary (liftGaugeTwoFormOperator spacetimeHodge curvature)
  have auxiliaryPairing :=
    generatedGaugeTwoFormMetricPairing_p286_adjoint_skew coframe generator
      auxiliary
        (liftGaugeTwoFormOperator spacetimeHodge
          (liftGaugeTwoFormOperator operator auxiliary))
  unfold p286LinkedActiveGaugeBFFirstVariationDensity
    p286GaugeBFCurvatureIncrementDensity
    p286CoordinateGaugeAuxiliaryFirstVariationDensity
  rw [liftGaugeTwoFormOperator_p286GaugeTwoFormAdjoint,
    liftGaugeTwoFormOperator_p286GaugeTwoFormAdjoint,
    liftGaugeTwoFormOperator_p286GaugeTwoFormAdjoint]
  linarith

/-! ## Faithful consumption of the linked primitive path -/

/-- The gauge--BF first coefficient read from the actual linked primitive
tangent at one spacetime point. -/
def holonomicP286LinkedActiveGaugeBFFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : ℝ :=
  let field := toContinuumPointField configuration point
  let tangent :=
    representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter
  generatedVolumeDensity field *
    (p286GaugeBFCurvatureIncrementDensity field.coframe
        (coframeGaugeSpacetimeHodgeLinear field.coframe)
        (p286AuxiliaryCoordinate field)
        (p286GaugeConnectionLinearCurvatureVariation configuration
          (fun current => (tangent current).connection) point) +
      p286CoordinateGaugeAuxiliaryFirstVariationDensity field.coframe
        (coframeGaugeSpacetimeHodgeLinear field.coframe)
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear field.coframe)
        (p286CurvatureCoordinate field)
        (p286AuxiliaryCoordinate field)
        (tangent point).auxiliary)

theorem holonomicP286LinkedActiveGaugeBFFirstVariationDensity_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    holonomicP286LinkedActiveGaugeBFFirstVariationDensity source
        configuration gaugeParameter point =
      0 := by
  have curvatureVariation :
      p286GaugeConnectionLinearCurvatureVariation configuration
          (fun current =>
            (representationDerivedP286CoupledGaugeTangentSection configuration
              gaugeParameter current).connection)
          point =
        p286GaugeTwoFormAdjoint (gaugeParameter point)
          (holonomicP286GaugeCurvatureCoordinate configuration point) := by
    have variationEquality :
        (fun current =>
          (representationDerivedP286CoupledGaugeTangentSection configuration
            gaugeParameter current).connection) =
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter).toFun := by
      funext current direction
      rfl
    rw [variationEquality]
    funext pair
    simpa only [
      p286GaugeTwoFormAdjoint,
      p286CoordinateLieBracket_eq_coordinateBracket] using
      p286InfinitesimalGaugeCurvatureVariation_eq_adjoint configuration
        smooth gaugeParameter point pair
  have auxiliaryVariation :
      (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).auxiliary =
        p286GaugeTwoFormAdjoint (gaugeParameter point)
          (holonomicP286GaugeAuxiliaryCoordinate configuration point) := by
    rfl
  unfold holonomicP286LinkedActiveGaugeBFFirstVariationDensity
  dsimp only
  rw [curvatureVariation, auxiliaryVariation]
  change generatedVolumeDensity (toContinuumPointField configuration point) *
    p286LinkedActiveGaugeBFFirstVariationDensity
      (toContinuumPointField configuration point).coframe
      (coframeGaugeSpacetimeHodgeLinear
        (toContinuumPointField configuration point).coframe)
      (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
        coframeGaugeSpacetimeHodgeLinear
          (toContinuumPointField configuration point).coframe)
      (p286CurvatureCoordinate (toContinuumPointField configuration point))
      (p286AuxiliaryCoordinate (toContinuumPointField configuration point))
      (gaugeParameter point) = 0
  rw [p286LinkedActiveGaugeBFFirstVariationDensity_eq_zero, mul_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveGaugeBFAlgebra
