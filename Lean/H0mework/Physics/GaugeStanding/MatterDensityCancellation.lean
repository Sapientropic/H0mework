import H0mework.Physics.Matter.ExteriorMotherLieYukawaDerivation
import H0mework.Physics.GaugeStanding.MatterCovariantJet
import H0mework.Physics.Matter.MatterVariation
import H0mework.Physics.Matter.ConjugateMatterVariation
import H0mework.Physics.Exterior.ScalarVariation

/-!
# S9-C: linked active P286 matter-density cancellation

The actual linked P286 matter and scalar responses generate the mother action
on the complete Dirac--Yukawa vector.  The source-owned conjugate-matter
response is the contragredient action, so the two legs cancel in the real
matter density at the same point and on the same configuration.

This is a pointwise active-symmetry identity.  It does not assume
stationarity, a field equation, a Ward receipt, a residual zero, or a target
vector.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveMatterDensityCancellation

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineConjugateMatterVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineExteriorMotherLieYukawaDerivation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveMatterCovariantJet
open StageNineP286LinkedActiveVariation
open StageNineScalarVariation
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- Abstract chart-zero representation identity used by the linked actual:
the matter-jet response plus the scalar Yukawa response is the mother action
on the complete Dirac--Yukawa vector. -/
theorem matterFieldVariationVector_add_scalarVariation_motherLieAction
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matrix : SU7MotherLieMatrix) :
    matterFieldVariationVector source point field
          (diracExteriorMotherLieAction matrix field.matter)
          (fun direction =>
            diracExteriorMotherLieAction matrix
              (field.matterCovariantDerivative direction)) +
        scalarYukawaVariationVector field
          (scalarMotherLieAction matrix field.scalar) =
      diracExteriorMotherLieAction matrix
        (generatedContinuumMatterVector source 0 point field) := by
  have spinCommutes (direction : LorentzianIndex) :
      diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := field.coframe, derivative := 0 } direction)
          (diracExteriorMotherLieAction matrix
            (field.matterCovariantDerivative direction)) =
        diracExteriorMotherLieAction matrix
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := field.coframe, derivative := 0 } direction)
            (field.matterCovariantDerivative direction)) := by
    exact LinearMap.congr_fun
      (diracMatrixMatterAction_commutes_internal
        (inverseCoframeDiracGamma
          { coframe := field.coframe, derivative := 0 } direction)
        (exteriorSpinorMotherLieAction matrix))
      (field.matterCovariantDerivative direction)
  have scalarAction :
      scalarCoordinateEquiv.symm
          (scalarMotherLieAction matrix field.scalar) =
        exteriorMotherLieAction 4 matrix
          (scalarCoordinateEquiv.symm field.scalar) := by
    simp [scalarMotherLieAction]
  unfold matterFieldVariationVector scalarYukawaVariationVector
    generatedContinuumMatterVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]
  rw [matterGaugeKineticSum_zeroChart]
  rw [scalarAction]
  simp_rw [spinCommutes]
  rw [add_assoc]
  rw [show
      chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm field.scalar)
            (diracExteriorMotherLieAction matrix field.matter) +
          chiralExteriorYukawaAction
            (exteriorMotherLieAction 4 matrix
              (scalarCoordinateEquiv.symm field.scalar))
            field.matter =
        diracExteriorMotherLieAction matrix
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm field.scalar) field.matter) by
      rw [add_comm, ← chiralExteriorYukawaAction_motherLieAction]]
  simp only [map_add, map_smul, map_sum]

/-- The complete actual first response of one matter covariant-jet component,
written from the primitive linked tangent. -/
def linkedActiveMatterCovariantJetResponse
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
        (fieldDirectionalDerivative
          (fun current =>
            matterCoordinateEquiv
              ((representationDerivedP286CoupledGaugeTangentSection
                configuration gaugeParameter current).matter))
          point direction) +
      diracMatrixMatterAction
        (diracSpinConnectionLift
          (configuration.gravityConnection point) direction)
        ((representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).matter) +
    diracExteriorMotherLieAction
        (p286LieBlockEmbed (configuration.gaugeConnection point direction))
        ((representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).matter) +
    diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            ((representationDerivedP286CoupledGaugeTangentSection
              configuration gaugeParameter point).connection direction)))
        (configuration.matter point)

theorem linkedActiveMatterCovariantJetResponse_eq_action
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    linkedActiveMatterCovariantJetResponse configuration gaugeParameter point
        direction =
      diracExteriorMotherLieAction
        (p286GaugeParameterMotherAt gaugeParameter point)
        (holonomicMatterCovariantDerivative configuration point direction) :=
  linkedActiveMatterCovariantJetVariation_eq_action configuration smooth
    gaugeParameter point direction

/-- Matter-vector response generated by the actual scalar, matter, and
covariant-jet legs of one linked parameter. -/
def linkedActiveMatterVectorFirstVariation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  let field := toContinuumPointField configuration point
  let tangent :=
    representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter
  matterFieldVariationVector source point field (tangent point).matter
      (linkedActiveMatterCovariantJetResponse configuration gaugeParameter
        point) +
    scalarYukawaVariationVector field (tangent point).scalar

/-- The source/action-generated linked matter-vector response is the actual
mother action on the pre-existing vector. -/
theorem linkedActiveMatterVectorFirstVariation_eq_action
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    linkedActiveMatterVectorFirstVariation source configuration
        gaugeParameter point =
      diracExteriorMotherLieAction
        (p286GaugeParameterMotherAt gaugeParameter point)
        (generatedContinuumMatterVector source 0 point
          (toContinuumPointField configuration point)) := by
  unfold linkedActiveMatterVectorFirstVariation
  dsimp only
  rw [show
      linkedActiveMatterCovariantJetResponse configuration gaugeParameter
          point =
        fun direction =>
          diracExteriorMotherLieAction
            (p286GaugeParameterMotherAt gaugeParameter point)
            ((toContinuumPointField configuration point).matterCovariantDerivative
              direction) by
      funext direction
      exact linkedActiveMatterCovariantJetResponse_eq_action configuration
        smooth gaugeParameter point direction]
  exact matterFieldVariationVector_add_scalarVariation_motherLieAction
    source point (toContinuumPointField configuration point)
      (p286GaugeParameterMotherAt gaugeParameter point)

/-- The two first-order legs of the chart-zero matter density: the linked
matter-vector response and the source-owned contragredient dual response. -/
def linkedActiveMatterDensityFirstVariation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : ℝ :=
  let field := toContinuumPointField configuration point
  let tangent :=
    representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter
  generatedVolumeDensity field *
    ((field.conjugateMatter
        (linkedActiveMatterVectorFirstVariation source configuration
          gaugeParameter point)).re +
      ((tangent point).conjugateMatter
        (generatedContinuumMatterVector source 0 point field)).re)

/-- Pointwise cancellation of the complete linked active matter-density
response.  Both terms are evaluated on the same source, configuration,
parameter, point, and matter vector. -/
theorem linkedActiveMatterDensityFirstVariation_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    linkedActiveMatterDensityFirstVariation source configuration
        gaugeParameter point =
      0 := by
  rw [linkedActiveMatterDensityFirstVariation]
  rw [linkedActiveMatterVectorFirstVariation_eq_action source configuration
    smooth gaugeParameter point]
  change
    generatedVolumeDensity (toContinuumPointField configuration point) *
      (((configuration.conjugateMatter point)
          (diracExteriorMotherLieAction
            (p286GaugeParameterMotherAt gaugeParameter point)
            (generatedContinuumMatterVector source 0 point
              (toContinuumPointField configuration point)))).re +
        ((-(configuration.conjugateMatter point).comp
            (diracExteriorMotherLieAction
              (p286GaugeParameterMotherAt gaugeParameter point)))
          (generatedContinuumMatterVector source 0 point
            (toContinuumPointField configuration point))).re) =
      0
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveMatterDensityCancellation
