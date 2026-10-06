import H0mework.Versions.AB.Physics.MotherSource.StaticHamiltonian.TimeJets
import H0mework.Physics.DualVariation.ScalarVariation
import H0mework.Physics.DualVariation.MatterVariation
import H0mework.Physics.Lorentz.LorentzConnectionLocalVariation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 150000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeMotherAction StageNineFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation StageNineDiracDualFormNativeMatterVariation
open StageNineScalarVariation StageNineMatterVariation StageNineScalarLocalSpinDensity
open StageNineScalarPointwiseEquation StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine StageNineP286GaugeConnectionVariationDensity
open StageNineFormNativeGaugeWedge StageNineTopologicalGravityCurvatureVariancePairing
open StageNineTopologicalFourFormPairing StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeLorentzConnectionLocalVariation
open DiracExteriorMatterAction StageNineCoframeLocalDifferentiability
noncomputable section

def timeQuadratic (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration) (point : BasePoint) : ℝ :=
  scalarSecondVariationDensity source point (toContinuumPointField background point) 0
    (temporalScalarVelocity background point)

private theorem matter_time_coefficient (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    diracDualMatterFirstVariationDensity source point (toContinuumPointField background point) 0
      (temporalMatterVelocity background point) =
    matterDifferentialMomentum source background
      (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv (background.matter candidate)) point 0) 0 point := by
  simp [diracDualMatterFirstVariationDensity, diracDualMatterFieldVariationVector,
    temporalMatterVelocity, matterDifferentialMomentum, matterDifferentialVariationVector,
    matterCovariantDerivativeVariationVector, matterCovariantDerivativeKineticSum,
    matterDerivativeFrameRelative_zeroChart, Fin.sum_univ_four, toContinuumPointField]

private theorem gravity_time_polynomial (background : StageNineHolonomicConfiguration) (point : BasePoint) (rate : ℝ) :
    generatedFormNativeGravityBFDensity (timeJets background point rate) =
    generatedFormNativeGravityBFDensity (toContinuumPointField background point) +
      rate*gravityTopologicalBFCoefficient (background.gravityAuxiliary point) (gravityVelocityCurvature background point) := by
  have result := generatedFormNativeGravityBFDensity_withLorentzConnectionJets_quadratic
    (toContinuumPointField background point) (gravityVelocityCurvature background point) 0 rate
    (holonomicMatterCovariantDerivative background point)
  have zero : gravityTopologicalBFCoefficient (background.gravityAuxiliary point) 0 = 0 := by
    simp [gravityTopologicalBFCoefficient, gravityTopologicalWedgeCoefficient]
  change _ = _ + rate*_ + rate^2*gravityTopologicalBFCoefficient (background.gravityAuxiliary point) 0 at result
  simp only [smul_zero, add_zero, zero, mul_zero] at result
  exact result

private theorem gauge_time_polynomial (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) (rate : ℝ) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source) (timeJets background point rate) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source) (toContinuumPointField background point) +
      rate*formNativeP286GaugeWedgeCoefficient (background.gaugeAuxiliary point) (gaugeVelocityCurvature background point) := by
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286, generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  simp only [timeJets, toContinuumPointField]
  rw [formNativeP286GaugeWedgeCoefficient_add_right, formNativeP286GaugeWedgeCoefficient_smul_right]
  ring

private theorem matter_time_polynomial (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) (rate : ℝ) :
    generatedDensitizedContinuumDiracDualMatterDensity source 0 point (timeJets background point rate) =
    generatedDensitizedContinuumDiracDualMatterDensity source 0 point (toContinuumPointField background point) +
      rate*matterDifferentialMomentum source background
        (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv (background.matter candidate)) point 0) 0 point := by
  have result := generatedDensitizedContinuumDiracDualMatterDensity_withMatterJets_affine source point
    (toContinuumPointField background point) 0 (temporalMatterVelocity background point) rate
  have zeroMatter : rate • (0 : DiracExteriorMatterCarrier) = 0 := by
    change (rate : ℂ) • (0 : DiracExteriorMatterCarrier) = 0
    exact smul_zero _
  simp only [zeroMatter, add_zero, matter_time_coefficient] at result
  exact result

private theorem scalar_time_polynomial (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) (rate : ℝ) :
    generatedDensitizedContinuumScalarDensity source 0 point (timeJets background point rate) =
    generatedDensitizedContinuumScalarDensity source 0 point (toContinuumPointField background point) +
      rate*scalarDifferentialMomentum source background (fieldDirectionalDerivative background.scalar point 0) 0 point +
      rate^2*timeQuadratic source background point := by
  have kinetic := generatedScalarKineticDensity_withScalarJets_quadratic source point
    (toContinuumPointField background point) 0 (temporalScalarVelocity background point) rate
  simp only [smul_zero, add_zero] at kinetic
  unfold generatedDensitizedContinuumScalarDensity
  have actual : generatedScalarKineticDensity source 0 point (timeJets background point rate) =
      generatedScalarKineticDensity source 0 point
        (withScalarJets (toContinuumPointField background point) (toContinuumPointField background point).scalar
          ((toContinuumPointField background point).scalarCovariantDerivative + rate • temporalScalarVelocity background point)) := rfl
  rw [actual, kinetic]
  simp only [timeJets, toContinuumPointField, generatedVolumeDensity]
  unfold timeQuadratic scalarSecondVariationDensity scalarDifferentialMomentum temporalScalarVelocity
  simp only [scalarCoordinateSquaredNorm_zero, sub_zero, generatedVolumeDensity, toContinuumPointField]
  ring

theorem original_time_polynomial (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (point : BasePoint) (rate : ℝ) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point (timeJets background point rate) =
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point (toContinuumPointField background point) +
      rate*ordinaryTimePairing source background point + rate^2*timeQuadratic source background point := by
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary generatedDiracDualFormNativeMatterDensity
  rw [gravity_time_polynomial, gauge_time_polynomial, matter_time_polynomial, scalar_time_polynomial]
  have constraint : generatedFormNativeGravityConstraintDensity (timeJets background point rate) =
      generatedFormNativeGravityConstraintDensity (toContinuumPointField background point) := rfl
  rw [constraint]
  unfold ordinaryTimePairing
  ring

/-- All four canonical time-velocity terms are generated by one actual nine-field time perturbation of the complete repaired action. -/
theorem source_time_legendre (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) :
    HasDerivAt (fun rate : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
      (toContinuumPointField (timeStretch background point rate) point))
      (ordinaryTimePairing source background point) 0 := by
  simp_rw [source_time_jets background smooth, original_time_polynomial]
  convert (((hasDerivAt_id (0 : ℝ)).mul_const (ordinaryTimePairing source background point)).const_add
    (sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point (toContinuumPointField background point))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (timeQuadratic source background point)) using 1 <;> try rfl
  simp

theorem hamiltonian_source_derivative (source : SmoothUnifiedSource) (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) :
    hamiltonianDensity source background point =
      deriv (fun rate : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField (timeStretch background point rate) point)) 0 -
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point (toContinuumPointField background point) := by
  rw [(source_time_legendre source background smooth point).deriv]
  rfl

/-- The same generated derivative is consumed at the actual complete-U runtime occurrence. -/
theorem original_time_legendre (point : BasePoint) :
    HasDerivAt (fun rate : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (timeStretch Stage10.Runtime.configuration point rate) point))
      (ordinaryTimePairing Stage10.Runtime.source Stage10.Runtime.configuration point) 0 := by
  rw [Stage10.Runtime.source_eq, Stage10.Runtime.configuration_eq]
  exact source_time_legendre _ _ Stage9C.Material.SpinPair.actual_smooth point

end
end SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
