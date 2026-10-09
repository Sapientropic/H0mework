import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageGreenSolution
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageGaussEnergyRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumVoltageGaussGreen
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal DiracExteriorMatterAction Stage9C.Material.SpinPair Stage10
open PreparationPhysicalVoltageNoether PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumSourceFieldFamily PreparationVacuumPhysicalFeedback
open GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumStaticVoltageSource SourcePropagationMotherEulerKernel
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb UnifiedAction
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap

open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open SU7MotherLieAlgebra

/-- Spatial source legs enter the original Cauchy family through the same fixed scale-one coordinates. -/
theorem sourceVoltage_raw_originalGauss (profile : BasePoint→ℝ)
    (regular : CanonicalGauss.ScalarRegular profile)
    (matter : Point→DiracExteriorMatterCarrier) (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : Point) :
    p286CoordinateLiePairing (p286CoordinateEquiv HyperchargeResponse.chargeDirection)
      (holonomicFormNativeP286GaugeEulerThreeForm Runtime.source 0
        (CanonicalGauss.withMatter (CanonicalGauss.abelianPotential profile)
          (fun x=>matter (spatialPoint 1 x)) (fun x=>dual (spatialPoint 1 x)))
        (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) 3)=
      -(2*lapse)*CanonicalGauss.spatialLaplacian profile
        (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point))+sourceVoltageRawCharge matter dual point := by
  rw [CanonicalGauss.poisson_gauss _ regular,StaticGreen.slice_source_coordinates]
  rfl

abbrev sourceVoltageActualState : ActionState := sourceState sourcePoint.val

private theorem actual_nondegenerate : sourceVoltageActualState.1.det≠0 :=
  coframe_nondegenerate sourcePoint

private theorem actual_temporal : coframeTemporalPrincipalScalar sourceVoltageActualState.1≠0 :=
  temporal_noncharacteristic sourcePoint

/-- The voltage fed back into the original family is its generated Green solution at the original spatial scale. -/
def sourceVoltageGreenProfile (matter : Point→DiracExteriorMatterCarrier)
    (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) : ℝ :=
  StaticGreen.potential (sourceVoltageRawCharge matter dual) (spatialPoint 1 point)

/-- Actual normalized Noether energy on two independent original charged Gauss legs reads the same Green potential. -/
theorem sourceVoltage_green_energy (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (matter : Point→DiracExteriorMatterCarrier) (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : Point) (side edge other opposite : Fin 2) :
    sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState (sourceVoltageGreenProfile matter dual)
      (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) side edge other opposite=
      (StaticGreen.potential (sourceVoltageRawCharge matter dual) point:ℂ)*
        (if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0) := by
  rw [sourceVoltageActualEnergy_Cauchy epsilon precision p sourceVoltageActualState actual_nondegenerate actual_temporal]
  simp only [sourceVoltageGreenProfile,StaticGreen.slice_source_coordinates]

/-- This physical energy read solves the actual field-response weak equation; the two-leg Gram factor is generated. -/
theorem sourceVoltage_energy_weak_gauss (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (matter : Point→DiracExteriorMatterCarrier) (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier)
    (integrable : Integrable (sourceVoltageRawCharge matter dual)) (test : 𝓢(Point, ℝ))
    (side edge other opposite : Fin 2) :
    (∫ point : Point,(sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState (sourceVoltageGreenProfile matter dual)
      (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) side edge other opposite).re*
        sourceVoltageTestResponse test point)+
      (∫ point : Point,sourceVoltageRawCharge matter dual point*test point)*
        (if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0)=0 := by
  simp only [sourceVoltage_green_energy epsilon precision p]
  split_ifs
  · simpa using sourceVoltage_raw_potential matter dual integrable test
  · simp

/-- The source-normalized energy retains the complete source denominator, once. -/
theorem sourceVoltage_energy_kernel (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (matter : Point→DiracExteriorMatterCarrier) (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : Point) (side edge : Fin 2) :
    (sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState (sourceVoltageGreenProfile matter dual)
      (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) side edge side edge).re=
      -(∫ sourcePoint : Point,sourceVoltageRawCharge matter dual sourcePoint*
        kernel (point-sourcePoint)/(8*Real.pi*lapse)) := by
  rw [sourceVoltage_green_energy epsilon precision p]
  simp only [ite_true,mul_one,Complex.ofReal_re]
  exact sourceVoltage_potential_kernel matter dual point

/-- Independent source currents pair through the same measured energy and the same complete Green kernel. -/
theorem sourceVoltage_pair_energy (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (matterA matterB : Point→DiracExteriorMatterCarrier)
    (dualA dualB : Point→Module.Dual ℂ DiracExteriorMatterCarrier)
    (integrableA : Integrable (sourceVoltageRawCharge matterA dualA))
    (integrableB : Integrable (sourceVoltageRawCharge matterB dualB))
    (bound : ℝ) (bounded : ∀ point,‖sourceVoltageRawCharge matterB dualB point‖≤bound)
    (side edge : Fin 2) :
    -(∫ point : Point,sourceVoltageRawCharge matterA dualA point*
      (sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState (sourceVoltageGreenProfile matterB dualB)
        (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) side edge side edge).re)=
      (∫ points : Point×Point,sourceVoltageRawCharge matterA dualA points.1*
        sourceVoltageRawCharge matterB dualB points.2*kernel (points.2-points.1))/(8*Real.pi*lapse) := by
  have joint:=StaticGreen.green_pair_integrable (sourceVoltageRawCharge matterA dualA)
    (sourceVoltageRawCharge matterB dualB) integrableA integrableB bound bounded
  simp only [sourceVoltage_green_energy epsilon precision p,
    ite_true,mul_one,Complex.ofReal_re]
  rw [←integral_div]
  have expression : (fun points : Point×Point=>sourceVoltageRawCharge matterA dualA points.1*
      sourceVoltageRawCharge matterB dualB points.2*kernel (points.2-points.1)/(8*Real.pi*lapse))=
      fun points=>sourceVoltageRawCharge matterA dualA points.1*
        sourceVoltageRawCharge matterB dualB points.2*StaticGreen.green (points.2-points.1) := by
    funext points
    rw [StaticGreen.green_kernel]
    ring
  rw [expression,Measure.volume_eq_prod,integral_prod _ (by simpa only [Measure.volume_eq_prod] using joint)]
  simp only [StaticGreen.potential,mul_neg,integral_neg,neg_neg]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with sourcePoint
  rw [StaticGreen.green_sub_comm]
  ring

end LowEnergy.PreparationVacuumVoltageGaussGreen
