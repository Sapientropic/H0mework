import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedVoltagePreparation

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedVoltageCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 Stage10.TemporalGauge CanonicalGradedSpatialSource SourceQuantumScalarChart
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussComposite GaussComposite.SourceGraph
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent CanonicalGradedCharge
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldConstraintResponse
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalVoltageNoether PreparationVacuumStaticVoltageSource PreparationPhysicalPhaseGaugeRealization
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard
open ActualDressedActionPhase ActualDressedFullCoulomb ActualDressedVoltagePhase
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse
  dressedJointInput chargeReader

open PreparationVacuumMixedFieldReturn PreparationVacuumFullFieldRiesz PreparationVacuumFieldCovector
open StageNineCanonicalCauchyState StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open ActualDressedVoltagePreparation

/-- The same original profile and unit factor transport its creation letter; the factor is not chosen anew. -/
def dressedVoltageFamily (event : DressedEvent) (slope scale : ℝ) : H :=
  ((‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*
    PhysicalEMDressedCharacter.emDressedCharacter true) •
      (completedLeg true 1 0 (sourceProfile event.epsilon event.precision)+
        scale • voltageScalarPreparation slope (sourceProfile event.epsilon event.precision))

theorem dressed_voltage_family_same (event : DressedEvent) (slope : ℝ) :
    dressedVoltageFamily event slope 0=sourceDressedUnit event.epsilon event.precision := by
  rw [dressedVoltageFamily,zero_smul,add_zero,source_dressed_unit_original,sourceDressedAddition]

private theorem scaled_affine_first {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] (a : ℂ) (x y : V) :
    HasDerivAt (fun t : ℝ=>a • (x+t • y)) (a • y) 0 := by
  have paid:=(((hasDerivAt_id (0:ℝ)).smul_const y).const_add x).const_smul a
  have normalized : HasDerivAt (a • (fun t : ℝ=>x+t • y)) (a • y) 0 := by
    simpa only [one_smul,id_eq] using paid
  exact normalized.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t=>rfl)

/-- The actual source normalizer is held and its complete scalar tangent is generated. -/
theorem dressed_voltage_family_derivative (event : DressedEvent) (slope : ℝ) :
    HasDerivAt (dressedVoltageFamily event slope) (dressedVoltageScalarInput event slope) 0 := by
  exact scaled_affine_first _ _ _

private theorem pair_first {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (f : ℝ→V) (df : V) (T : V→L[ℂ]V) (first : HasDerivAt f df 0) :
    HasDerivAt (fun t : ℝ=>inner ℂ (f t) (T (f t)))
      (inner ℂ (f 0) (T df)+inner ℂ df (T (f 0))) 0 :=
  first.inner ℂ ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 first)

attribute [local irreducible] dressedVoltageFamily dressedVoltageScalarInput currentVertex

/-- Every full289 current slot receives both true external scalar-preparation derivatives; its original background is fixed. -/
theorem dressed_voltage_connected_current_derivative (event : DressedEvent) (slope : ℝ)
    (transfer : PhysicalMomentum) (i : Fin 289) :
    HasDerivAt (fun scale : ℝ=>
      inner ℂ (dressedVoltageFamily event slope scale)
        (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (dressedVoltageFamily event slope scale))-
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (prepared (sourceProfile event.epsilon event.precision))))
      (inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (dressedVoltageScalarInput event slope))+
       inner ℂ (dressedVoltageScalarInput event slope)
        (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (sourceDressedUnit event.epsilon event.precision))) 0 := by
  have paid:=(pair_first (dressedVoltageFamily event slope) (dressedVoltageScalarInput event slope)
    (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy)
    (dressed_voltage_family_derivative event slope)).sub_const
      (inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (prepared (sourceProfile event.epsilon event.precision))))
  simpa only [dressed_voltage_family_same] using paid

/-- The scalar preparation tangent propagates at the same original frequency, frame and cutoff. -/
theorem dressed_voltage_response_derivative (event : DressedEvent) (slope : ℝ) :
    HasDerivAt (fun scale : ℝ=>finiteFull event.momentum event.frame event.cut event.energy
      (dressedVoltageFamily event slope scale))
      (finiteFull event.momentum event.frame event.cut event.energy (dressedVoltageScalarInput event slope)) 0 :=
  ((finiteFull event.momentum event.frame event.cut event.energy).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 (dressed_voltage_family_derivative event slope)

/-- The original Gauss Cauchy scalar time jet generates the actual creation-letter tangent. -/
theorem original_cauchy_creation_derivative (phi : Scalar) (potential : BasePoint→ℝ)
    (space : StageNineSpatialPoint) :
    HasDerivAt (fun scale : ℝ=>fiberCreation 1 0 (phi+scale •
      scalarNormalConstraintRawVelocity (TemporalGauge.configuration (CanonicalGauss.abelianPotential potential)) space))
      (fiberCreation 1 0
        (-(potential (canonicalCauchySlicePoint 0 space)) • scalarCharge HyperchargeResponse.chargeDirection)) 0 := by
  rw [sourceVoltage_scalar_temporal]
  exact voltage_creation_scalar_derivative phi _

end LowEnergy.GaussComposite.ActualDressedVoltageCurrent
