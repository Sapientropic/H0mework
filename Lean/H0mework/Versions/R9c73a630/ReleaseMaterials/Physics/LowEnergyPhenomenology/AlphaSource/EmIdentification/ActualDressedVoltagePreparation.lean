import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedVoltagePhase

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedVoltagePreparation
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

private theorem creation_scalar_affine (phi delta : Scalar) (scale : ℝ) :
    fiberCreation 1 0 (phi+scale • delta)=fiberCreation 1 0 phi+scale • fiberCreation 1 0 delta := by
  have coefficient (c : Fin 3) : star (scalarCoefficient 1 c (phi+scale • delta))=
      star (scalarCoefficient 1 c phi)+(scale:ℂ)*star (scalarCoefficient 1 c delta) := by
    have linear:=((scalarCoefficient 1 c).restrictScalars ℝ).map_smul scale delta
    change scalarCoefficient 1 c (scale • delta)=scale • scalarCoefficient 1 c delta at linear
    rw [map_add,linear]
    simp [Complex.real_smul]
  unfold fiberCreation
  simp only [coefficient]
  rw [Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  change (star (scalarCoefficient 1 c phi)+(scale:ℂ)*star (scalarCoefficient 1 c delta)) •
    GaussCARHistory.createFiber (mode 0 c)=
      star (scalarCoefficient 1 c phi) • GaussCARHistory.createFiber (mode 0 c)+
        (scale:ℂ) • (star (scalarCoefficient 1 c delta) • GaussCARHistory.createFiber (mode 0 c))
  module

/-- The original fixed creation letter differentiates along the actual voltage scalar Cauchy direction. -/
theorem voltage_creation_scalar_derivative (phi : Scalar) (slope : ℝ) :
    HasDerivAt (fun scale : ℝ=>fiberCreation 1 0
      (phi+scale • (slope • scalarCharge HyperchargeResponse.chargeDirection)))
      (fiberCreation 1 0 (slope • scalarCharge HyperchargeResponse.chargeDirection)) 0 := by
  have paid:=((hasDerivAt_id (0:ℝ)).smul_const
    (fiberCreation 1 0 (slope • scalarCharge HyperchargeResponse.chargeDirection))).const_add (fiberCreation 1 0 phi)
  simpa only [creation_scalar_affine,one_smul,id_eq] using paid

/-- Original bounded half-density CAR creation transports the unchanged prepared profile along the voltage scalar tangent. -/
def voltageScalarPreparation (slope : ℝ) : Profile→L[ℂ]H :=
  ∑c : Fin 3,star (scalarCoefficient 1 c (slope • scalarCharge HyperchargeResponse.chargeDirection)) •
    (GaussCARHistory.create (mode 0 c)).comp prepared

theorem voltage_scalar_preparation_original (slope : ℝ) (profile : Profile) :
    voltageScalarPreparation slope profile=
      ∑c : Fin 3,star (scalarCoefficient 1 c (slope • scalarCharge HyperchargeResponse.chargeDirection)) •
        GaussCARHistory.create (mode 0 c) (prepared profile) := by
  simp only [voltageScalarPreparation,sum_apply,smul_apply,
    ContinuousLinearMap.comp_apply]

/-- The same actual norm is used for the scalar variation and the already generated creation state. -/
def dressedVoltageScalarInput (event : DressedEvent) (slope : ℝ) : H :=
  ((‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*
    PhysicalEMDressedCharacter.emDressedCharacter true) •
      voltageScalarPreparation slope (sourceProfile event.epsilon event.precision)

/-- The original quantum scalar orbit, input profile and completed preparation are retained against the actual voltage tangent. -/
def dressedVoltageJointResidual (event : DressedEvent) (slope : ℝ) : H :=
  dressedJointInput event.epsilon event.precision-Complex.I • dressedVoltageScalarInput event slope

theorem dressed_voltage_joint_preparation_return (event : DressedEvent) (slope : ℝ) :
    chargeReader sourcePhaseGaugeLie (sourceDressedUnit event.epsilon event.precision)-
        Complex.I • dressedVoltageScalarInput event slope=
      (1/2:ℂ) • sourceDressedUnit event.epsilon event.precision+dressedVoltageJointResidual event slope := by
  rw [dressed_joint_unit_return,dressedVoltageJointResidual]
  abel

/-- This actual scalar/input return propagates through the same full inverse and its original cutoff. -/
theorem dressed_voltage_scalar_response (event : DressedEvent) (slope : ℝ) :
    (CanonicalPhysicalSpatial.compression event.momentum event.frame+
      FullYSourceCutoffVolterra.cutoff event.cut-event.energy • 1)
      (finiteFull event.momentum event.frame event.cut event.energy (dressedVoltageScalarInput event slope))=
      dressedVoltageScalarInput event slope := by
  exact congrArg (fun A : H→L[ℂ]H=>A (dressedVoltageScalarInput event slope))
    (finiteFull_right event.momentum event.frame event.cut event.energy event.nonreal)

end LowEnergy.GaussComposite.ActualDressedVoltagePreparation
