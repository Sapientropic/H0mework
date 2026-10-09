import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonObservableChannels

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonObservableUnits
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance SourceCommonPhysicalUnitsIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

open PreparationVacuumStaticSpatialSource PreparationVacuumStaticSimpleCoupling

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalActualRetardedWard

/-- Physical wave number is read from the same epsilon-squared momentum used by the finite scattering response. -/
def sourceObservableWaveNumber (n : PhysicalMomentum) (e : scaleDomain) : ℝ :=
  Real.sqrt (spatialSquare (e.val^2 • n))

theorem sourceObservableWaveNumber_generated (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (e : scaleDomain) : sourceObservableWaveNumber n e=e.val^2 := by
  have square : spatialSquare (e.val^2 • n)=(e.val^2)^2*spatialSquare n := by
    simp only [spatialSquare,Pi.smul_apply,smul_eq_mul]
    ring
  rw [sourceObservableWaveNumber,square,unit,mul_one,Real.sqrt_sq (sq_nonneg e.val)]

def sourceObservablePhaseSpeed (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : ℝ :=
  sourceFrequency e.val (sourceSheet branch n unit e.val)/sourceObservableWaveNumber n e

theorem sourceObservablePhaseSpeed_generated (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) :
    sourceObservablePhaseSpeed branch n unit e=sourceSheet branch n unit e.val := by
  rw [sourceObservablePhaseSpeed,sourceObservableWaveNumber_generated n unit e,sourceFrequency]
  field_simp [e.property.1.ne']

theorem sourceObservablePhaseSpeed_limit (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    Tendsto (sourceObservablePhaseSpeed branch n unit) scaleApproach (𝓝 (sourceSpeed branch)) := by
  apply ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto).congr
  intro e
  exact (sourceObservablePhaseSpeed_generated branch n unit e).symm

/-- Phase momentum is the original source action response to its unit matter phase, not a chosen numerical unit. -/
theorem sourceObservableActionUnit (point : BasePoint) :
    Stage10.ActionNormalization.phaseMomentum=
      StageNineMatterPointwiseEquation.matterDifferentialMomentum Stage10.Runtime.source
        Stage10.CanonicalMatter.preparedConfiguration
        (StageNineHolonomicField.matterCoordinateEquiv
          ((-Complex.I) • Stage10.CanonicalMatter.preparedConfiguration.matter point)) 0 point := by
  rw [Stage10.ActionNormalization.phaseMomentum_source,
    Stage10.CanonicalMatter.prepared_action_time_momentum]

/-- The complete tensor is normalized by its source action phase and the visible propagation branch, before any angular scalar read. -/
def sourceObservableReducedTensor (branch : Fin 2) (q : PhysicalResponsePoint)
    (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ •
    sourceCommonCoulombTensor q n l r

def sourceObservableFiniteReducedTensor (branch : Fin 2) (q : PhysicalResponsePoint)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (l r : RestStateIndex)
    (e : scaleDomain) : Fin 289→ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceObservablePhaseSpeed branch n unit e:ℝ):ℂ)⁻¹ •
    sourceCommonCoulombTensor q n l r

/-- The same physical-frequency sheet generates the full directional normalization; no lapse or alternate cone is substituted. -/
theorem sourceObservableReducedTensor_generated (branch : Fin 2) (q : PhysicalResponsePoint)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (l r : RestStateIndex) :
    Tendsto (sourceObservableFiniteReducedTensor branch q n unit l r) scaleApproach
      (𝓝 (sourceObservableReducedTensor branch q n l r)) := by
  have speed:=(sourceObservablePhaseSpeed_limit branch n unit).const_mul Stage10.ActionNormalization.phaseMomentum
  have cast:=Complex.continuous_ofReal.continuousAt.tendsto.comp speed
  have nonzero : ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos Stage10.ActionNormalization.phaseMomentum_positive (sourceSpeed_positive branch)).ne'
  exact (cast.inv₀ nonzero).smul_const _

theorem sourceObservableReducedTensor_radial (branch : Fin 2) (q : PhysicalResponsePoint)
    (n : PhysicalMomentum) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceObservableReducedTensor branch q (s • n) l r=sourceObservableReducedTensor branch q n l r := by
  simp only [sourceObservableReducedTensor,sourceCommonCoulombTensor_radial q n s positive]

end LowEnergy.PreparationPhysicalCommonObservableUnits
