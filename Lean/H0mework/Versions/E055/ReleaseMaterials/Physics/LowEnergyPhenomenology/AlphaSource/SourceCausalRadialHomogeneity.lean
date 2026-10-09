import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalMasterDerivative

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCausalSpatialDilation
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
local instance CausalMasterIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalCommonObservableUnits PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumObservedPoleTensor
open PreparationVacuumActualSpatialPacket
open scoped Matrix.Norms.Operator SchwartzMap

open PreparationPhysicalCommonSpatialGreen PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn

open Set GaussianFourier


open PreparationPhysicalChannelGreen


open PreparationPhysicalChannelRadialJet PreparationVacuumObservedStaticResidue


open GaussCoreHilbert SourceJointResidualEnergy PreparationVacuumQuantumSlowResponse
open PreparationPhysicalJointRadialForcing

open PreparationVacuumPhysicalHalfAxis CanonicalGradedCurrent GaussUnitaryHistory
open PreparationPhysicalRetainerResolventSquare PreparationVacuumStaticSpatialSource
attribute [local irreducible] sourcePinnedResolvent sourcePoleRead sourceRetainerSeed sourceEqualProjection
  sourceFullInitialBase sourceFullCurrentResidue sourceOriginCurrentResidue sourceActualNativeResidue
  sourceNativeReaderFirst sourceMasterCurrent sourceMasterNative sourceMasterNativeDerivative

private theorem scaled_positive (s : ℝ) (positive : 0<s) (zeta : ℂ) (causal : 0<zeta.re) :
    0<((s:ℂ)*zeta).re := by
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positive causal

private theorem fixedMomentum_radial (n : PhysicalMomentum) (zeta : ℂ) (s : ℝ) :
    fixedMomentum (s • n) ((s:ℂ)*zeta)=(s:ℂ) • fixedMomentum n zeta := by
  ext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [fixedMomentum,fullMomentum]
  · simp [fixedMomentum,fullMomentum,PreparationVacuumPhysicalFeedback.physicalSpatial]
    ring

/-- The actual full289 current carries degree minus two under the original simultaneous physical radial scale. -/
theorem sourceCompleteCurrent_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceFullCurrentResidue q (s • n) ((s:ℂ)*zeta) l r=
      ((s:ℂ)⁻¹)^2 • sourceFullCurrentResidue q n zeta l r := by
  funext i
  simp only [Pi.smul_apply]
  rw [sourceFullCurrentResidue_square q (s • n) _ (scaled_positive s positive zeta causal),
    sourceFullCurrentResidue_square q n zeta causal,
    sourcePinnedResolvent_radial q.F n s positive zeta causal]
  simp only [pow_two,smul_mul_assoc,mul_smul_comm,smul_smul,map_smul,smul_eq_mul]
  ring

/-- Both actual gauge slots scale with the same pinned inverse, without a static substitution. -/
theorem sourceCompleteGauge_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    sourceGaugeCurrentResidue q (s • n) ((s:ℂ)*zeta) l r mu a=
      (s:ℂ)⁻¹*sourceGaugeCurrentResidue q n zeta l r mu a := by
  simp only [sourceGaugeCurrentResidue,sourceGaugeResidue,(paidSpatial% projected_origin),
    sourcePinnedResolvent_radial q.F n s positive zeta causal,smul_mul_assoc,map_smul,smul_eq_mul]
  ring

private theorem originPair_smul (z w : ℂ) : sourceOriginPair (z*w)=z • sourceOriginPair w := by
  funext i
  simp only [sourceOriginPair,Pi.smul_apply,Pi.add_apply,Pi.single_apply,smul_eq_mul]
  split_ifs <;> ring

theorem sourceCompleteOrigin_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceOriginCurrentResidue q (s • n) ((s:ℂ)*zeta) l r=
      (s:ℂ)⁻¹ • sourceOriginCurrentResidue q n zeta l r := by
  simp only [sourceOriginCurrentResidue,sourceCompleteGauge_radial q n zeta causal s positive]
  rw [←originPair_smul]
  congr 1
  ring

/-- Native forcing homogeneity includes the actual gauge term and the complete time/spatial reader. -/
theorem sourceCompleteNative_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceActualNativeResidue q (s • n) ((s:ℂ)*zeta) l r=
      (s:ℂ)⁻¹ • sourceActualNativeResidue q n zeta l r := by
  have nonzero:=Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [sourceActualNativeResidue,sourceCompleteOrigin_radial q n zeta causal s positive,
    fixedMomentum_radial,sourceReaderFirst_radial,sourceCompleteCurrent_radial q n zeta causal s positive,
    Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,smul_add]
  have factor : ((s:ℂ)⁻¹)^2*(s:ℂ)=(s:ℂ)⁻¹ := by field_simp
  rw [factor]

private theorem slow_smul (z : ℂ) (v : Fin 289→ℂ) (i : Fin 5) :
    sourceSlowRead (z • v) i=z*sourceSlowRead v i := by
  simp only [sourceSlowRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> simp only [mul_zero]

theorem sourceCompleteDenominator_radial (n : PhysicalMomentum) (zeta : ℂ) (s : ℝ) (i : Fin 3) :
    sourceChargedDenominator (s • n) ((s:ℂ)*zeta) i=(s:ℂ)^2*sourceChargedDenominator n zeta i := by
  simp only [sourceChargedDenominator,sourceSpatialSquare_radial,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

/-- All three original causal channels have degree minus three; the moving channel0 is included. -/
theorem sourceCompleteChannel_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3) :
    sourceCommonCausalChannel q (s • n) ((s:ℂ)*zeta) l r i=
      ((s:ℂ)⁻¹)^3*sourceCommonCausalChannel q n zeta l r i := by
  simp only [sourceCommonCausalChannel,sourceCompleteDenominator_radial,
    sourceCompleteNative_radial q n zeta causal s positive,slow_smul,mul_inv_rev,inv_pow]
  ring

theorem sourceMasterCurrent_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceMasterCurrent q (s • n) ((s:ℂ)*zeta) l r=
      (s:ℂ)⁻¹ • sourceMasterCurrent q n zeta l r := by
  funext i
  simp only [sourceMasterCurrent,sourcePinnedResolvent_radial q.F n s positive zeta causal,
    smul_mul_assoc,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem sourceMasterNative_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceMasterNative q (s • n) ((s:ℂ)*zeta) l r=sourceMasterNative q n zeta l r := by
  have nonzero:=Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [sourceMasterNative,fixedMomentum_radial,sourceReaderFirst_radial,
    sourceMasterCurrent_radial q n zeta causal s positive,Matrix.smul_mulVec,Matrix.mulVec_smul,
    smul_smul,inv_mul_cancel₀ nonzero,one_smul]

theorem sourceMasterNativeDerivative_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceMasterNativeDerivative q (s • n) ((s:ℂ)*zeta) l r=
      (s:ℂ)⁻¹ • sourceMasterNativeDerivative q n zeta l r := by
  have nonzero:=Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [sourceMasterNativeDerivative,fixedMomentum_radial,sourceReaderFirst_radial,
    sourceMasterCurrent_radial q n zeta causal s positive,sourceCompleteCurrent_radial q n zeta causal s positive,
    Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,smul_add]
  have factor : ((s:ℂ)⁻¹)^2*(s:ℂ)=(s:ℂ)⁻¹ := by field_simp
  rw [factor]

/-- The first-order master has degree minus two on the same source physical coordinates. -/
theorem sourceMasterChannel_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3) :
    sourceMasterChannel q (s • n) ((s:ℂ)*zeta) l r i=
      ((s:ℂ)⁻¹)^2*sourceMasterChannel q n zeta l r i := by
  simp only [sourceMasterChannel,sourceCompleteDenominator_radial,
    sourceMasterNative_radial q n zeta causal s positive,mul_inv_rev,inv_pow]
  ring

theorem sourceMasterChannelDerivative_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3) :
    sourceMasterChannelDerivative q (s • n) ((s:ℂ)*zeta) l r i=
      ((s:ℂ)⁻¹)^3*sourceMasterChannelDerivative q n zeta l r i := by
  have nonzero:=Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [sourceMasterChannelDerivative,sourceCompleteDenominator_radial,
    sourceMasterNative_radial q n zeta causal s positive,
    sourceMasterNativeDerivative_radial q n zeta causal s positive,slow_smul,mul_inv_rev,inv_pow]
  field_simp

/-- The complete gauge, reader-time and denominator correction scales together, without deleting any summand. -/
theorem sourceMasterChannelCorrection_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3) :
    sourceMasterChannelCorrection q (s • n) ((s:ℂ)*zeta) l r i=
      ((s:ℂ)⁻¹)^3*sourceMasterChannelCorrection q n zeta l r i := by
  have complete:=sourceCommonCausalChannel_master q (s • n) ((s:ℂ)*zeta) l r i
  rw [sourceCompleteChannel_radial q n zeta causal s positive,
    sourceMasterChannelDerivative_radial q n zeta causal s positive,
    sourceCommonCausalChannel_master q n zeta,mul_add] at complete
  exact add_left_cancel complete.symm

end LowEnergy.PreparationPhysicalCausalSpatialDilation
