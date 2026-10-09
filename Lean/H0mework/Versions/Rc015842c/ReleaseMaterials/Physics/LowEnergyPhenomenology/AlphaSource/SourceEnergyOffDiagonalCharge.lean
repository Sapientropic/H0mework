import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGradedExchangePotential

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMaterialSpectralCharge
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
local instance MaterialExchangeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalCausalSpatialDilation
open PreparationPhysicalMasterCorrectionReturn PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalGaugeSeedNull PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open PreparationPhysicalActionSeedReduction PreparationVacuumLowerClassical PreparationVacuumJointFieldResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussCoreDifferential GaussCoreLabel NativeHistoryGrade GaussFockLabel GaussYukawaGrade
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalGradeZeroRead
open PreparationPhysicalLorentzSeedReturn
open PreparationVacuumYukawaTransport

open PreparationPhysicalTriangularSeedReturn PreparationVacuumPhysicalModeContact
open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumNativeLocalWard
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart


open PreparationPhysicalOriginConfigurationReturn PreparationVacuumRestModeCoupling
open PreparationPhysicalActionUnits

open PreparationPhysicalCoframeOriginPolynomial
open Stage9DEF Stage9DEF.Compatibility Stage10.ChargedPreparation.Dynamics
open GaussQuantumMultiplier GaussFockLift CanonicalGradedCharge

open PreparationPhysicalCoframePreparedReturn PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativePhaseChargeInventory PreparationVacuumPhysicalGaussMaterialContact
open PreparationVacuumNativeFieldInjection
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualLegNormalization
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePoleRead sourceProjection jointResolvent sourceEqualProjection
  sourceResonanceProjection frameVector frameTest finiteRiesz


open PreparationVacuumFieldConstraintResponse
open PreparationPhysicalCoframeChargeSelection GaussFockPair
open scoped ContDiff
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional


open PreparationPhysicalCoframeChargeExchange PreparationVacuumPhysicalGaussColorTorque
open GaussDiagonalHistory GaussCoframeSpin GaussLiveMomentum

open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial CanonicalPhysicalWardCore

open PreparationPhysicalMaterialChargeTorque

/-- The actual zero-momentum material compression torque, prior to the independently retained full-Y term. -/
def sourceC0ChargeTorque (F : GaussUnitaryHistory.Index) : SourceOp :=
  actualC 0 F*sourceActualGaussCharge-sourceActualGaussCharge*actualC 0 F

theorem sourceC0ChargeTorque_entry (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    sourceChannelOp F i*sourceC0ChargeTorque F*sourceChannelOp F j=
      ((channelValue F i-channelValue F j:ℝ):ℂ) •
        (sourceChannelOp F i*sourceActualGaussCharge*sourceChannelOp F j) := by
  unfold sourceC0ChargeTorque
  calc
    _=(sourceChannelOp F i*actualC 0 F)*sourceActualGaussCharge*sourceChannelOp F j-
        sourceChannelOp F i*sourceActualGaussCharge*(actualC 0 F*sourceChannelOp F j) := by
      simp only [mul_sub,sub_mul,mul_assoc]
    _=_ := by
      rw [sourceChannelOp_right,sourceChannelOp_left]
      simp only [smul_mul_assoc,mul_smul_comm,Complex.ofReal_sub]
      exact (sub_smul (channelValue F i:ℂ) (channelValue F j:ℂ)
        (sourceChannelOp F i*sourceActualGaussCharge*sourceChannelOp F j)).symm

/-- Only unequal actual source energies enter the inverse coefficient; the entire degenerate block is retained by Eq. -/
def sourceChargeOffEnergy (F : GaussUnitaryHistory.Index) : SourceOp :=
  ∑i : Channel F,∑j : Channel F,if channelValue F i=channelValue F j then 0 else
    (((channelValue F i-channelValue F j:ℝ):ℂ)⁻¹) •
      (sourceChannelOp F i*sourceC0ChargeTorque F*sourceChannelOp F j)

private theorem energy_term (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (different : channelValue F i≠channelValue F j) :
    (((channelValue F i-channelValue F j:ℝ):ℂ)⁻¹) •
      (sourceChannelOp F i*sourceC0ChargeTorque F*sourceChannelOp F j)=
      sourceChannelOp F i*sourceActualGaussCharge*sourceChannelOp F j := by
  rw [sourceC0ChargeTorque_entry,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr different)),one_smul]

/-- The full equal-energy and unequal-energy pieces reconstruct the original actual Q, including escape. -/
theorem sourceChargeEnergy_resolution (F : GaussUnitaryHistory.Index) :
    sourceEqualProjection F sourceActualGaussCharge+sourceChargeOffEnergy F=sourceActualGaussCharge := by
  classical
  have all : (∑i : Channel F,∑j : Channel F,
      sourceChannelOp F i*sourceActualGaussCharge*sourceChannelOp F j)=sourceActualGaussCharge := by
    calc
      _=(∑i : Channel F,sourceChannelOp F i)*sourceActualGaussCharge*(∑j : Channel F,sourceChannelOp F j) := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
      _=_ := by rw [sourceChannelOp_resolution,one_mul,mul_one]
  calc
    _=∑i : Channel F,∑j : Channel F,
      ((if channelValue F i=channelValue F j then sourceChannelOp F i*sourceActualGaussCharge*sourceChannelOp F j else 0)+
      (if channelValue F i=channelValue F j then 0 else
        (((channelValue F i-channelValue F j:ℝ):ℂ)⁻¹) •
          (sourceChannelOp F i*sourceC0ChargeTorque F*sourceChannelOp F j))) := by
      simp only [sourceChargeOffEnergy,sourceEqualProjection_apply,sourcePairProjection_apply,
        Finset.sum_add_distrib]
    _=∑i : Channel F,∑j : Channel F,sourceChannelOp F i*sourceActualGaussCharge*sourceChannelOp F j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases same : channelValue F i=channelValue F j
      · simp only [if_pos same,add_zero]
      · simp only [if_neg same,zero_add,energy_term F i j same]
    _=_ := all

theorem sourceChargeOffEnergy_original (F : GaussUnitaryHistory.Index) :
    sourceChargeOffEnergy F=sourceActualGaussCharge-sourceEqualProjection F sourceActualGaussCharge := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using sourceChargeEnergy_resolution F

def sourceEnergyChargePrice (F : GaussUnitaryHistory.Index) : ℝ :=
  ∑i : Channel F,∑j : Channel F,if channelValue F i=channelValue F j then 0 else
    |channelValue F i-channelValue F j|⁻¹

theorem sourceEnergyChargePrice_nonneg (F : GaussUnitaryHistory.Index) : (0:ℝ)  ≤  (sourceEnergyChargePrice F:ℝ) := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- A finite price generated by the actual spectrum, without a uniform-gap claim. -/
theorem sourceChargeOffEnergy_price (F : GaussUnitaryHistory.Index) :
    ‖sourceChargeOffEnergy F‖ ≤ sourceEnergyChargePrice F*‖sourceC0ChargeTorque F‖ := by
  classical
  have sandwich (i j : Channel F) :
      ‖sourceChannelOp F i*sourceC0ChargeTorque F*sourceChannelOp F j‖ ≤ ‖sourceC0ChargeTorque F‖ := by
    calc
      _ ≤ ‖sourceChannelOp F i‖*‖sourceC0ChargeTorque F‖*‖sourceChannelOp F j‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖sourceC0ChargeTorque F‖*1 := by
        gcongr
        · exact sourceChannelOp_price F i
        · exact sourceChannelOp_price F j
      _=_ := by rw [one_mul,mul_one]
  unfold sourceChargeOffEnergy sourceEnergyChargePrice
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases same : channelValue F i=channelValue F j
  · simp only [if_pos same,norm_zero,zero_mul,le_refl]
  · simp only [if_neg same,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (sandwich i j) (inv_nonneg.mpr (abs_nonneg _))

/-- The complete grouped window exchange is generated by the actual material off-diagonal charge. -/
def sourceEqualMaterialExchange (F : GaussUnitaryHistory.Index) (A : SourceOp) : SourceOp :=
  sourceChargeOffEnergy F*sourceEqualProjection F A-sourceEqualProjection F A*sourceChargeOffEnergy F-
    sourceEqualProjection F (sourceChargeOffEnergy F*A-A*sourceChargeOffEnergy F)

theorem sourceEqualMaterialExchange_original (F : GaussUnitaryHistory.Index) (A : SourceOp) :
    sourceEqualMaterialExchange F A=sourceCoframeEqualExchange F A := by
  have original : sourceCoframeEqualExchange F A=
      (sourceActualGaussCharge*sourceEqualProjection F A-sourceEqualProjection F A*sourceActualGaussCharge)-
        sourceEqualProjection F (sourceActualGaussCharge*A-A*sourceActualGaussCharge) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sourceCoframeEqualExchange_return F A).symm
  rw [original]
  unfold sourceEqualMaterialExchange
  rw [sourceChargeOffEnergy_original]
  simp only [sub_mul,mul_sub,map_sub,sourceEqualProjection_left_module,sourceEqualProjection_right_module]
  abel

/-- The kernel used in the source energy transfer is the already-generated complete native/matter and physical-span pairing. -/
def sourceC0ConfigurationRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  ∑g : NativeHistoryGrade.Label,
    (-(sourceNativeTorque (gradedTest 0 F g x) (gradedTest 0 F g y)+
        sourcePair (gradedTest 0 F g x)
          (sourceColorWardOperator GaussMatterCore.matterAction (gradedTest 0 F g y)))+
      sourcePair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (sourcePhysicalSpanChargeDefect F g y))-
      sourcePair (sourcePhysicalSpanChargeDefect F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y)))

private theorem c0_pair (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (sourceC0ChargeTorque F y)=sourceC0ConfigurationRead F x y :=
  sourcePhysicalCompression_chargePair F x y

private theorem c0_sandwich (F : GaussUnitaryHistory.Index) (L R : SourceOp) (x y : H) :
    inner ℂ x ((L*sourceC0ChargeTorque F*R) y)=sourceC0ConfigurationRead F (L.adjoint x) (R y) := by
  have paid:=(ContinuousLinearMap.adjoint_inner_left L (sourceC0ChargeTorque F (R y)) x).symm.trans
    (c0_pair F (L.adjoint x) (R y))
  simpa only [mul_apply_eq_comp] using paid

/-- Every actual transported pair consumes the source C0 configuration torque, including finite-span defects. -/
theorem sourceChargeOffEnergy_read (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (sourceChargeOffEnergy F y)=
      ∑i : Channel F,∑j : Channel F,if channelValue F i=channelValue F j then 0 else
        (((channelValue F i-channelValue F j:ℝ):ℂ)⁻¹)*
          sourceC0ConfigurationRead F ((sourceChannelOp F i).adjoint x) (sourceChannelOp F j y) := by
  classical
  simp only [sourceChargeOffEnergy,sum_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : channelValue F i=channelValue F j
  · simp only [if_pos same,zero_apply,inner_zero_right]
  · simp only [if_neg same,smul_apply,inner_smul_right,c0_sandwich]

/-- Actual prepared matrix elements consume every unequal-energy material torque entry; same-energy contributions are not divided. -/
theorem sourceChargeOffEnergy_prepared (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) :
    sourceQuantumChargedRead q sL eL sR eR (sourceChargeOffEnergy q.F)=
      ∑i : Channel q.F,∑j : Channel q.F,if channelValue q.F i=channelValue q.F j then 0 else
        (((channelValue q.F i-channelValue q.F j:ℝ):ℂ)⁻¹)*
          sourceC0ConfigurationRead q.F
            ((sourceChannelOp q.F i).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
            (sourceChannelOp q.F j (sourceChargedGaussPrepared q.epsilon q.precision sR eR)) := by
  simpa only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply] using
    sourceChargeOffEnergy_read q.F (sourceChargedGaussPrepared q.epsilon q.precision sL eL)
      (sourceChargedGaussPrepared q.epsilon q.precision sR eR)

end LowEnergy.PreparationPhysicalMaterialSpectralCharge
