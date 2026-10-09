import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceWholeConfigurationPotential

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeOriginPolynomial
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
local instance OriginConfigurationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The three coefficients are literal cofactors of the actual positive triangular source frame. -/
def sourceCoframeModeWeight (z : SourceCoordinateSlice) : Fin 3 → ℝ :=
  ![lapse*z.1 2*z.1 5,lapse*z.1 1*z.1 5,lapse*z.1 0*z.1 5]

def sourceCoframeModeGamma (j : Fin 4) : SourceMatrix :=
  Complex.I • spinCoordinates (diracGamma j)

private theorem first_gamma (z : physicalChart) :
    coefficientMatrix 1 (sourceCoframe z.val)=((z.val.1 0)⁻¹:ℂ) • sourceCoframeModeGamma 1 := by
  unfold coefficientMatrix
  rw [show (1:Fin 4)=(0:Fin 3).succ from rfl,spatial_gamma]
  simp only [Fin.sum_univ_three]
  change Complex.I • spinCoordinates ((((z.val.1 0)⁻¹:ℝ):ℂ) • diracGamma 1+
    (0:ℂ) • diracGamma 2+(0:ℂ) • diracGamma 3)=_
  simp only [zero_smul,add_zero,map_smul]
  unfold sourceCoframeModeGamma
  rw [smul_comm]
  simp only [Complex.ofReal_inv]
  rfl

private theorem second_gamma (z : physicalChart) :
    coefficientMatrix 2 (sourceCoframe z.val)=
      ((-(z.val.1 1)/(z.val.1 0*z.val.1 2):ℝ):ℂ) • sourceCoframeModeGamma 1+
        ((z.val.1 2)⁻¹:ℂ) • sourceCoframeModeGamma 2 := by
  unfold coefficientMatrix
  rw [show (2:Fin 4)=(1:Fin 3).succ from rfl,spatial_gamma]
  simp only [Fin.sum_univ_three]
  change Complex.I • spinCoordinates (((-(z.val.1 1)/(z.val.1 0*z.val.1 2):ℝ):ℂ) • diracGamma 1+
    (((z.val.1 2)⁻¹:ℝ):ℂ) • diracGamma 2+(0:ℂ) • diracGamma 3)=_
  simp only [zero_smul,add_zero,map_add,map_smul,smul_add]
  unfold sourceCoframeModeGamma
  congr 1 <;> rw [smul_comm]
  simp only [Complex.ofReal_inv]
  rfl

/-- Volume cancels the inverse in the first source row without a chosen scale or new profile. -/
theorem sourceCoframeMode_first (z : physicalChart) :
    stateVolume (sourceState z.val) • coefficientMatrix 1 (sourceCoframe z.val)=
      (sourceCoframeModeWeight z.val 0:ℂ) • sourceCoframeModeGamma 1 := by
  rw [sourceStateVolume_actual,first_gamma,smul_smul]
  congr 1
  have h0 : (z.val.1 0:ℂ)≠0:=Complex.ofReal_ne_zero.mpr z.property.1.ne'
  simp only [sourceCoframeModeWeight,Matrix.cons_val_zero,GaussNativeEnergy.volume]
  push_cast
  field_simp

/-- The second source row retains both its shear and diagonal cofactor. -/
theorem sourceCoframeMode_second (z : physicalChart) :
    stateVolume (sourceState z.val) • coefficientMatrix 2 (sourceCoframe z.val)=
      -(sourceCoframeModeWeight z.val 1:ℂ) • sourceCoframeModeGamma 1+
        (sourceCoframeModeWeight z.val 2:ℂ) • sourceCoframeModeGamma 2 := by
  rw [sourceStateVolume_actual,second_gamma,smul_add,smul_smul,smul_smul]
  have h0 : (z.val.1 0:ℂ)≠0:=Complex.ofReal_ne_zero.mpr z.property.1.ne'
  have h2 : (z.val.1 2:ℂ)≠0:=Complex.ofReal_ne_zero.mpr z.property.2.1.ne'
  congr 1
  · congr 1
    change _ = -((lapse*z.val.1 1*z.val.1 5:ℝ):ℂ)
    simp only [GaussNativeEnergy.volume]
    push_cast
    field_simp
  · congr 1
    change _ = ((lapse*z.val.1 0*z.val.1 5:ℝ):ℂ)
    simp only [GaussNativeEnergy.volume]
    push_cast
    field_simp

/-- Fixed source matrices, before the independent dual branch and full CAR quantizer. -/
def sourceCoframeModeMatrix : Fin 3 → SourceMatrix :=
  ![densityActionMatrix*(sourceCoframeModeGamma 1*nativePrimal (colorGenerator 1)),
    densityActionMatrix*(sourceCoframeModeGamma 1*nativePrimal (colorGenerator 0)),
    densityActionMatrix*(sourceCoframeModeGamma 2*nativePrimal (colorGenerator 0))]

def sourceCoframeModeCoefficient (z : SourceCoordinateSlice) : SourceMatrix :=
  (2:ℝ) • ((sourceCoframeModeWeight z 0:ℂ) • sourceCoframeModeMatrix 0+
    (sourceCoframeModeWeight z 1:ℂ) • sourceCoframeModeMatrix 1-
    (sourceCoframeModeWeight z 2:ℂ) • sourceCoframeModeMatrix 2)

/-- All configuration dependence of this actual vertex is the three source cofactor polynomials. -/
theorem sourceModeCoefficient_polynomial (z : physicalChart) :
    sourceModeCoefficient (sourceState z.val)=sourceCoframeModeCoefficient z.val := by
  unfold sourceModeCoefficient sourceCoframeModeCoefficient
  congr 1
  change densityActionMatrix*(stateVolume (sourceState z.val) •
    (coefficientMatrix 1 (sourceCoframe z.val)*nativePrimal (colorGenerator 1)-
      coefficientMatrix 2 (sourceCoframe z.val)*nativePrimal (colorGenerator 0)))=_
  rw [smul_sub,←smul_mul_assoc,←smul_mul_assoc,sourceCoframeMode_first,sourceCoframeMode_second]
  simp only [sourceCoframeModeMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,add_mul,smul_mul_assoc,mul_smul_comm,mul_add,mul_sub,neg_smul,neg_mul,mul_neg]
  abel

/-- The full primal/independent-dual symbol retains the actual opposite-dual operator. -/
def sourceCoframeModeSymbol (z : SourceCoordinateSlice) : FullMatrix :=
  oppositeDual*SourceRealScalarFock.branches (sourceCoframeModeCoefficient z)

theorem sourceModeSymbol_polynomial (z : physicalChart) :
    sourceModeSymbol (sourceState z.val)=sourceCoframeModeSymbol z.val := by
  unfold sourceModeSymbol sourceCoframeModeSymbol
  rw [sourceModeCoefficient_polynomial]

def sourceCoframeModeFiber (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber :=
  GaussQuantumMultiplier.quantizer (sourceCoframeModeSymbol z)

theorem sourceModeFiber_polynomial (z : physicalChart) :
    sourceModeFiber z.val=sourceCoframeModeFiber z.val := by
  unfold sourceModeFiber sourceCoframeModeFiber
  rw [sourceModeSymbol_polynomial]

end LowEnergy.PreparationPhysicalCoframeOriginPolynomial
