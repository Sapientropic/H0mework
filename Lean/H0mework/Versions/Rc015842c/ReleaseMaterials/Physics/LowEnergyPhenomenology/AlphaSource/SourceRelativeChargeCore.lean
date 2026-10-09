import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargeObservation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMaterialChargeTorque
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
local instance RelativeChargeCoreIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The relative primal/independent-dual phase, on the original complete source matrix. -/
def sourceRelativeChargeMatrix : FullMatrix := Matrix.fromBlocks 1 0 0 (-1)

theorem sourceActualCharge_colourRelative :
    sourceActualGaussChargeMatrix= -chargeMatrix (colorGenerator 2)+(1/2:ℂ) • sourceRelativeChargeMatrix := by
  rw [sourceActualGaussChargeMatrix,sourcePhaseNoether_native]
  ext i j
  cases i <;> cases j <;>
    simp [SourceRealScalarFock.branches,sourceRelativeChargeMatrix,chargeMatrix,nativeFull,
      Matrix.fromBlocks,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_add,map_neg]
  norm_num [Matrix.one_apply,map_ofNat]
  split_ifs <;> ring

private theorem relative_blocks (A D : SourceMatrix) :
    sourceRelativeChargeMatrix*Matrix.fromBlocks A 0 0 D=
      Matrix.fromBlocks A 0 0 D*sourceRelativeChargeMatrix := by
  unfold sourceRelativeChargeMatrix
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [one_mul,mul_one,zero_mul,mul_zero,add_zero,zero_add,neg_mul,mul_neg,neg_zero]

/-- Both original real-scalar branches are retained for arbitrary source scalar and matter matrices. -/
theorem sourceRelativeCharge_branches (A : SourceMatrix) :
    sourceRelativeChargeMatrix*SourceRealScalarFock.branches A=
      SourceRealScalarFock.branches A*sourceRelativeChargeMatrix := relative_blocks A _

theorem sourceRelativeCharge_native (a : NativeLie) :
    sourceRelativeChargeMatrix*nativeFull a=nativeFull a*sourceRelativeChargeMatrix :=
  relative_blocks _ _

theorem sourceRelativeCharge_hermitian : sourceRelativeChargeMatrix.conjTranspose=sourceRelativeChargeMatrix := by
  ext i j
  cases i <;> cases j <;>
    simp [sourceRelativeChargeMatrix,Matrix.conjTranspose_apply,Matrix.fromBlocks,Matrix.one_apply,eq_comm]

def sourceRelativeChargeFiber : FockFiber→L[ℂ]FockFiber := quantized sourceRelativeChargeMatrix

def sourceRelativeChargeCore : QuantumTest→ₗ[ℂ]QuantumTest :=
  action (fun _=>sourceRelativeChargeMatrix) (fun _=>contDiffAt_const)

def sourceRelativeCharge : H→L[ℂ]H := GaussFockLift.lift sourceRelativeChargeFiber

private theorem relative_quantized (A : FullMatrix)
    (generated : sourceRelativeChargeMatrix*A=A*sourceRelativeChargeMatrix) :
    sourceRelativeChargeFiber*quantized A=quantized A*sourceRelativeChargeFiber := by
  have paid:=congrArg quantizer (sub_eq_zero.mpr generated)
  rw [paidCoframeQuantizerComm%,map_zero] at paid
  exact sub_eq_zero.mp paid

theorem sourceRelativeCharge_nativeFiber (a : NativeLie) :
    sourceRelativeChargeFiber*nativeFock a=nativeFock a*sourceRelativeChargeFiber :=
  relative_quantized _ (sourceRelativeCharge_native a)

theorem sourceRelativeCharge_scalarFiber (phi : SourceQuantumScalarChart.Scalar) :
    sourceRelativeChargeFiber*GaussYukawaCoefficient.sourceMap phi=
      GaussYukawaCoefficient.sourceMap phi*sourceRelativeChargeFiber := by
  rw [GaussYukawaCoefficient.source_map_return]
  exact relative_quantized _ (sourceRelativeCharge_branches _)

theorem sourceRelativeCharge_embed (f : QuantumTest) :
    sourceRelativeCharge (embed f)=embed (sourceRelativeChargeCore f) := by
  change GaussFockLift.lift (quantized sourceRelativeChargeMatrix) (embed f)=_
  rw [←paidPhaseGaugeBoundedLift%]
  exact CanonicalGradedCurrent.boundedMatrix_core sourceRelativeChargeMatrix f

theorem sourceRelativeCharge_pair (f g : QuantumTest) :
    sourcePair f (sourceRelativeChargeCore g)=sourcePair (sourceRelativeChargeCore f) g := by
  have hermitian (v w : FockFiber) : inner ℂ (sourceRelativeChargeFiber v) w=
      inner ℂ v (sourceRelativeChargeFiber w) := by
    have paid:=SourceQuantumFockGauge.quantizedFiber_adjoint sourceRelativeChargeMatrix v w
    rw [sourceRelativeCharge_hermitian] at paid
    exact paid
  have paid:=GaussFockLift.lift_pair sourceRelativeChargeFiber sourceRelativeChargeFiber hermitian (embed f) (embed g)
  change inner ℂ (sourceRelativeCharge (embed f)) (embed g)=
    inner ℂ (embed f) (sourceRelativeCharge (embed g)) at paid
  rw [sourceRelativeCharge_embed,sourceRelativeCharge_embed] at paid
  exact paid.symm

/-- The complete actual charge is derived before any finite compression or source-state projection. -/
theorem sourceActualCharge_coreDecomposition :
    sourceCoframeChargeCore= -(chargeAction (colorGenerator 2))+(1/2:ℂ) • sourceRelativeChargeCore := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have paid:=congrArg quantizer sourceActualCharge_colourRelative
  rw [map_add,map_neg,map_smul] at paid
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z)) paid

open Lean Elab Term in
elab "paidRelativeDirectional%" : term => do
  let wanted:=`LowEnergy.PreparationVacuumPhysicalGaussColorTorque.directional_constant
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussConnection." &&
      privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceGaussConnection.directional_constant"

theorem sourceRelativeCharge_directional (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (sourceRelativeChargeCore f) z=sourceRelativeChargeFiber (directional v f z) := by
  exact (paidRelativeDirectional%) v sourceRelativeChargeFiber f z

theorem sourceRelativeCharge_covariant (v : Ambient) :
    (covariantMomentum v).comp sourceRelativeChargeCore=sourceRelativeChargeCore.comp (covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (sourceRelativeChargeCore f) z+
    connection v z (sourceRelativeChargeFiber (f z)))=
      sourceRelativeChargeFiber ((-Complex.I) • (directional v f z+connection v z (f z)))
  rw [sourceRelativeCharge_directional,map_smul,map_add]
  congr 1
  congr 1
  exact (congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z))
    (sourceRelativeCharge_nativeFiber (inverseL z v).1)).symm

theorem sourceRelativeCharge_multiply (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    (GaussNativeForm.multiply c smooth).comp sourceRelativeChargeCore=
      sourceRelativeChargeCore.comp (GaussNativeForm.multiply c smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul sourceRelativeChargeFiber (c z:ℂ) (f z)).symm

theorem sourceRelativeCharge_adjoint (v : Ambient) :
    (GaussMomentumAdjoint.adjoint v).comp sourceRelativeChargeCore=
      sourceRelativeChargeCore.comp (GaussMomentumAdjoint.adjoint v) := by
  apply LinearMap.ext
  intro g
  have pair (f : QuantumTest) :
      sourcePair f (GaussMomentumAdjoint.adjoint v (sourceRelativeChargeCore g))=
        sourcePair f (sourceRelativeChargeCore (GaussMomentumAdjoint.adjoint v g)) := by
    rw [GaussNativeForm.adjoint_pair,sourceRelativeCharge_pair]
    have commute:=congrArg (fun A : QuantumTest→ₗ[ℂ]QuantumTest=>A f) (sourceRelativeCharge_covariant v)
    change covariantMomentum v (sourceRelativeChargeCore f)=sourceRelativeChargeCore (covariantMomentum v f) at commute
    rw [←commute,←GaussNativeForm.adjoint_pair,←sourceRelativeCharge_pair]
  apply sub_eq_zero.mp
  apply embed_injective
  rw [map_zero]
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  let d:=GaussMomentumAdjoint.adjoint v (sourceRelativeChargeCore g)-
    sourceRelativeChargeCore (GaussMomentumAdjoint.adjoint v g)
  have paid:=pair d
  change sourcePair d _=sourcePair d _ at paid
  change sourcePair d d=0
  unfold d sourcePair
  rw [map_sub,inner_sub_right]
  simpa only [sourcePair,d,map_sub] using (sub_eq_zero.mpr paid)

end LowEnergy.PreparationPhysicalMaterialChargeTorque
