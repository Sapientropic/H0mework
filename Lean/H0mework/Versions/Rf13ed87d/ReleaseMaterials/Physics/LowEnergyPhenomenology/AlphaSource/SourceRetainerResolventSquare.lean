import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialSpatialReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalRetainerResolventSquare
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
local instance RetainerSquareIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalJointRadialForcing PreparationVacuumPhysicalHalfAxis CanonicalGradedCurrent

attribute [local irreducible] actualC actualA sourceEqualProjection sourceRetainerReturn sourceFullInitialUpper
  sourceFullInitialBase sourcePinnedResolvent sourcePoleRead sourceOriginInverse sourceBaseResidue sourceUpperResidue
  sourceChannelOp sourcePairProjection channelValue sourceNativeReaderFirst sourceActualNativeResidue sourceProjection

open Lean Elab Term in
elab "paidRetainerEq% " : term => do
  let wanted:=`LowEnergy.PreparationVacuumPhysicalPinnedVelocity.equal_of_commute
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedLeadingInverse." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>
    let actual:=(←getEnv).constants.toList.filter fun (name,_)=>privateToUserName name==wanted
    throwError "Expected unique original SourcePinnedLeadingInverse.equal_of_commute; imported exact-user-name owners: {actual.map Prod.fst}"

private theorem adjoint_product (A B : SourceOp) :
    ContinuousLinearMap.adjoint (A*B)=ContinuousLinearMap.adjoint B*ContinuousLinearMap.adjoint A := by
  simp only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp]

/-- The original equal-energy conditional expectation preserves the actual independent adjoint. -/
theorem sourceEqualProjection_adjoint (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    ContinuousLinearMap.adjoint (sourceEqualProjection F X)=
      sourceEqualProjection F (ContinuousLinearMap.adjoint X) := by
  rw [sourceEqualProjection_apply,sourceEqualProjection_apply,map_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : channelValue F i=channelValue F j
  · simp only [if_pos same,if_pos same.symm,sourcePairProjection_apply]
    have left:=sourceChannel_selfAdjoint F i
    have right:=sourceChannel_selfAdjoint F j
    change ContinuousLinearMap.adjoint (sourceChannelOp F i)=sourceChannelOp F i at left
    change ContinuousLinearMap.adjoint (sourceChannelOp F j)=sourceChannelOp F j at right
    simp only [adjoint_product,left,right]
    noncomm_ring
  · have reverse : channelValue F j≠channelValue F i:=Ne.symm same
    rw [if_neg same,if_neg reverse]
    exact (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=H) (F:=H)).map_zero

/-- The left module law is generated from the same original energy projection, not supplied by a caller. -/
theorem sourceEqualProjection_left_module (F : GaussUnitaryHistory.Index) (A X : SourceOp) :
    sourceEqualProjection F (sourceEqualProjection F A*X)=
      sourceEqualProjection F A*sourceEqualProjection F X := by
  have generated:=congrArg (fun Y : SourceOp=>ContinuousLinearMap.adjoint Y)
    (sourceEqualProjection_right_module F (ContinuousLinearMap.adjoint X) (ContinuousLinearMap.adjoint A))
  simpa only [sourceEqualProjection_adjoint,adjoint_product,ContinuousLinearMap.adjoint_adjoint] using generated

theorem sourcePinnedResolvent_equal (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) :
    sourceEqualProjection F (sourcePinnedResolvent F n zeta)=sourcePinnedResolvent F n zeta :=
  (paidRetainerEq%) F _ (sourcePinnedResolvent_commute F n zeta positive)

/-- The actual pinned inverse pulls through its own C0 conditional expectation. -/
theorem sourcePinnedResolvent_left_module (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (X : SourceOp) :
    sourceEqualProjection F (sourcePinnedResolvent F n zeta*X)=
      sourcePinnedResolvent F n zeta*sourceEqualProjection F X := by
  have generated:=sourceEqualProjection_left_module F (sourcePinnedResolvent F n zeta) X
  simpa only [sourcePinnedResolvent_equal F n zeta positive] using generated

/-- All original field columns keep their actual right retainer and both source energy projections. -/
def sourceRetainerSeed (q : PhysicalResponsePoint) (i : Fin 289) : SourceOp :=
  sourceEqualProjection q.F (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)*
    (actualA 0 q.F*sourceProjection))

/-- The full original two-resolvent base is a same-source resolvent square, because the actual retainer acts on the right. -/
theorem sourceBaseResidue_square (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (i : Fin 289) :
    sourceBaseResidue q n zeta i=(-Complex.I) •
      ((sourcePinnedResolvent q.F n zeta)^2*sourceRetainerSeed q i) := by
  simp only [sourceBaseResidue,sourceUpperResidue,(paidSpatial% projected_origin),sourceRetainerReturn_apply,map_smul]
  rw [mul_assoc (sourcePinnedResolvent q.F n zeta),sourcePinnedResolvent_left_module q.F n zeta positive]
  simp only [sourceRetainerSeed,pow_two,←mul_assoc]
  apply ContinuousLinearMap.ext
  intro x
  simp only [neg_apply,smul_apply]
  exact (neg_smul Complex.I _).symm

/-- The actual independent two-Green reader consumes every current component of the same resolvent square. -/
theorem sourceFullCurrentResidue_square (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) (i : Fin 289) :
    sourceFullCurrentResidue q n zeta l r i=Complex.I*
      sourcePoleRead q.epsilon q.precision 0 0 l r
        ((sourcePinnedResolvent q.F n zeta)^2*sourceRetainerSeed q i) := by
  rw [sourceFullCurrentResidue,sourceBaseResidue_square q n zeta positive i,map_smul]
  simp only [smul_eq_mul,neg_mul,neg_neg]

/-- The original full native field keeps its complete gauge term and first reader, with the actual square current inserted. -/
theorem sourceActualNativeResidue_square (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    sourceActualNativeResidue q n zeta l r=sourceOriginCurrentResidue q n zeta l r+
      sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥ(fun i : Fin 289=>Complex.I*
        sourcePoleRead q.epsilon q.precision 0 0 l r
          ((sourcePinnedResolvent q.F n zeta)^2*sourceRetainerSeed q i)) := by
  rw [sourceActualNativeResidue]
  congr 1
  apply congrArg (fun v : Fin 289→ℂ=>sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥv)
  funext i
  exact sourceFullCurrentResidue_square q n zeta positive l r i

theorem sourceRetainerSeed_bound (q : PhysicalResponsePoint) (i : Fin 289) :
    ‖sourceRetainerSeed q i‖≤‖sourceEqualProjection q.F‖^2*‖sourceFullInitialUpper q 0 0 i‖*
      ‖actualA 0 q.F*sourceProjection‖ := by
  unfold sourceRetainerSeed
  calc
    _≤‖sourceEqualProjection q.F‖*‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)*
        (actualA 0 q.F*sourceProjection)‖ := (sourceEqualProjection q.F).le_opNorm _
    _≤‖sourceEqualProjection q.F‖*(‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖*
        ‖actualA 0 q.F*sourceProjection‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (ContinuousLinearMap.opNorm_nonneg (sourceEqualProjection q.F))
    _≤‖sourceEqualProjection q.F‖*((‖sourceEqualProjection q.F‖*‖sourceFullInitialUpper q 0 0 i‖)*
        ‖actualA 0 q.F*sourceProjection‖) := by gcongr;exact (sourceEqualProjection q.F).le_opNorm _
    _=_:=by ring

end LowEnergy.PreparationPhysicalRetainerResolventSquare
