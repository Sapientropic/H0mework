import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceLorentzRawGrade

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalLorentzSeedReturn
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
local instance LorentzProjectionIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] frameTest frameVector finiteRiesz rawForm sourceRetainerSeed sourceFullInitialUpper
  jointResolvent sourceProjection sourceExcitedProjection
attribute [local irreducible] PreparationVacuumRawJointFeedback.rawReader

private theorem lorentz_weak_project (mu : Fin 4) (a : Fin 6) (p : PhysicalMomentum)
    (g : Label) (f h : GaussCoreDifferential.QuantumTest) :
    rawForm (fieldUnit (lorentzSlot mu a)) p (project g f) h 0=
      rawForm (fieldUnit (lorentzSlot mu a)) p f (project g h) 0 := by
  rw [rawForm_original,rawForm_original]
  apply integral_congr_ae
  filter_upwards with z
  simp only [project_apply]
  by_cases inside : z∈physicalChart
  · rw [(paidLorentzGrade% sample_project)]
    have commute:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (h z))
      (sourceLorentzRawFiber_blocks mu a p ⟨z,inside⟩ g).eq
    simpa only [mul_apply_eq_comp] using congrArg (fun v=>pairSample z (f z) v) commute
  · have off : z∉tsupport f:=fun member=>inside (f.tsupport_subset member)
    rw [image_eq_zero_of_notMem_tsupport off,map_zero,pairSample_zero_left,pairSample_zero_left]

private theorem lorentz_frame_off (mu : Fin 4) (a : Fin 6) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (i j : FrameIndex F) (different : i.1≠j.1) :
    rawForm (fieldUnit (lorentzSlot mu a)) p (frameTest F i) (frameTest F j) 0=0 := by
  have paid:=lorentz_weak_project mu a p i.1 (frameTest F i) (frameTest F j)
  rw [(paidLorentzGrade% frame_project),if_pos rfl,(paidLorentzGrade% frame_project),if_neg different] at paid
  refine paid.trans ?_
  rw [rawForm_original]
  simp [pairSample]

/-- Original configuration pairing and finiteRiesz compression preserve the generated Lorentz grade, including every independent frame label. -/
theorem sourceLorentzRawReader_blocks (mu : Fin 4) (a : Fin 6) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (g : Label) :
    Commute (projection g) (PreparationVacuumRawJointFeedback.rawReader (fieldUnit (lorentzSlot mu a)) p F 0) := by
  change projection g*PreparationVacuumRawJointFeedback.rawReader (fieldUnit (lorentzSlot mu a)) p F 0=
    PreparationVacuumRawJointFeedback.rawReader (fieldUnit (lorentzSlot mu a)) p F 0*projection g
  unfold PreparationVacuumRawJointFeedback.rawReader finiteRiesz
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    (paidLorentzGrade% frame_rank_left),(paidLorentzGrade% frame_rank_right)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : i.1=j.1
  · have predicates : (g=i.1)↔(g=j.1):=by rw [same]
    simp only [predicates]
  · have scalarZero (e : ℂ) (x y : SourceOp) (zero : e=0) : e • x=e • y := by
      subst e
      apply ContinuousLinearMap.ext
      intro v
      change (0:ℂ) • (x v)=(0:ℂ) • (y v)
      rw [zero_smul,zero_smul]
    exact scalarZero
      (rawForm (fieldUnit (lorentzSlot mu a)) p (frameTest F i) (frameTest F j) 0)
      (if g=i.1 then InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j) else 0)
      (if g=j.1 then InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j) else 0)
      (lorentz_frame_off mu a p F i j same)

private theorem projection_orthogonal : sourceProjection*sourceExcitedProjection=0 := by
  unfold sourceProjection sourceExcitedProjection
  rw [projection_product]
  norm_num [CanonicalGradedCurrent.sourceLabel,sourceExcitedLabel]

private theorem projected_initial (P E gLeft gRight fLeft fRight B : SourceOp)
    (left : P*gLeft=fLeft*P) (right : P*gRight=fRight*P) (reader : P*B=B*P) (zero : P*E=0) :
    P*(gLeft*B*gRight)*E=0 := by
  calc
    _=((P*gLeft)*B*gRight)*E:=by noncomm_ring
    _=((fLeft*P)*B*gRight)*E:=by rw [left]
    _=fLeft*(P*B)*gRight*E:=by noncomm_ring
    _=fLeft*(B*P)*gRight*E:=by rw [reader]
    _=fLeft*B*(P*gRight)*E:=by noncomm_ring
    _=fLeft*B*(fRight*P)*E:=by rw [right]
    _=fLeft*B*fRight*(P*E):=by noncomm_ring
    _=0:=by rw [zero,mul_zero]

/-- Both original full Green inverses and the actual N1 projectors turn the Lorentz grade into zero original upper seed. -/
theorem sourceFullInitialUpper_lorentz_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 6) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceFullInitialUpper q pL pR (lorentzSlot mu a)=0 := by
  unfold sourceFullInitialUpper rawInitial
  rw [sourcePhysicalMaterialPoint_left]
  change sourceProjection*(jointResolvent pL q.F q.z 0*
    PreparationVacuumRawJointFeedback.rawReader (fieldUnit (lorentzSlot mu a)) pR q.F 0*
      jointResolvent pR q.F q.w 0)*sourceExcitedProjection=0
  exact projected_initial _ _ _ _ _ _ _
    ((actual_resolvent_sourceProjection pL q.F q.z left).trans ((paidLorentzGrade% bareResolvent_blocks) pL q.F q.z left).eq)
    ((actual_resolvent_sourceProjection pR q.F q.w right).trans ((paidLorentzGrade% bareResolvent_blocks) pR q.F q.w right).eq)
    (by simpa only [sourceProjection] using (sourceLorentzRawReader_blocks mu a pR q.F CanonicalGradedCurrent.sourceLabel).eq) projection_orthogonal

/-- Every original Lorentz24 retainer seed is computed zero; scalar and coframe Yukawa columns remain. -/
theorem sourceRetainerSeed_lorentz_zero (q : PhysicalResponsePoint) (mu : Fin 4) (a : Fin 6)
    (left : q.z.im≠0) (right : q.w.im≠0) : sourceRetainerSeed q (lorentzSlot mu a)=0 := by
  simp only [sourceRetainerSeed,sourceFullInitialUpper_lorentz_zero q 0 0 mu a left right,map_zero,zero_mul]

theorem sourceMasterCurrent_lorentz_zero (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 6) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceMasterCurrent q n zeta l r (lorentzSlot mu a)=0 := by
  simp only [sourceMasterCurrent,sourceRetainerSeed_lorentz_zero q mu a left right,mul_zero,map_zero]

theorem sourceFullCurrentResidue_lorentz_zero (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 6)
    (left : q.z.im≠0) (right : q.w.im≠0) : sourceFullCurrentResidue q n zeta l r (lorentzSlot mu a)=0 := by
  rw [sourceFullCurrentResidue_square q n zeta causal]
  simp only [sourceRetainerSeed_lorentz_zero q mu a left right,mul_zero,map_zero]

theorem sourceStaticCurrent_lorentz_zero (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 6) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceStaticCurrent q n l r (lorentzSlot mu a)=0 := by
  rw [sourceStaticCurrent_seed]
  simp only [sourceRetainerSeed_lorentz_zero q mu a left right,mul_zero,map_zero]

end LowEnergy.PreparationPhysicalLorentzSeedReturn
