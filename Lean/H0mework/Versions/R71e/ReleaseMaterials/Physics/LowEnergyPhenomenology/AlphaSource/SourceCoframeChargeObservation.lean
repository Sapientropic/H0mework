import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargeTransport

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeChargeExchange
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
local instance CoframeExchangeObservationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalCoframeChargeSelection

/-- Actual source preparation charges are read at both ends after all material and finite-frame exchanges. -/
theorem sourceCoframePreparedChannel_ward (positive : Bool) (q : PhysicalResponsePoint)
    (n : PhysicalMomentum) (sL eL sR eR : Fin 2) (left : q.z.im≠0) (right : q.w.im≠0) :
    ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ)-(if positive then (1:ℂ) else -1))*
      sourceQuantumChargedRead q sL eL sR eR (sourceCoframeStaticChannel positive q n)=
      sourceQuantumChargedRead q sL eL sR eR (sourceCoframeStaticExchange positive q n) := by
  have generated:=congrArg (sourceQuantumChargedRead q sL eL sR eR)
    (sourceCoframeStaticChannel_ward positive q n left right)
  rw [sourceActualPreparedCharge_commutator,map_add,map_smul,smul_eq_mul] at generated
  linear_combination generated

/-- Equal-charge actual ends return the complete original static response through the signed material exchanges. -/
theorem sourceCoframePreparedStatic_sameCharge (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (sL sR edge : Fin 2) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceQuantumChargedRead q sL edge sR edge (sourceCoframeChargeStatic q n)=
      sourceQuantumChargedRead q sL edge sR edge
        (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n) := by
  have plus:=sourceCoframePreparedChannel_ward true q n sL edge sR edge left right
  have minus:=sourceCoframePreparedChannel_ward false q n sL edge sR edge left right
  simp only [sub_self,zero_sub,if_true,Bool.false_eq_true,if_false,neg_neg,one_mul,neg_mul] at plus minus
  rw [←sourceCoframeStaticChannel_total,map_add,map_sub]
  linear_combination -plus+minus

def sourceCoframeReturnedStatic (q : PhysicalResponsePoint) (n : PhysicalMomentum) : SourceOp :=
  sourceActualGaussCharge*(sourceCoframeStaticChannel true q n-sourceCoframeStaticChannel false q n)-
    (sourceCoframeStaticChannel true q n-sourceCoframeStaticChannel false q n)*sourceActualGaussCharge+
      (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)

theorem sourceCoframeReturnedStatic_original (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceCoframeReturnedStatic q n=sourceCoframeChargeStatic q n := by
  rw [sourceCoframeStaticChannel_return q n left right]
  unfold sourceCoframeReturnedStatic
  simp only [mul_sub,sub_mul]
  abel

/-- The complete returned expression stays under its original common Schwartz read; no exchange summand is integrated without a price. -/
def sourceCoframeExchangeIntegrand (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
    (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
    sourceSlowRead (sourceOriginPair (sourcePoleRead q.epsilon q.precision 0 0 l r
      (sourceCoframeReturnedStatic q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)

theorem sourceCoframeExchangeIntegrand_original (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceCoframeExchangeIntegrand q c eta l r i test x n=
      sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
        (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
        sourceSlowRead (sourceNativeSimple q (sourceSpatialMomentum n) l r) ⟨i.val,by omega⟩) := by
  rw [sourceCoframeExchangeIntegrand,sourceCoframeReturnedStatic_original q _ left right,
    ←sourceNativeSimple_charge q _ l r left right]

theorem sourceCoframeExchangeIntegrand_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (left : q.z.im≠0) (right : q.w.im≠0)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) (nonzero : n≠0) :
    ‖sourceCoframeExchangeIntegrand q c eta l r i test x n‖≤
      sourceMasterCorrectionPrice q c eta l r i*sourceRadialSchwartzPrice test n := by
  rw [sourceCoframeExchangeIntegrand_original q c eta l r i test x n left right]
  have momentumNZ : sourceSpatialMomentum n≠0:=by
    unfold sourceSpatialMomentum
    exact smul_ne_zero (by positivity : (2*Real.pi:ℝ)≠0) nonzero
  have zp : 0<(sourcePoleSide c eta).re:=by simpa [sourcePoleSide] using causal
  have limit:=(sourceMasterCorrection_pointwise q (sourceSpatialMomentum n) momentumNZ
    (sourcePoleSide c eta) zp l r i).const_mul (sourceSpatialPhase n x*test n)
  exact le_of_tendsto limit.norm (by
    filter_upwards [self_mem_nhdsWithin] with d dp
    exact sourceMasterCorrection_fourier_bound q c eta frequency causal d dp l r i test x n nonzero)

private theorem scaled_side (d c eta : ℝ) :
    (d:ℂ)*sourcePoleSide c eta=sourcePoleSide (d*c) (d*eta) := by
  unfold sourcePoleSide
  push_cast
  ring

theorem sourceCoframeExchangeIntegrand_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (left : q.z.im≠0) (right : q.w.im≠0)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (sourceCoframeExchangeIntegrand q c eta l r i test x) volume := by
  have nz : ∀ᵐ n : PhysicalMomentum ∂volume,n≠0:=by rw [ae_iff];simp
  let approx (d : ℝ) (n : PhysicalMomentum) : ℂ:=if 0<d then
    sourceSpatialPhase n x*test n*((d:ℂ)*sourceMasterChannelCorrection q (sourceSpatialMomentum n)
      ((d:ℂ)*sourcePoleSide c eta) l r i) else 0
  have measurable (d : ℝ) : AEStronglyMeasurable (approx d) volume := by
    by_cases dp : 0<d
    · have paid:=((paidCorrectionIntegrable%) q (d*c) (d*eta) (mul_ne_zero dp.ne' frequency)
        (mul_pos dp causal) l r i test x).const_mul (d:ℂ)
      apply paid.aestronglyMeasurable.congr
      filter_upwards with n
      simp only [approx,if_pos dp,scaled_side]
      ring
    · simp only [approx,if_neg dp]
      exact aestronglyMeasurable_const
  have limit : ∀ᵐ n : PhysicalMomentum ∂volume,
      Tendsto (fun d : ℝ=>approx d n) (𝓝[>] 0) (𝓝 (sourceCoframeExchangeIntegrand q c eta l r i test x n)) := by
    filter_upwards [nz] with n hn
    rw [sourceCoframeExchangeIntegrand_original q c eta l r i test x n left right]
    have momentumNZ : sourceSpatialMomentum n≠0:=by
      unfold sourceSpatialMomentum
      exact smul_ne_zero (by positivity : (2*Real.pi:ℝ)≠0) hn
    have zp : 0<(sourcePoleSide c eta).re:=by simpa [sourcePoleSide] using causal
    apply ((sourceMasterCorrection_pointwise q (sourceSpatialMomentum n) momentumNZ
      (sourcePoleSide c eta) zp l r i).const_mul (sourceSpatialPhase n x*test n)).congr'
    filter_upwards [self_mem_nhdsWithin] with d dp
    change 0<d at dp
    simp only [approx,if_pos dp]
  apply ((sourceRadialSchwartzPrice_integrable test).const_mul (sourceMasterCorrectionPrice q c eta l r i)).mono'
    (aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0:ℝ)) measurable limit)
  filter_upwards [nz] with n hn
  exact sourceCoframeExchangeIntegrand_bound q c eta frequency causal left right l r i test x n hn

def sourceCoframeExchangeSimpleField (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,(∫n : PhysicalMomentum,sourceCoframeExchangeIntegrand q c eta l r i test x n) • sourceCommonOriginColumn i

def sourceActualCoframeExchangeSimple (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceCoframeExchangeSimpleField q c eta l r test x

theorem sourceActualCoframeExchangeSimple_original (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualCoframeExchangeSimple q sL eL sR eR c eta test x=
      sourceActualCoframeChargeSimple q sL eL sR eR c eta test x := by
  simp only [sourceActualCoframeExchangeSimple,sourceActualCoframeChargeSimple,
    sourceCoframeExchangeSimpleField,sourceCoframeChargeSimpleField,sourceCoframeChargeSimpleChannel,
    sourceCoframeExchangeIntegrand,sourceCoframeReturnedStatic_original q _ left right]

private theorem slow_origin_scalar (i : Fin 5) (z : ℂ) :
    sourceSlowRead (sourceOriginPair z) i=z*sourceSlowRead (sourceOriginPair 1) i := by
  have pair : sourceOriginPair z=z • sourceOriginPair 1 := by
    ext j
    simp [sourceOriginPair,Pi.single_apply]
    split_ifs <;> ring
  rw [pair,sourceSlowRead_smul]
  rfl

def sourceActualCoframeExchangeIntegral (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
    (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
    sourceSlowRead (sourceOriginPair (sourceQuantumChargedRead q sL eL sR eR
      (sourceCoframeReturnedStatic q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)

private theorem actual_integrand_source (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
  (c eta : ℝ) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) :
    sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
      (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair (sourceQuantumChargedRead q sL eL sR eR
        (sourceCoframeReturnedStatic q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)=
    ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r*
      sourceCoframeExchangeIntegrand q c eta l r i test x n := by
  simp only [sourceCoframeExchangeIntegrand]
  conv_lhs => rw [slow_origin_scalar]
  conv_rhs =>
    arg 2
    ext l
    arg 2
    ext r
    rw [slow_origin_scalar]
  rw [sourceActualGaussRead_poles q 0 0]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem sourceActualCoframeExchangeIntegral_source (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (frequency : c≠0) (causal : 0<eta) (left : q.z.im≠0) (right : q.w.im≠0)
    (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualCoframeExchangeIntegral q sL eL sR eR c eta i test x=
      ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r*
        ∫n : PhysicalMomentum,sourceCoframeExchangeIntegrand q c eta l r i test x n := by
  unfold sourceActualCoframeExchangeIntegral
  simp_rw [actual_integrand_source]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro l _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro r _
      exact (sourceCoframeExchangeIntegrand_integrable q c eta frequency causal left right l r i test x).const_mul _
  · intro l _
    exact integrable_finsetSum _ (fun r _=>
      (sourceCoframeExchangeIntegrand_integrable q c eta frequency causal left right l r i test x).const_mul _)

theorem sourceActualCoframeExchange_sameCharge_integrable (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (c eta : ℝ) (frequency : c≠0) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
      (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair (sourceQuantumChargedRead q sL edge sR edge
        (sourceCoframeStaticExchange false q (sourceSpatialMomentum n)-
          sourceCoframeStaticExchange true q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)) volume := by
  have generated : Integrable (fun n : PhysicalMomentum=>∑l : RestStateIndex,∑r : RestStateIndex,
      sourceActualPreparedWeight 0 0 sL edge sR edge l r*sourceCoframeExchangeIntegrand q c eta l r i test x n) volume :=
    integrable_finsetSum _ (fun l _=>integrable_finsetSum _ (fun r _=>
      (sourceCoframeExchangeIntegrand_integrable q c eta frequency causal left right l r i test x).const_mul _))
  apply generated.congr
  filter_upwards with n
  rw [←actual_integrand_source,sourceCoframeReturnedStatic_original q _ left right,
    sourceCoframePreparedStatic_sameCharge q _ sL sR edge left right]

/-- The full source64 read is one actual preparation read under the same priced integral. -/
theorem sourceActualCoframeExchangeSimple_read (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (frequency : c≠0) (causal : 0<eta) (left : q.z.im≠0) (right : q.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualCoframeExchangeSimple q sL eL sR eR c eta test x=
      ∑i : Fin 3,sourceActualCoframeExchangeIntegral q sL eL sR eR c eta i test x • sourceCommonOriginColumn i := by
  simp only [sourceActualCoframeExchangeSimple,sourceCoframeExchangeSimpleField,Finset.smul_sum,smul_smul,
    sourceActualCoframeExchangeIntegral_source q sL eL sR eR c eta frequency causal left right,
    Finset.sum_smul]
  conv_lhs =>
    arg 2
    ext l
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Actual equal-charge spatial potential retains every finite-frame, Green, C0 and resonance exchange; no charge-zero field premise is supplied. -/
theorem sourceActualCoframeExchangeSimple_sameCharge (q : PhysicalResponsePoint) (sL sR edge : Fin 2)
    (c eta : ℝ) (frequency : c≠0) (causal : 0<eta) (left : q.z.im≠0) (right : q.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualCoframeExchangeSimple q sL edge sR edge c eta test x=
      ∑i : Fin 3,(∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
        (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
        sourceSlowRead (sourceOriginPair (sourceQuantumChargedRead q sL edge sR edge
          (sourceCoframeStaticExchange false q (sourceSpatialMomentum n)-
            sourceCoframeStaticExchange true q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)) • sourceCommonOriginColumn i := by
  rw [sourceActualCoframeExchangeSimple_read q sL edge sR edge c eta frequency causal left right]
  simp only [sourceActualCoframeExchangeIntegral,sourceCoframeReturnedStatic_original q _ left right,
    sourceCoframePreparedStatic_sameCharge q _ sL sR edge left right]

theorem sourceActualRadialPotential_exchange (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)
      (𝓝[>] 0) (𝓝 (sourceActualCoframeExchangeSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x)) := by
  rw [sourceActualCoframeExchangeSimple_original q sL eL sR eR _ eta test x left right]
  exact sourceActualRadialPotential_charge q sL eL sR eR branch negative eta causal left right test x

/-- Every original independent leg normalization and correction remains in the actual unit observation. -/
theorem sourceActualUnitRadialPotential_exchange (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualCoframeExchangeSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [sourceActualCoframeExchangeSimple_original q sL eL sR eR _ eta test x sourceLeft sourceRight]
  exact sourceActualUnitRadialPotential_charge qd q dSL dEL dSR dER sL eL sR eR T branch negative eta
    causal sourceLeft sourceRight left right test x

/-- The same source phase momentum and propagation speed read this complete charge-selected potential. -/
theorem sourceGaugeRadialCoupling_exchange (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (sourceActualCoframeExchangeSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [sourceActualCoframeExchangeSimple_original q sL eL sR eR _ eta test x sourceLeft sourceRight]
  exact sourceGaugeRadialCoupling_charge qd q dSL dEL dSR dER sL eL sR eR T branch negative eta
    causal sourceLeft sourceRight left right test x


/-- The same physical h*c-normalized, independently normalized detector reads the generated complete exchanges of the original equal-charge source potential. -/
theorem sourceGaugeRadialCoupling_sameCharge (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL sR edge : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL edge sR edge branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (∑i : Fin 3,(∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
          ((sourcePoleSide (sourceSignedSpeed branch negative) eta)⁻¹*
          (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
          sourceSlowRead (sourceOriginPair (sourceQuantumChargedRead q sL edge sR edge
            (sourceCoframeStaticExchange false q (sourceSpatialMomentum n)-
              sourceCoframeStaticExchange true q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)) • sourceCommonOriginColumn i))) := by
  have generated:=sourceGaugeRadialCoupling_exchange qd q dSL dEL dSR dER sL edge sR edge T branch negative eta
    causal sourceLeft sourceRight left right test x
  rw [sourceActualCoframeExchangeSimple_sameCharge q sL sR edge _ eta
    (sourceSignedSpeed_nonzero branch negative) causal sourceLeft sourceRight test x] at generated
  exact generated

end LowEnergy.PreparationPhysicalCoframeChargeExchange
