import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointMaterialCharge

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

/-- This is the actual Number/G preservation of the full source charge, independent of a chosen eigenbasis. -/
theorem sourceActualCharge_gradePreserves : GaussFockLabel.Preserves sourceActualGaussChargeMatrix := by
  intro i j
  rw [sourceActualCharge_fullDiagonal,Matrix.diagonal_apply]
  split_ifs with same
  · subst j
    simp
  · simp

theorem sourceActualCharge_grade (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g) sourceActualGaussCharge := by
  have paid:=CanonicalGradedCurrent.boundedMatrix_blocks sourceActualGaussChargeMatrix sourceActualCharge_gradePreserves g
  rw [paidPhaseGaugeBoundedLift%] at paid
  exact paid

theorem sourceActualCharge_projection : Commute sourceProjection sourceActualGaussCharge := by
  simpa only [sourceProjection] using sourceActualCharge_grade sourceLabel

/-- The joint source uses the original physical compression at its zero-field point. -/
theorem sourceMaterialJoint_base (F : GaussUnitaryHistory.Index) :
    jointGenerator 0 F 0 0=actualC 0 F+uncutOperator 0 (finiteRetainer 0 F) 0 := by
  have base:=(jointCompression_ray (0:Field289) 0 F).self_of_nhds
  simp only [zero_smul,transportedCompression_zero] at base
  have scalar : jointY (finiteRetainer 0 F) 0=uncutOperator 0 (finiteRetainer 0 F) 0 := by
    simpa only [zero_smul] using jointY_ray (0:Field289) (finiteRetainer 0 F) 0
  unfold jointGenerator
  rw [base,scalar,zero_smul ℂ (1:SourceOp),sub_zero]
  rfl

/-- No sourceApprox is substituted: both tests come from the original physicalSpan and gradedTest. -/
theorem sourcePhysicalCompression_pair (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (actualC 0 F y)=∑g : NativeHistoryGrade.Label,
      sourcePair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y)) := by
  have paid:=(gradedForm_pair (0:Field289) 0 F x y).self_of_nhds
  simpa only [actualC,gradedForm_zero,physicalForm_source,physicalAction_zero] using paid

def sourcePhysicalSpanChargeDefect (F : GaussUnitaryHistory.Index) (g : NativeHistoryGrade.Label) (x : H) : QuantumTest :=
  gradedTest 0 F g (sourceActualGaussCharge x)-sourceCoframeChargeCore (gradedTest 0 F g x)

private theorem actual_core_pair (f g : QuantumTest) :
    sourcePair (sourceCoframeChargeCore f) g=sourcePair f (sourceCoframeChargeCore g) := by
  have paid:=sourceActualGaussCharge_pair (embed f) (embed g)
  rw [sourceCoframeChargeCore_embed,sourceCoframeChargeCore_embed] at paid
  exact paid

/-- The original finite material charge exchange is evaluated as the actual native/matter torque and both physical-span defects. -/
theorem sourcePhysicalCompression_chargePair (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x ((actualC 0 F*sourceActualGaussCharge-sourceActualGaussCharge*actualC 0 F) y)=
      ∑g : NativeHistoryGrade.Label,
        (-(sourceNativeTorque (gradedTest 0 F g x) (gradedTest 0 F g y)+
            sourcePair (gradedTest 0 F g x)
              (sourceColorWardOperator GaussMatterCore.matterAction (gradedTest 0 F g y)))+
          sourcePair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (sourcePhysicalSpanChargeDefect F g y))-
          sourcePair (sourcePhysicalSpanChargeDefect F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y))) := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_right]
  rw [←sourceActualGaussCharge_pair,sourcePhysicalCompression_pair,sourcePhysicalCompression_pair,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have right : gradedTest 0 F g (sourceActualGaussCharge y)=
      sourceCoframeChargeCore (gradedTest 0 F g y)+sourcePhysicalSpanChargeDefect F g y := by
    unfold sourcePhysicalSpanChargeDefect
    abel
  have left : gradedTest 0 F g (sourceActualGaussCharge x)=
      sourceCoframeChargeCore (gradedTest 0 F g x)+sourcePhysicalSpanChargeDefect F g x := by
    unfold sourcePhysicalSpanChargeDefect
    abel
  rw [right,left,map_add]
  have torque:=sourceActualCharge_diagonalForm (gradedTest 0 F g x) (gradedTest 0 F g y)
  have paired:=actual_core_pair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y))
  simp only [sourcePair,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_right] at torque paired ⊢
  rw [paired]
  linear_combination torque

/-- The auxiliary core approximation is taken at a fixed original retainer and at arbitrary actual Hilbert states. -/
theorem sourceRetainedTorque_whole (phi : CanonicalGradedLocalCurrent.Localizer) (x y : H) :
    Tendsto (fun D : GaussUnitaryHistory.Index=>sourcePair (sourceTestApprox D x)
      (sourceMaterialYukawaTorqueCore phi (sourceTestApprox D y))) GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ x ((uncutOperator 0 phi 0*sourceActualGaussCharge-
        sourceActualGaussCharge*uncutOperator 0 phi 0) y))) := by
  have generated:=(same_source_approximation x).inner (𝕜:=ℂ)
    ((uncutOperator 0 phi 0*sourceActualGaussCharge-
      sourceActualGaussCharge*uncutOperator 0 phi 0).continuous.tendsto y |>.comp (same_source_approximation y))
  simpa only [Function.comp_apply,sourceMaterialYukawaTorque_return,sourcePair] using generated

/-- Literal native/matter configuration torque, both physical-span defects, and the original whole retained scalar term. -/
def sourceMaterialChargeRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  (∑g : NativeHistoryGrade.Label,
    (-(sourceNativeTorque (gradedTest 0 F g x) (gradedTest 0 F g y)+
        sourcePair (gradedTest 0 F g x)
          (sourceColorWardOperator GaussMatterCore.matterAction (gradedTest 0 F g y)))+
      sourcePair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (sourcePhysicalSpanChargeDefect F g y))-
      sourcePair (sourcePhysicalSpanChargeDefect F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y))))+
    inner ℂ x ((uncutOperator 0 (finiteRetainer 0 F) 0*sourceActualGaussCharge-
      sourceActualGaussCharge*uncutOperator 0 (finiteRetainer 0 F) 0) y)

theorem sourceMaterialChargeRead_return (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x ((jointGenerator 0 F 0 0*sourceActualGaussCharge-
      sourceActualGaussCharge*jointGenerator 0 F 0 0) y)=sourceMaterialChargeRead F x y := by
  rw [sourceMaterialJoint_base]
  have split : (actualC 0 F+uncutOperator 0 (finiteRetainer 0 F) 0)*sourceActualGaussCharge-
      sourceActualGaussCharge*(actualC 0 F+uncutOperator 0 (finiteRetainer 0 F) 0)=
      (actualC 0 F*sourceActualGaussCharge-sourceActualGaussCharge*actualC 0 F)+
      (uncutOperator 0 (finiteRetainer 0 F) 0*sourceActualGaussCharge-
        sourceActualGaussCharge*uncutOperator 0 (finiteRetainer 0 F) 0) := by
    simp only [add_mul,mul_add]
    abel
  rw [split,add_apply,inner_add_right,sourcePhysicalCompression_chargePair]
  rfl

/-- The two material inverses read this evaluated torque at their actual left-adjoint/right transported states. -/
theorem sourceMaterialGreen_chargeRead (F : GaussUnitaryHistory.Index) (z : ℂ) (x y : H) :
    inner ℂ x (sourceCoframeGreenExchange F z y)=
      sourceMaterialChargeRead F ((jointResolvent 0 F z 0).adjoint x) (jointResolvent 0 F z 0 y) := by
  unfold sourceCoframeGreenExchange
  simp only [mul_apply_eq_comp]
  rw [←ContinuousLinearMap.adjoint_inner_left,sourceMaterialChargeRead_return]

/-- The source-generated Number/G symmetry removes exactly the two P0 charge commutators. -/
theorem sourceMaterialProjectedExchange (positive : Bool) (q : PhysicalResponsePoint) :
    sourceCoframeProjectedExchange positive q=
      sourceProjection*sourceCoframeGreenChannelExchange positive q*sourceProjection := by
  have zero : sourceActualGaussCharge*sourceProjection-sourceProjection*sourceActualGaussCharge=0 :=
    sub_eq_zero.mpr sourceActualCharge_projection.symm.eq
  simp only [sourceCoframeProjectedExchange,zero,zero_mul,mul_zero,zero_add,add_zero]

/-- Evaluated left and right material insertions, with the independently generated vertex-compression term between them. -/
def sourceMaterialChannelRead (positive : Bool) (q : PhysicalResponsePoint) (x y : H) : ℂ :=
  sourceMaterialChargeRead q.F ((jointResolvent 0 q.F q.z 0).adjoint x)
    (jointResolvent 0 q.F q.z 0 (((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChannelReader positive q.F)
      (jointResolvent 0 q.F q.w 0 y)))+
  inner ℂ x (jointResolvent 0 q.F q.z 0
    (((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeCompressionExchange positive q.F) (jointResolvent 0 q.F q.w 0 y)))+
  sourceMaterialChargeRead q.F
    ((jointResolvent 0 q.F q.w 0).adjoint
      ((jointResolvent 0 q.F q.z 0*((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChannelReader positive q.F)).adjoint x))
    (jointResolvent 0 q.F q.w 0 y)

theorem sourceMaterialChannelRead_return (positive : Bool) (q : PhysicalResponsePoint) (x y : H) :
    inner ℂ x (sourceCoframeGreenChannelExchange positive q y)=sourceMaterialChannelRead positive q x y := by
  unfold sourceMaterialChannelRead
  rw [←sourceMaterialGreen_chargeRead q.F q.z x,
    ←sourceMaterialGreen_chargeRead q.F q.w
      ((jointResolvent 0 q.F q.z 0*((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChannelReader positive q.F)).adjoint x) y]
  simp only [sourceCoframeGreenChannelExchange,add_apply,inner_add_right,
    ContinuousLinearMap.adjoint_inner_left,mul_apply_eq_comp]

private theorem material_prepared_sandwich (positive : Bool) (q : PhysicalResponsePoint)
    (L R : SourceOp) (sL eL sR eR : Fin 2) :
    sourceQuantumChargedRead q sL eL sR eR (L*sourceCoframeGreenChannelExchange positive q*R)=
      sourceMaterialChannelRead positive q
        (L.adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
        (R (sourceChargedGaussPrepared q.epsilon q.precision sR eR)) := by
  have paid := (ContinuousLinearMap.adjoint_inner_left L
    (sourceCoframeGreenChannelExchange positive q (R (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))
    (sourceChargedGaussPrepared q.epsilon q.precision sL eL)).symm.trans
      (sourceMaterialChannelRead_return positive q
        (L.adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
        (R (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))
  simpa only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,mul_apply_eq_comp] using paid

/-- Every actual grouped equal-energy window transports the original prepared bra and ket into the evaluated material insertion. -/
def sourceMaterialPreparedStatic (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (sL eL sR eR : Fin 2) : ℂ :=
  sourceQuantumChargedRead q sL eL sR eR
    (sourceCoframeResonanceExchange q.F n*sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q)+
      sourceResonanceProjection q.F n 0*sourceCoframeEqualExchange q.F (sourceCoframeProjectedChannel positive q))+
  ∑i : Channel q.F,sourceMaterialChannelRead positive q
    ((sourceResonanceProjection q.F n 0*sourceChannelOp q.F i*sourceProjection).adjoint
      (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
    ((sourceProjection*sourceEnergyWindow q.F i) (sourceChargedGaussPrepared q.epsilon q.precision sR eR))

theorem sourceMaterialPreparedStatic_return (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (sL eL sR eR : Fin 2) :
    sourceQuantumChargedRead q sL eL sR eR (sourceCoframeStaticExchange positive q n)=
      sourceMaterialPreparedStatic positive q n sL eL sR eR := by
  have grouped : sourceQuantumChargedRead q sL eL sR eR
      (sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
        (sourceProjection*sourceCoframeGreenChannelExchange positive q*sourceProjection))=
      ∑i : Channel q.F,sourceMaterialChannelRead positive q
        ((sourceResonanceProjection q.F n 0*sourceChannelOp q.F i*sourceProjection).adjoint
          (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
        ((sourceProjection*sourceEnergyWindow q.F i) (sourceChargedGaussPrepared q.epsilon q.precision sR eR)) := by
    rw [sourceEqualProjection_grouped,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have regroup : sourceResonanceProjection q.F n 0*
        (sourceChannelOp q.F i*(sourceProjection*sourceCoframeGreenChannelExchange positive q*sourceProjection)*sourceEnergyWindow q.F i)=
        (sourceResonanceProjection q.F n 0*sourceChannelOp q.F i*sourceProjection)*
          sourceCoframeGreenChannelExchange positive q*(sourceProjection*sourceEnergyWindow q.F i) := by
      simp only [mul_assoc]
    rw [regroup]
    exact material_prepared_sandwich positive q
      (sourceResonanceProjection q.F n 0*sourceChannelOp q.F i*sourceProjection)
      (sourceProjection*sourceEnergyWindow q.F i) sL eL sR eR

  simp only [sourceCoframeStaticExchange,sourceMaterialProjectedExchange,mul_add,add_assoc,map_add,
    sourceMaterialPreparedStatic,grouped]

/-- The actual combined E_minus-E_plus retains its paid Schwartz/norm-square price; no separate spectral term is integrated without a price. -/
theorem sourceMaterialStaticTorque_integrable (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (c eta : ℝ) (frequency : c≠0) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
      (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair
        (sourceMaterialPreparedStatic false q (sourceSpatialMomentum n) sL edge sR edge-
          sourceMaterialPreparedStatic true q (sourceSpatialMomentum n) sL edge sR edge)) ⟨i.val,by omega⟩)) volume := by
  have paid:=sourceActualCoframeExchange_sameCharge_integrable q sL sR edge c eta frequency causal left right i test x
  simpa only [map_sub,sourceMaterialPreparedStatic_return] using paid

/-- The unsubtracted actual potential and its h*c-normalized independent detector consume the evaluated full material, finite-span and spectral exchanges. -/
theorem sourceMaterialRadialCoupling_return (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL sR edge : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL edge sR edge branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (∑i : Fin 3,(∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
          ((sourcePoleSide (sourceSignedSpeed branch negative) eta)⁻¹*
          (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
          sourceSlowRead (sourceOriginPair
            (sourceMaterialPreparedStatic false q (sourceSpatialMomentum n) sL edge sR edge-
              sourceMaterialPreparedStatic true q (sourceSpatialMomentum n) sL edge sR edge)) ⟨i.val,by omega⟩)) • sourceCommonOriginColumn i))) := by
  have paid:=sourceGaugeRadialCoupling_sameCharge qd q dSL dEL dSR dER sL sR edge T branch negative eta
    causal sourceLeft sourceRight left right test x
  simpa only [map_sub,sourceMaterialPreparedStatic_return] using paid

end LowEnergy.PreparationPhysicalMaterialChargeTorque
