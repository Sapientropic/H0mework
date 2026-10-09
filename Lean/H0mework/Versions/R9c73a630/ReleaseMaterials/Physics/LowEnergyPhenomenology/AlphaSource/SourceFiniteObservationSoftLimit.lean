import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteObservationBound
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteTransferL2

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteObservationSoftReturn
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
local instance finiteObservationWindowIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalFiniteTransferWard MatterSpace.Response

private theorem ordered_forward_continuous (A B : Fin 4→FiberOperators) (q : PhysicalMomentum)
    (T : ℝ) (i j : Fin 4) (v : FullMatterL2) :
    Continuous (fun age=>sourceOrderedInterior A B q T age i j v) := by
  let L : FullMatterL2→L[ℂ]FullMatterL2:=spatialFlow 0 (-T)*(shiftCoefficients A q i).compLpL 2 volume*shiftFlow q T
  have generated:=L.continuous.comp (sourceTransferTransport_continuous (B j) q 0 v)
  have same (age : ℝ) : sourceOrderedInterior A B q T age i j v=
      L ((shiftFlow q (-age)*(B j).compLpL 2 volume*shiftFlow 0 age : FullMatterL2→L[ℂ]FullMatterL2) v) := by
    unfold sourceOrderedInterior L
    rw [sourceTransferShiftFlow_zeroShift,sub_eq_add_neg,←sourceTransferShiftFlow_group q T (-age)]
    simp only [mul_assoc,mul_apply_eq_comp]
  simpa only [Function.comp_def,←same] using generated

private theorem ordered_backward_continuous (A B : Fin 4→FiberOperators) (q : PhysicalMomentum)
    (T : ℝ) (i j : Fin 4) (v : FullMatterL2) :
    Continuous (fun age=>sourceOrderedInterior A B q age T i j v) := by
  let seed:=((shiftFlow q (-T)*(B j).compLpL 2 volume*spatialFlow 0 T : FullMatterL2→L[ℂ]FullMatterL2) v)
  have generated:=sourceTransferTransport_continuous (shiftCoefficients A q i) 0 q seed
  have same (age : ℝ) : sourceOrderedInterior A B q age T i j v=
      (shiftFlow 0 (-age)*(shiftCoefficients A q i).compLpL 2 volume*shiftFlow q age : FullMatterL2→L[ℂ]FullMatterL2) seed := by
    unfold sourceOrderedInterior seed
    rw [sourceTransferShiftFlow_zeroShift,sub_eq_add_neg,←sourceTransferShiftFlow_group q age (-T)]
    simp only [mul_assoc,mul_apply_eq_comp]
  simpa only [←same] using generated

private theorem ordered_read (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (q : PhysicalMomentum) (time age : ℝ) (i j : Fin 4) :
    sourcePreparedOrderedCAR sideL edgeL sideR edgeR A B q time age i j=
      inner ℂ (coordinateLeg i (sourceActualScatteringInput sideL edgeL))
        (sourceOrderedInterior A B q time age i j (coordinateLeg j (sourceActualScatteringInput sideR edgeR))) := by
  rw [sourcePreparedOrderedCAR_source]
  change inner ℂ (sourceActualScatteringInput sideL edgeL)
    ((coordinateLeg i).adjoint (sourceOrderedInterior A B q time age i j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))=_
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

private theorem pair_age_continuous (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (q : PhysicalMomentum) (T : ℝ) :
    Continuous (fun age=>(sourcePreparedScatteringPair sideL edgeL sideR edgeR A B q T age).1) := by
  simp only [sourcePreparedScatteringPair_fullCAR]
  apply Continuous.const_mul
  apply Continuous.sub
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    simp_rw [ordered_read]
    exact continuous_const.inner (ordered_backward_continuous _ _ _ T i j _)
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    simp_rw [ordered_read]
    exact continuous_const.inner (ordered_forward_continuous _ _ _ T i j _)

/-- The full finite response is strongly measurable in its actual age, retaining both ordered terms and the physical transfer. -/
theorem sourceActualCoupled_age_continuous (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (T : ℝ) (e : scaleDomain) :
    Continuous (fun age=>(sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1) :=
  pair_age_continuous sideL edgeL sideR edgeR _ _ _ T

private theorem soft_field_limit (leg : SourceChargedSoftLeg) (branch : Fin 2) :
    sourceChargedSoftFieldLimit leg branch=sourceSoftGaussAmplitude leg branch • nativeBranchVector branch := by
  unfold sourceChargedSoftFieldLimit sourceSoftGaussAmplitude
  split_ifs <;> simp

private theorem coupled_pointwise (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (T age : ℝ) (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age) scaleApproach
      (𝓝 (sourceWindowScatteringPair sideL edgeL sideR edgeR legs branch T age)) := by
  have generated:=sourceChargedCoupledScattering_tendsto sideL edgeL sideR edgeR legs branch n unit T age nonrealL nonrealR
  simpa only [sourceChargedSoftFieldsLimit,soft_field_limit,sourceWindowScatteringPair,sourceWindowReader,sourceWindowForce] using generated

private theorem weight_bound (energy damping T age : ℝ) (positive : 0 < damping) (window : age ≤ T) :
    ‖sourceWindowWeight energy damping T age‖ ≤ 1 := by
  rw [sourceWindowWeight,temporalWeight_norm]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positive.le) (sub_nonneg.mpr window))

/-- Each actual epsilon response is observed on the same finite retarded age window; its direct contact stays outside. -/
def sourceCoupledCausalWindow (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (e : scaleDomain) : ℂ × ℂ :=
  (∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
    (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1,
    (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T T e).2)

/-- The source-generated uniform price pays the actual epsilon/finite-age interchange. -/
theorem sourceCoupledCausalWindow_tendsto (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (future : 0 ≤ T) (positive : 0 < damping)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (sourceCoupledCausalWindow sideL edgeL sideR edgeR legs branch n unit energy damping T) scaleApproach
      (𝓝 (sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T)) := by
  let μ : Measure ℝ:=volume.restrict (Ioc 0 T)
  let M:=(sourceUniformObservationPrice sideL edgeL sideR edgeR legs branch T).1
  have measurable (e : scaleDomain) : AEStronglyMeasurable (fun age=>sourceWindowWeight energy damping T age*
      (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1) μ :=
    (((temporalWeight_continuous energy damping).comp (continuous_const.sub continuous_id)).mul
      (sourceActualCoupled_age_continuous sideL edgeL sideR edgeR legs branch n unit T e)).aestronglyMeasurable
  have dominated : ∀ᶠ e in scaleApproach,∀ᵐ age ∂μ,‖sourceWindowWeight energy damping T age*
      (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1‖ ≤ M := by
    filter_upwards [sourceActualUniformObservation_bound sideL edgeL sideR edgeR legs branch n unit T future nonrealL nonrealR]
      with e sourceBound
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with age window
    rw [norm_mul]
    have price:=(sourceBound age ⟨window.1.le,window.2⟩).1
    exact (mul_le_mul (weight_bound energy damping T age positive window.2) price
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul M)
  have integrable : Integrable (fun _ : ℝ=>M) μ:=integrable_const _
  have pointwise : ∀ᵐ age ∂μ,Tendsto (fun e=>sourceWindowWeight energy damping T age*
      (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1) scaleApproach
      (𝓝 (sourceWindowWeight energy damping T age*(sourceWindowScatteringPair sideL edgeL sideR edgeR legs branch T age).1)) :=
    ae_of_all _ fun age=>(tendsto_const_nhds (x:=sourceWindowWeight energy damping T age)).mul
      ((continuous_fst.tendsto _).comp (coupled_pointwise sideL edgeL sideR edgeR legs branch n unit T age nonrealL nonrealR))
  let : scaleApproach.IsCountablyGenerated:=by unfold scaleApproach; infer_instance
  have integrals:=tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun _=>M)
    (Eventually.of_forall measurable) dominated integrable pointwise
  have contact:=(continuous_snd.tendsto _).comp
    (coupled_pointwise sideL edgeL sideR edgeR legs branch n unit T T nonrealL nonrealR)
  unfold sourceCoupledCausalWindow sourceFiniteCausalPair
  simpa only [intervalIntegral.integral_of_le future,Function.comp_def,μ] using
    integrals.prodMk_nhds contact

/-- The observable is the original physical-frequency residue pair, before its generated (2 omega)^2 normalization. -/
def sourcePhysicalResidueWindow (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (e : scaleDomain) : ℂ × ℂ :=
  (∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
    (sourceChargedPhysicalResidueScattering sideL edgeL sideR edgeR legs branch n unit T age e).1,
    (sourceChargedPhysicalResidueScattering sideL edgeL sideR edgeR legs branch n unit T T e).2)

theorem sourcePhysicalResidueWindow_normalization (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (e : scaleDomain) :
    sourceCoupledCausalWindow sideL edgeL sideR edgeR legs branch n unit energy damping T e=
      (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
        sourcePhysicalResidueWindow sideL edgeL sideR edgeR legs branch n unit energy damping T e := by
  simp only [sourceCoupledCausalWindow,sourcePhysicalResidueWindow,sourceChargedCoupledScattering_normalization,
    Prod.smul_mk,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  apply Prod.ext
  · dsimp only [Prod.fst]
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro age _
    ring
  · rfl

/-- Both physical branches enter the same source-priced finite causal observation, with their actual independent source legs and direct contact. -/
theorem sourcePhysicalResidueWindow_soft (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (future : 0 ≤ T) (positive : 0 < damping)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
      sourcePhysicalResidueWindow sideL edgeL sideR edgeR legs branch n unit energy damping T e) scaleApproach
      (𝓝 (sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T)) :=
  (sourceCoupledCausalWindow_tendsto sideL edgeL sideR edgeR legs branch n unit energy damping T future positive nonrealL nonrealR).congr'
    (Eventually.of_forall fun e=>sourcePhysicalResidueWindow_normalization sideL edgeL sideR edgeR legs branch n unit energy damping T e)

end LowEnergy.PreparationPhysicalFiniteObservationSoftReturn
