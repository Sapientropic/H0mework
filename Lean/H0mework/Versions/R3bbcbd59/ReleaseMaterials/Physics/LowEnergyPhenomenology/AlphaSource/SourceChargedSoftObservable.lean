import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeSoftVertices

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedSoftObservable
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
local instance chargedSoftObservableQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

attribute [local irreducible] sourceNativeOriginCanonicalFiber sourceChargedQuantumRead sourceActualScatteringInput
  sourceChargedPhysicalResidueScattering sourcePreparedScatteringPair sourceChargedSoftFieldLimit nativeBranchVector

private def onlyTime (T : FiberOperators) : Fin 4→FiberOperators := fun k=>if k=0 then T else 0
private theorem scalar_zero (c : ℂ) : c • (0:FiberOperators)=0 := @_root_.smul_zero ℂ FiberOperators _ _ c
private theorem scalar_neg (c : ℂ) (A : FiberOperators) : c • (-A)=(-c) • A := by
  apply ContinuousLinearMap.ext
  intro v
  change c • (-(A v))=(-c) • (A v)
  rw [smul_neg,neg_smul]

private theorem onlyTime_shift (T : FiberOperators) (shift : PhysicalMomentum) :
    shiftCoefficients (onlyTime T) shift=onlyTime T := by
  funext k
  cases k using Fin.cases <;> simp [shiftCoefficients,onlyTime,scalar_zero]
private theorem onlyTime_adjoint (T : FiberOperators) : adjointCoefficients (onlyTime T)=onlyTime T.adjoint := by
  funext k
  by_cases zero : k=0 <;> simp [adjointCoefficients,onlyTime,zero]
private theorem zero_compLpL : (0:FiberOperators).compLpL 2 volume=(0:FullMatterL2→L[ℂ]FullMatterL2) := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [norm_zero] using ((0:FiberOperators).norm_compLpL_le (p:=2) (μ:=volume)))
    (norm_nonneg _)

/-- The original real density reader retains its independent positive/negative complex source amplitudes. -/
def sourceSoftNoetherReader (branch : Fin 2) (positive negative : ℂ) : FiberOperators :=
  (2:ℂ)⁻¹ • (negative • sourceNativeOriginCanonicalFiber branch+
    star positive • (sourceNativeOriginCanonicalFiber branch).adjoint)

private theorem reader_time (branch : Fin 2) (positive negative : ℂ) :
    realReaderCoefficients (originalTransferPair (positive • nativeBranchVector branch)
      (negative • nativeBranchVector branch)) 0=onlyTime (sourceSoftNoetherReader branch positive negative) := by
  funext k
  cases k using Fin.cases <;>
    simp [realReaderCoefficients,originalTransferPair,sourceSoftDensity_scaled,sourceSoftDensity_Noether,
      shiftCoefficients,adjointCoefficients,onlyTime,sourceSoftNoetherReader,scalar_zero,
      map_smulₛₗ]

private theorem frequency_time (branch : Fin 2) (c : ℂ) :
    complexFrequencyCoefficients (originalComplexDirection (c • nativeBranchVector branch))=
      onlyTime ((-c) • sourceNativeOriginCanonicalFiber branch) := by
  funext k
  simpa only [onlyTime,sourceSoftFrequency_Noether,scalar_neg] using sourceSoftFrequency_scaled c branch k

private theorem mixed_zero (branch : Fin 2) (ap an bp bn : ℂ) :
    realMixedCoefficients (originalTransferPair (ap • nativeBranchVector branch) (an • nativeBranchVector branch))
      (originalTransferPair (bp • nativeBranchVector branch) (bn • nativeBranchVector branch))=0 := by
  funext k
  simp only [realMixedCoefficients,originalTransferPair,sourceSoftMixed_scaled,map_zero,
    add_zero,scalar_zero,Pi.zero_apply]

/-- Original full-space propagation between two Noether vertices, with time and age in their original order. -/
def sourceSoftOrderedOperator (A B : FiberOperators) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  spatialFlow 0 (-time)*A.compLpL 2 volume*shiftFlow 0 (time-age)*B.compLpL 2 volume*spatialFlow 0 age

private theorem word_time (A B : FiberOperators) (time age : ℝ) :
    orderedWord (onlyTime A) (onlyTime B) 0 time age=
      (coordinateLeg 0).adjoint*sourceSoftOrderedOperator A B time age*coordinateLeg 0 := by
  unfold orderedWord
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp only [orderedLeft,orderedRight,onlyTime_shift,onlyTime,ite_true,sourceSoftOrderedOperator,mul_assoc]
    · intro j _ different
      simp only [orderedRight,onlyTime,if_neg different,zero_compLpL,zero_mul,mul_zero]
    · simp
  · intro i _ different
    simp only [orderedLeft,onlyTime_shift,onlyTime,if_neg different,zero_compLpL,mul_zero,zero_mul,Finset.sum_const_zero]
  · simp

/-- Both complete ordered terms use the actual full Noether operator, with the energy vertex's generated minus sign. -/
def sourceSoftNoetherOperator (branch : Fin 2) (ap an bp bn : ℂ) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  Complex.I •
    (sourceSoftOrderedOperator (((-bn) • sourceNativeOriginCanonicalFiber branch).adjoint)
        (sourceSoftNoetherReader branch ap an) age time-
      sourceSoftOrderedOperator (sourceSoftNoetherReader branch ap an)
        ((-bp) • sourceNativeOriginCanonicalFiber branch) time age)

/-- The original soft endpoint is evaluated on the same two filtered preparations, without any rest-state projection of the intermediate propagation. -/
theorem sourceSoftObservable_read (branch : Fin 2) (ap an bp bn : ℂ)
    (sideL edgeL sideR edgeR : Fin 2) (time age : ℝ) :
    sourcePreparedScatteringPair sideL edgeL sideR edgeR
      (originalTransferPair (ap • nativeBranchVector branch) (an • nativeBranchVector branch))
      (originalTransferPair (bp • nativeBranchVector branch) (bn • nativeBranchVector branch)) 0 time age=
      (sourceChargedQuantumRead sideL edgeL sideR edgeR (sourceSoftNoetherOperator branch ap an bp bn time age),0) := by
  rw [sourcePreparedScatteringPair]
  apply Prod.ext
  · change sourceActualScatteringRead sideL edgeL sideR edgeR (fieldTwoTimeKernel _ _ 0 time age)=_
    rw [fieldTwoTimeKernel,reader_time]
    simp only [originalTransferPair,frequency_time,onlyTime_adjoint,onlyTime_shift,neg_zero,word_time]
    have grouped (A B : FullMatterL2→L[ℂ]FullMatterL2) :
        Complex.I • ((coordinateLeg 0).adjoint*A*coordinateLeg 0-(coordinateLeg 0).adjoint*B*coordinateLeg 0)=
          (coordinateLeg 0).adjoint*(Complex.I • (A-B))*coordinateLeg 0 := by
      simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    rw [grouped]
    exact sourceActualScatteringRead_inserted sideL edgeL sideR edgeR _
  · change sourceActualScatteringRead sideL edgeL sideR edgeR (fieldMixedContact _ _ time)=0
    rw [fieldMixedContact,mixed_zero]
    simp only [contactWord,Pi.zero_apply,zero_compLpL,mul_zero,zero_mul,Finset.sum_const_zero,
      sourceActualScatteringRead_source,zero_apply,inner_zero_right]

def sourceSoftGaussAmplitude (leg : SourceChargedSoftLeg) (branch : Fin 2) : ℂ :=
  if branch=0 then (softCoefficient branch:ℂ)*actualGaussWeight leg.q
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window else 0

private theorem source_limit_amplitude (leg : SourceChargedSoftLeg) (branch : Fin 2) :
    sourceChargedSoftFieldLimit leg branch=sourceSoftGaussAmplitude leg branch • nativeBranchVector branch := by
  unfold sourceChargedSoftFieldLimit sourceSoftGaussAmplitude
  split_ifs <;> simp

/-- The signed actual source Gauss weights determine the observable returned by the coupled physical soft limit. -/
theorem sourceChargedSoftObservable_tendsto (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (time age : ℝ)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
      sourceChargedPhysicalResidueScattering sideL edgeL sideR edgeR legs branch n unit time age e) scaleApproach
      (𝓝 (sourceChargedQuantumRead sideL edgeL sideR edgeR
        (sourceSoftNoetherOperator branch (sourceSoftGaussAmplitude (legs 0) branch)
          (sourceSoftGaussAmplitude (legs 1) branch) (sourceSoftGaussAmplitude (legs 2) branch)
          (sourceSoftGaussAmplitude (legs 3) branch) time age),0)) := by
  have generated:=sourceChargedPhysicalResidueScattering_soft sideL edgeL sideR edgeR legs branch n unit time age nonrealL nonrealR
  simp only [sourceChargedSoftFieldsLimit,source_limit_amplitude,sourceSoftObservable_read] at generated
  exact generated

end LowEnergy.PreparationPhysicalChargedSoftObservable
