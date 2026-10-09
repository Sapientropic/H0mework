import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonStaticField

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonCurrentStaticRead
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
local instance SourceCommonPropagationReadIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

def sourceCommonCoulombTensor (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  ∑i : Fin 3,((sourceChargedSpatialCoefficient i:ℂ)⁻¹*
    sourceSlowRead (sourceNativeSimple q n l r) ⟨i.val,by omega⟩) • sourceCommonOriginColumn i

/-- The inverse-square spatial factor retains its source angular and material tensor. -/
theorem sourceCommonStaticSimple_green (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) :
    sourceCommonStaticSimple q n l r=(spatialSquare n:ℂ)⁻¹ • sourceCommonCoulombTensor q n l r := by
  simp only [sourceCommonStaticSimple,sourceCommonCoulombTensor,sourceChargedDenominator,
    zero_pow (by decide : 2≠0),mul_zero,add_zero,mul_inv_rev,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem sourceCommonCoulombTensor_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceCommonCoulombTensor q (s • n) l r=sourceCommonCoulombTensor q n l r := by
  simp only [sourceCommonCoulombTensor,sourceNativeSimple_radial q n s positive]

/-- The duality is the original bilinear action pairing; no positive-definite field metric is inserted. -/
theorem sourceCommonNative_pair (branch : Fin 2) (current : Fin 289→ℂ) :
    (∑i : Fin 289,current i*nativeBranchVector branch i)=nativeBranchRead branch current := by
  have active : fullKernelFrame.transpose*activeProjection=fullKernelFrame.transpose := by
    have h:=congrArg Matrix.transpose fullKernel_active
    simpa only [Matrix.transpose_mul,activeProjection,projectionMatrix,Matrix.diagonal_transpose] using h
  have origin : fullKernelFrame.transpose*ᵥactiveForcing 0 current=
      fullNativeOrigin.transpose*ᵥcurrent := by
    unfold activeForcing
    rw [Matrix.mulVec_mulVec (originalReadback 0*ᵥcurrent),active]
    simp only [fullNativeOrigin,Matrix.transpose_mul,originalReadback,neg_zero,Matrix.mulVec_mulVec]
  rw [nativeBranchRead,origin]
  have single : fiveVector (Pi.single (residueIndex branch) (1:ℂ))=
      Pi.single (fiveIndex (residueIndex branch)) 1 := by
    funext i
    by_cases inside : i.val<5
    · simp [fiveVector,inside,Pi.single_apply,Fin.ext_iff,fiveIndex]
    · have outside : i≠fiveIndex (residueIndex branch) := by
        intro same
        subst i
        exact inside (residueIndex branch).isLt
      simp [fiveVector,inside,Pi.single_eq_of_ne outside]
  change current ⬝ᵥ nativeBranchVector branch=_
  rw [nativeBranchVector,single]
  simp only [Matrix.dotProduct_mulVec,fullNativeOrigin,Matrix.transpose_mul,
    Matrix.mulVec_mulVec,dotProduct_single_one]
  simp only [←Matrix.transpose_mul,Matrix.mulVec_transpose,Matrix.mul_assoc]

/-- The detector's original Gauss action returns the complete charge derivative, color contact and source deviation. -/
theorem sourceCommonDetector_gauss (q : PhysicalResponsePoint) (l r : RestStateIndex)
    (T : ℝ) (branch : Fin 2) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceCommonDetector q 0 0 l r 0 T (nativeBranchVector branch)=
      if branch=0 then actualGaussWeight q l r T else 0 := by
  rw [sourceCommonDetector_current,sourceCommonNative_pair,returnedCurrentWindow_zero,
    actualCurrent_branchRead,actualOriginWeight_completeGauss q l r T nonrealL nonrealR]

section Detector
variable (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum) (a b : RestStateIndex)
  (lambda : ℂ) (T : ℝ)
local notation "D" => sourceCommonDetector qd pDL pDR a b lambda T

/-- The observed inverse-square coefficient uses the same full action detector as the physical-frequency residue. -/
theorem sourceCommonStaticCoulomb_read (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) :
    D (sourceCommonStaticSimple q n l r)=(spatialSquare n:ℂ)⁻¹*
      D (sourceCommonCoulombTensor q n l r) := by
  rw [sourceCommonStaticSimple_green,map_smul,smul_eq_mul]

/-- Original full physical-frequency Green residue, contracted with the same full detector and source current. -/
theorem sourceCommonGreen_frequencyResidue (leg : SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun omega : ℝ=>((omega-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ)*
        D (sourceWholePhotonGreen e.val (omega/e.val^2) n*ᵥsourceChargedSoftCurrent leg branch n unit e))
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (sourceActualSoftEmitter leg branch n unit e*
        D (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n))) := by
  filter_upwards [sourceWholePhotonGreen_frequencyResidue branch n unit,
    sourceWholePhotonResidue_factor branch n unit] with e residue factor
  have read : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ=>
      D (M*ᵥsourceChargedSoftCurrent leg branch n unit e)) :=
    (D).continuous.comp (continuous_id.matrix_mulVec continuous_const)
  have generated:=read.tendsto _ |>.comp residue
  have result : sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
      sourceChargedSoftCurrent leg branch n unit e=
      sourceActualSoftEmitter leg branch n unit e •
        sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
    rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor]
    exact smul_comm _ _ _
  rw [result,map_smul,smul_eq_mul] at generated
  simpa only [Function.comp_def,Matrix.smul_mulVec,map_smul,smul_eq_mul] using generated

/-- The normalized finite photon field is observed by precisely the same action detector. -/
theorem sourceCommonSoftField_read (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀leg : SourceChargedSoftLeg,
      D (sourceChargedSoftField leg branch n unit e)=
        sourceActualSoftAmplitude leg branch n unit e*
          D (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) := by
  filter_upwards [sourceActualSoftField_factor branch n unit] with e factor
  intro leg
  rw [factor leg,map_smul,smul_eq_mul]

end Detector

/-- Both actual current families move together; the source Gauss factors remain distinct. -/
theorem sourceCommonSoftPair_limit (left right : SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (leftZ : left.q.z.im≠0) (leftW : left.q.w.im≠0)
    (rightZ : right.q.z.im≠0) (rightW : right.q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>
      sourceCommonDetector left.q (sheetLeft e.val n 0) 0
        (sourceChargedRestIndex left.sideL left.edgeL) (sourceChargedRestIndex left.sideR left.edgeR)
        (sheetLambda e.val (sourceSheet branch n unit e.val)) left.window
        (sourceChargedSoftField right branch n unit e)) scaleApproach
      (𝓝 (if branch=0 then (softCoefficient branch:ℂ)*
        actualGaussWeight right.q (sourceChargedRestIndex right.sideL right.edgeL)
          (sourceChargedRestIndex right.sideR right.edgeR) right.window*
        actualGaussWeight left.q (sourceChargedRestIndex left.sideL left.edgeL)
          (sourceChargedRestIndex left.sideR left.edgeR) left.window else 0)) := by
  have current:=actualSoftCurrent_tendsto left.q branch n unit
    (sourceChargedRestIndex left.sideL left.edgeL) (sourceChargedRestIndex left.sideR left.edgeR)
    left.window leftZ leftW
  have field:=sourceChargedSoftField_tendsto right branch n unit rightZ rightW
  have read : Continuous (fun pair : (Fin 289→ℂ)×(Fin 289→ℂ)=>∑i : Fin 289,pair.1 i*pair.2 i) := by
    fun_prop
  have generated:=read.tendsto _ |>.comp (current.prodMk_nhds field)
  have limit : (∑i : Fin 289,actualCurrent left.q 0 0
      (sourceChargedRestIndex left.sideL left.edgeL) (sourceChargedRestIndex left.sideR left.edgeR)
      0 left.window i*sourceChargedSoftFieldLimit right branch i)=
      if branch=0 then (softCoefficient branch:ℂ)*
        actualGaussWeight right.q (sourceChargedRestIndex right.sideL right.edgeL)
          (sourceChargedRestIndex right.sideR right.edgeR) right.window*
        actualGaussWeight left.q (sourceChargedRestIndex left.sideL left.edgeL)
          (sourceChargedRestIndex left.sideR left.edgeR) left.window else 0 := by
    unfold sourceChargedSoftFieldLimit
    split_ifs with h
    · simp only [Pi.smul_apply,smul_eq_mul]
      have regroup (c : ℂ) (f v : Fin 289→ℂ) : (∑i,f i*(c*v i))=c*(∑i,f i*v i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [regroup,sourceCommonNative_pair,actualCurrent_branchRead,if_pos h,
        actualOriginWeight_completeGauss left.q _ _ left.window leftZ leftW]
    · simp
  rw [limit] at generated
  simpa only [Function.comp_def,sourceCommonDetector_soft,sourceChargedSoftCurrent] using generated

end LowEnergy.PreparationPhysicalCommonCurrentStaticRead
