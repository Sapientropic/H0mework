import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColourSymbolCovariance

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGaussMaterialContact
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff



open PreparationVacuumPhysicalGaussColorTorque



open FullQuantum
open scoped Matrix.Norms.L2Operator

local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace



theorem sourceColour_flip :
    Commute (nativePrimal (colorGenerator 2)) (Quantum.operatorMatrix YangMills.FullPairing.flipMatter) := by
  have flip : YangMills.FullPairing.flipMatter=DiracExteriorMatterAction.diracMatrixMatterAction
      StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap :=
    LinearMap.ext YangMills.FullPairing.flipMatter_source
  rw [flip,GaussCoframeSpin.spinLift_source]
  exact (GaussMatterCore.spin_native_commute _ (colorGenerator 2)).symm

theorem sourceColour_inversePhase (s : ActionState) :
    Commute (nativePrimal (colorGenerator 2)) (inversePhase s) := by
  change nativePrimal (colorGenerator 2)*((-Complex.I*stateVolume s) • CoframeResponse.principalMatrix s.1)=
    ((-Complex.I*stateVolume s) • CoframeResponse.principalMatrix s.1)*nativePrimal (colorGenerator 2)
  rw [mul_smul_comm,smul_mul_assoc,(sourceColour_principal s.1).eq]

theorem sourceColour_weight (s : ActionState) :
    Commute (nativeFull (colorGenerator 2)) (sourceActionWeight s) := by
  let M : SourceMatrix := (Stage9C.Material.SpinPair.spinScale : ℂ) •
    (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s)
  have h : nativePrimal (colorGenerator 2)*M=M*nativePrimal (colorGenerator 2) := by
    unfold M
    rw [mul_smul_comm,smul_mul_assoc]
    exact congrArg (fun A : SourceMatrix=>(Stage9C.Material.SpinPair.spinScale : ℂ) • A)
      (sourceColour_flip.mul_right (sourceColour_inversePhase s)).eq
  have dual:=congrArg (fun A=>A.map (starRingEnd ℂ)) h
  rw [Matrix.map_mul,Matrix.map_mul] at dual
  change Matrix.fromBlocks (nativePrimal (colorGenerator 2)) 0 0 ((nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))*
    Matrix.fromBlocks M 0 0 (-(M.map (starRingEnd ℂ)))=
    Matrix.fromBlocks M 0 0 (-(M.map (starRingEnd ℂ)))*
      Matrix.fromBlocks (nativePrimal (colorGenerator 2)) 0 0 ((nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.mul_neg,Matrix.neg_mul,neg_zero,h,dual]

private theorem weighted_commutator {A : Type*} [Ring A] [Algebra ℂ A]
    (G W S : A) (h : G*W=W*G) :
    -(4:ℂ) • (W*(G*S-S*G))=(4*Complex.I) • ((Complex.I • G)*(W*S)-(W*S)*(Complex.I • G)) := by
  simp only [smul_mul_assoc,mul_smul_comm,←smul_sub,smul_smul]
  have coefficient : (4*Complex.I)*Complex.I=-(4:ℂ) := by
    rw [mul_assoc,Complex.I_mul_I]
    ring
  rw [coefficient]
  congr 1
  rw [mul_sub,←mul_assoc G W,h]
  simp only [mul_assoc]

theorem sourceColourRaw_material (p : PhysicalMomentum) (z : physicalChart) :
    nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState z.val)=
      (4*Complex.I) • (chargeMatrix (colorGenerator 2)*(sourceActionWeight (sourceState z.val)*sourceSymbol p (sourceState z.val))-
        (sourceActionWeight (sourceState z.val)*sourceSymbol p (sourceState z.val))*chargeMatrix (colorGenerator 2)) := by
  unfold nativeRaw
  rw [sourceColourFirst_generated]
  exact weighted_commutator _ _ _ (sourceColour_weight (sourceState z.val)).eq

private theorem quantizer_commutator (A B : FullMatrix) :
    quantizer (A*B-B*A)=quantizer A*quantizer B-quantizer B*quantizer A := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  change LowEnergy.Fermion.quantize (A*B-B*A) (fiberCoordinates f)=
    LowEnergy.Fermion.quantize A (LowEnergy.Fermion.quantize B (fiberCoordinates f))-
      LowEnergy.Fermion.quantize B (LowEnergy.Fermion.quantize A (fiberCoordinates f))
  exact LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B).symm (fiberCoordinates f)

/-- The original coframe/density weight is multiplied before full CAR quantization. -/
def sourceQuantumMaterialSymbol (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber :=
  quantizer (sourceActionWeight (sourceState z)*sourceSymbol p (sourceState z))

theorem sourceColourRaw_quantum (p : PhysicalMomentum) (z : physicalChart) :
    quantizer (nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState z.val))=
      (4*Complex.I) • (sourceColorChargeFiber*sourceQuantumMaterialSymbol p z.val-
        sourceQuantumMaterialSymbol p z.val*sourceColorChargeFiber) := by
  rw [sourceColourRaw_material,map_smul,quantizer_commutator]
  rfl


def sourceQuantumCommSample (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  pairSample z (a z) ((sourceColorChargeFiber*sourceQuantumMaterialSymbol p z-
    sourceQuantumMaterialSymbol p z*sourceColorChargeFiber) (b z))

def sourceQuantumCommForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,sourceQuantumCommSample p a b z ∂GaussHistoryHilbert.configurationMeasure

private theorem pair_complex_smul (z : SourceCoordinateSlice) (u v : FockFiber) (c : ℂ) :
    pairSample z u (c • v)=c*pairSample z u v := by
  simp only [pairSample,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem sourceNativeSample_quantum (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,z)=
      (4*Complex.I)*sourceQuantumCommSample p a b z := by
  by_cases inside : z∈tsupport a
  · rw [PreparationVacuumNativeLocalWard.nativeSample,nativeJointFiber,nativeNoetherFiber,ambientState_zero,nativeNoether_source]
    rw [sourceColourRaw_quantum p ⟨z,a.tsupport_subset inside⟩]
    change pairSample z (a z) ((4*Complex.I) •
      ((sourceColorChargeFiber*sourceQuantumMaterialSymbol p z-sourceQuantumMaterialSymbol p z*sourceColorChargeFiber) (b z)))=_
    exact pair_complex_smul z (a z) _ _
  · rw [PreparationVacuumNativeLocalWard.nativeSample_zero _ _ _ _ _ _ _ _ inside]
    simp only [sourceQuantumCommSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,mul_zero]

private theorem native_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun z=>PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,z))
      GaussHistoryHilbert.configurationMeasure :=
  parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
    (fun z=>nativeSample_near_smooth _ _ _ p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
    (PreparationVacuumNativeLocalWard.nativeSample_zero _ _ _ p a b)

theorem sourceQuantumComm_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (sourceQuantumCommSample p a b) GaussHistoryHilbert.configurationMeasure := by
  have h:=(native_integrable p a b).const_mul ((4*Complex.I)⁻¹)
  exact h.congr (Eventually.of_forall (fun z=>by
    change (4*Complex.I)⁻¹*PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,z)=_
    rw [sourceNativeSample_quantum,←mul_assoc,inv_mul_cancel₀ (by simp),one_mul]))

theorem sourceNativeForm_quantum (p : PhysicalMomentum) (a b : QuantumTest) :
    PreparationVacuumNativeLocalWard.nativeForm (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b 0=
      (4*Complex.I)*sourceQuantumCommForm p a b := by
  unfold PreparationVacuumNativeLocalWard.nativeForm sourceQuantumCommForm
  simp_rw [sourceNativeSample_quantum]
  rw [integral_const_mul]

def sourceQuantumCommReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun i j=>sourceQuantumCommForm p (frameTest F i) (frameTest F j))

attribute [local irreducible] sourceQuantumCommReader sourceQuantumCommForm
  PreparationVacuumNativeLocalWard.nativeReader PreparationVacuumNativeLocalWard.nativeForm frameVector frameTest

theorem sourceNativeReader_quantum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 p F 0=
      (4*Complex.I) • sourceQuantumCommReader p F := by
  unfold PreparationVacuumNativeLocalWard.nativeReader sourceQuantumCommReader finiteRiesz
  simp_rw [sourceNativeForm_quantum]
  simp only [Finset.smul_sum,smul_smul]


def sourceQuantumCommKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  SourceFiniteUnitary.time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    sourceQuantumCommReader pR q.F*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      SourceFiniteUnitary.time (actualC pR q.F) t

theorem sourceContactKernel_quantum_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    sourceContactKernel q pL pR t=(4*Complex.I) • sourceQuantumCommKernel q pL pR t := by
  unfold sourceContactKernel sourceQuantumCommKernel
  rw [sourceNativeReader_quantum]
  simp only [mul_smul_comm,smul_mul_assoc]

theorem sourceActualMode_quantum_deviation (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (gaugeScale/2 : ℝ) • (sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-
      sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1))=
      (4*Complex.I)*sourcePoleRead q.epsilon q.precision pL pR left right (sourceQuantumCommKernel q pL pR t)-
        sourcePoleRead q.epsilon q.precision pL pR left right (sourceDeviationKernel q pL pR t) := by
  rw [sourceActualMode_contact_deviation q pL pR left right t nonrealL nonrealR,sourceContactKernel_quantum_generated]
  simp only [map_smul,smul_eq_mul]

end LowEnergy.PreparationVacuumPhysicalGaussMaterialContact
