import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeResidueReturn
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGradedExchangePotential

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

/-- The actual first-pole native charge acts on both original branches. -/
def sourceFirstChargeMatrix : FullMatrix := (-Complex.I) • sourceFirstBackgroundFullGenerator

def sourceFirstBrokenLie : NativeLie := sourceFirstTemporalLie-colorGenerator 2

def sourceFirstDifferenceMatrix : FullMatrix := sourceFirstChargeMatrix-sourceActualGaussChargeMatrix

theorem sourceFirstCharge_native : sourceFirstChargeMatrix= -chargeMatrix sourceFirstTemporalLie := by
  change (-Complex.I) • nativeFull sourceFirstTemporalLie= -(Complex.I • nativeFull sourceFirstTemporalLie)
  exact neg_smul _ _

/-- Full broken native direction and relative phase are retained before any external restriction. -/
theorem sourceFirstDifference_native :
    sourceFirstDifferenceMatrix= -chargeMatrix sourceFirstBrokenLie-(1/2:ℂ) • sourceRelativeChargeMatrix := by
  rw [sourceFirstDifferenceMatrix,sourceFirstCharge_native,sourceActualCharge_colourRelative]
  simp only [sourceFirstBrokenLie,chargeMatrix,map_sub,smul_sub]
  module

theorem sourceFirstCharge_branches :
    sourceFirstChargeMatrix=SourceRealScalarFock.branches (Quantum.operatorMatrix sourceFirstTemporalCharge) := by
  simp only [sourceFirstChargeMatrix,sourceFirstBackgroundFullGenerator,sourceFirstTemporalCharge,
    map_smul,sourceFirstTemporal_native]
  ext i j
  cases i <;> cases j <;>
    simp [SourceRealScalarFock.branches,Matrix.fromBlocks,Matrix.map_apply,Matrix.smul_apply,
      smul_eq_mul,map_mul]

/-- The exact whole charge is Hermitian in the source pairing. -/
theorem sourceFirstCharge_hermitian : sourceFirstChargeMatrix.conjTranspose=sourceFirstChargeMatrix := by
  rw [sourceFirstCharge_native]
  simp only [chargeMatrix,Matrix.conjTranspose_neg,Matrix.conjTranspose_smul,nativeFull_skew,
    Complex.star_def,Complex.conj_I,smul_neg,neg_smul,neg_neg]

theorem sourceFirstDifference_hermitian :
    sourceFirstDifferenceMatrix.conjTranspose=sourceFirstDifferenceMatrix := by
  rw [sourceFirstDifferenceMatrix,Matrix.conjTranspose_sub,sourceFirstCharge_hermitian,sourceActualGaussCharge_hermitian]

/-- Actual source matter columns, including their original phase, generate the full-coordinate action. -/
theorem sourceFirstCharge_coordinates (side edge : Fin 2) :
    sourceFirstChargeMatrix*ᵥsourceChargedCoordinates side edge=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge := by
  have primal:=congrArg Quantum.coordinates (sourceFirstTemporalCharge_actualColumn side edge)
  rw [←Quantum.matrix_action,map_smul] at primal
  rw [sourceFirstCharge_branches]
  unfold SourceRealScalarFock.branches sourceChargedCoordinates
  rw [Matrix.fromBlocks_mulVec]
  have left : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inl=Quantum.coordinates (sourceChargedRestriction side edge) := rfl
  have right : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inr=0 := rfl
  rw [left,right,Matrix.zero_mulVec,Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero,zero_add,primal]
  funext i
  cases i with
  | inl i=>rfl
  | inr i=>simp

theorem sourceFirstCharge_fiber (side edge : Fin 2) :
    quantized sourceFirstChargeMatrix (sourceChargedFiber side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedFiber side edge := by
  rw [sourceChargedFiber,quantized_oneParticle,sourceFirstCharge_coordinates]
  change fiberCoordinates.symm (Fermion.oneParticleLinear
    ((sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge))=_
  rw [map_smul,map_smul]
  rfl

def sourceFirstCharge : H→L[ℂ]H := lift (quantized sourceFirstChargeMatrix)

def sourceFirstDifference : H→L[ℂ]H := sourceFirstCharge-sourceActualGaussCharge

/-- Gauss preparation, not a bare-vector label, consumes the generated first-pole charge. -/
theorem sourceFirstCharge_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourceFirstCharge (sourceChargedGaussPrepared epsilon precision side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedGaussPrepared epsilon precision side edge := by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [map_smul]
  apply PiLp.ext
  intro word
  rw [sourceFirstCharge,sourceChargedGauss_action_coordinates,sourceFirstCharge_fiber]
  simp only [PiLp.smul_apply,sourceChargedGaussPrepared_coordinates,smul_smul,smul_eq_mul]

theorem sourceFirstCharge_pair (v w : H) :
    inner ℂ (sourceFirstCharge v) w=inner ℂ v (sourceFirstCharge w) := by
  apply lift_pair
  intro f g
  have H:=SourceQuantumFockGauge.quantizedFiber_adjoint sourceFirstChargeMatrix f g
  rw [sourceFirstCharge_hermitian] at H
  exact H

theorem sourceFirstDifference_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourceFirstDifference (sourceChargedGaussPrepared epsilon precision side edge)=0 := by
  change sourceFirstCharge _-sourceActualGaussCharge _=0
  rw [sourceFirstCharge_prepared,sourceActualGaussCharge_prepared,sub_self]

theorem sourceFirstDifference_pair (v w : H) :
    inner ℂ (sourceFirstDifference v) w=inner ℂ v (sourceFirstDifference w) := by
  simp only [sourceFirstDifference,sub_apply,inner_sub_left,inner_sub_right,
    sourceFirstCharge_pair,sourceActualGaussCharge_pair]

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

private theorem native_lie (a b : NativeLie) :
    nativeFull a*nativeFull b-nativeFull b*nativeFull a=nativeFull (lie a b) := by
  simp only [nativeFull,LinearMap.coe_mk,AddHom.coe_mk,Matrix.fromBlocks_multiply,
    mul_zero,zero_mul,add_zero,zero_add,blocks_sub]
  have original:=originalGauge_commutator a b
  change nativePrimal (lie a b)=nativePrimal a*nativePrimal b-nativePrimal b*nativePrimal a at original
  rw [original]
  congr 1
  rw [Matrix.map_sub _ (fun x y=>map_sub (starRingEnd ℂ) x y),Matrix.map_mul,Matrix.map_mul]

/-- The full12 connection transfer is computed; no color-only restriction is imposed on the connection. -/
theorem sourceFirstDifference_nativeTransfer (a : NativeLie) :
    nativeFull a*sourceFirstDifferenceMatrix-sourceFirstDifferenceMatrix*nativeFull a=
      Complex.I • nativeFull (lie sourceFirstBrokenLie a) := by
  rw [sourceFirstDifference_native]
  unfold chargeMatrix
  calc
    _=Complex.I • (nativeFull sourceFirstBrokenLie*nativeFull a-nativeFull a*nativeFull sourceFirstBrokenLie)+
        (1/2:ℂ) • (sourceRelativeChargeMatrix*nativeFull a-nativeFull a*sourceRelativeChargeMatrix) := by
      simp only [mul_sub,sub_mul,mul_neg,neg_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
      module
    _=_ := by rw [native_lie,sourceRelativeCharge_native,sub_self,smul_zero,add_zero]

/-- Complete CAR consumes the same nonzero native transfer before any finite projection. -/
theorem sourceFirstDifference_nativeFiber (a : NativeLie) :
    nativeFock a*quantized sourceFirstDifferenceMatrix-quantized sourceFirstDifferenceMatrix*nativeFock a=
      Complex.I • nativeFock (lie sourceFirstBrokenLie a) := by
  have H:=congrArg quantizer (sourceFirstDifference_nativeTransfer a)
  rw [paidCoframeQuantizerComm%,map_smul] at H
  exact H

/-- The original full connection of the physical chart supplies the actual native supplement. -/
theorem sourceFirstDifference_connection (v : GaussLiveMomentum.Ambient) (z : SourceCoordinateSlice) :
    connection v z*quantized sourceFirstDifferenceMatrix-quantized sourceFirstDifferenceMatrix*connection v z=
      Complex.I • nativeFock (lie sourceFirstBrokenLie (inverseL z v).1) :=
  sourceFirstDifference_nativeFiber _

end LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference
