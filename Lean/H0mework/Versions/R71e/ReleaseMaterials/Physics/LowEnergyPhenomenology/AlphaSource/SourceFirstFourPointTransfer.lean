import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstWeightedChargeInsertion

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstChargeFourPointReturn
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

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

open PreparationPhysicalFirstGaugeMaterialDifference PreparationPhysicalActualUnitFourPointReturn
open PreparationPhysicalActualPolarizationResponse PreparationVacuumFullFieldRiesz

attribute [local irreducible] jointCurrent jointHessian sourceFirstCharge

open PreparationVacuumSpatialDensityTransport PreparationVacuumGradedTransport
  PreparationVacuumSourceActionJets PreparationVacuumHalfDensityFiber

/-- Original physical-frame action, including every finite-basis charge discrepancy. -/
def sourceFirstFrameInsertion (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (entries : PhysicalBasisIndex p F→PhysicalBasisIndex p F→ℂ) : H→L[ℂ]H :=
  ∑g : NativeHistoryGrade.Label,∑i : PhysicalBasisIndex p F,∑j : PhysicalBasisIndex p F,
    entries i j • (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (sourceFirstCharge (physicalFrame p F (g,j)))-
      InnerProductSpace.rankOne ℂ (sourceFirstCharge (physicalFrame p F (g,i))) (physicalFrame p F (g,j)))

private theorem rank_charge (a b : H) :
    InnerProductSpace.rankOne ℂ a b*sourceFirstCharge-sourceFirstCharge*InnerProductSpace.rankOne ℂ a b=
      InnerProductSpace.rankOne ℂ a (sourceFirstCharge b)-InnerProductSpace.rankOne ℂ (sourceFirstCharge a) b := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [sub_apply,mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul,sourceFirstCharge_pair]

private theorem scaled_charge (c : ℂ) (A : H→L[ℂ]H) :
    (c • A)*sourceFirstCharge-sourceFirstCharge*(c • A)=c • (A*sourceFirstCharge-sourceFirstCharge*A) := by
  rw [smul_mul_assoc c A sourceFirstCharge,mul_smul_comm c sourceFirstCharge A]
  exact (smul_sub c (A*sourceFirstCharge) (sourceFirstCharge*A)).symm

theorem sourceFirstFrameInsertion_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (entries : PhysicalBasisIndex p F→PhysicalBasisIndex p F→ℂ) :
    sourceAssembly p F entries*sourceFirstCharge-sourceFirstCharge*sourceAssembly p F entries=
      sourceFirstFrameInsertion p F entries := by
  simp only [sourceAssembly,sourceFirstFrameInsertion,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,
    scaled_charge,rank_charge]

/-- Native, coframe and matter fixed jets and the retained Yukawa insertion remain explicit. -/
def sourceFirstCurrentInsertion (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  sourceFirstFrameInsertion p F (fun i j=>(completeJets f p (bareTest p F i) (bareTest p F j)).first 0)+
    (sourceYJet f p F none 1 0*sourceFirstCharge-sourceFirstCharge*sourceYJet f p F none 1 0)

def sourceFirstSecondInsertion (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  sourceFirstFrameInsertion p F (fun i j=>(completeJets f p (bareTest p F i) (bareTest p F j)).second)+
    (sourceYJet f p F none 2 0*sourceFirstCharge-sourceFirstCharge*sourceYJet f p F none 2 0)

private theorem sum_charge {R : Type*} [Ring R] (A B Q : R) :
    (A+B)*Q-Q*(A+B)=(A*Q-Q*A)+(B*Q-Q*B) := by noncomm_ring

theorem sourceFirstCurrentInsertion_generated (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointCurrent p F z 0 f*sourceFirstCharge-sourceFirstCharge*jointCurrent p F z 0 f=
      sourceFirstCurrentInsertion f p F := by
  rw [jointCurrent_source,sourceCurrent_complete]
  unfold completeCurrent
  rw [sum_charge,sourceFirstFrameInsertion_generated]
  rfl

theorem sourceFirstSecondInsertion_generated (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointHessian p F z f f*sourceFirstCharge-sourceFirstCharge*jointHessian p F z f f=
      sourceFirstSecondInsertion f p F := by
  rw [jointHessian_source_diagonal,sourceContact_complete]
  unfold completeContact
  rw [sum_charge,sourceFirstFrameInsertion_generated]
  rfl

/-- The actual mixed contact is polarized from the three complete second source jets. -/
def sourceFirstMixedInsertion (f g : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  (1/2:ℝ) • (sourceFirstSecondInsertion (f+g) p F-sourceFirstSecondInsertion f p F-sourceFirstSecondInsertion g p F)

private theorem half_sum {E : Type*} [AddCommGroup E] [Module ℝ E] (a b c : E) :
    b=(1/2:ℝ) • (a+b+(b+c)-a-c) := by module

private theorem symmetric_polarization (L : Field289→L[ℝ]Field289→L[ℝ](H→L[ℂ]H)) (f g : Field289)
    (symmetric : L g f=L f g) : L f g=(1/2:ℝ) • (L (f+g) (f+g)-L f f-L g g) := by
  have expansion : L (f+g) (f+g)=L f f+L f g+(L g f+L g g) := by
    simp only [map_add,add_apply]
    abel
  have collapsed:=expansion.trans (congrArg (fun v : H→L[ℂ]H=>L f f+L f g+(v+L g g)) symmetric)
  exact (half_sum (L f f) (L f g) (L g g)).trans
    (congrArg (fun v : H→L[ℂ]H=>(1/2:ℝ) • (v-L f f-L g g)) collapsed.symm)

private theorem mixed_polarization (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (f g : Field289) :
    jointHessian p F z f g=(1/2:ℝ) •
      (jointHessian p F z (f+g) (f+g)-jointHessian p F z f f-jointHessian p F z g g) := by
  exact symmetric_polarization (jointHessian p F z) f g (jointHessian_symmetric p F z g f)

private def chargeReal : (H→L[ℂ]H)→L[ℝ](H→L[ℂ]H) :=
  (ContinuousLinearMap.mul ℝ (H→L[ℂ]H)).flip sourceFirstCharge-
    ContinuousLinearMap.mul ℝ (H→L[ℂ]H) sourceFirstCharge

theorem sourceFirstMixedInsertion_generated (f g : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointHessian p F z f g*sourceFirstCharge-sourceFirstCharge*jointHessian p F z f g=
      sourceFirstMixedInsertion f g p F := by
  have diagonal (h : Field289) : chargeReal (jointHessian p F z h h)=sourceFirstSecondInsertion h p F :=
    sourceFirstSecondInsertion_generated h p F z
  calc
    _=chargeReal (jointHessian p F z f g) := rfl
    _=chargeReal ((1/2:ℝ) • (jointHessian p F z (f+g) (f+g)-jointHessian p F z f f-jointHessian p F z g g)) :=
      congrArg chargeReal (mixed_polarization p F z f g)
    _=(1/2:ℝ) • (chargeReal (jointHessian p F z (f+g) (f+g))-
        chargeReal (jointHessian p F z f f)-chargeReal (jointHessian p F z g g)) := by
      have outer:=map_sub chargeReal
        (jointHessian p F z (f+g) (f+g)-jointHessian p F z f f) (jointHessian p F z g g)
      have inner:=map_sub chargeReal (jointHessian p F z (f+g) (f+g)) (jointHessian p F z f f)
      exact (map_smul chargeReal (1/2:ℝ) _).trans
        (congrArg (fun v : H→L[ℂ]H=>(1/2:ℝ) • v)
          (outer.trans (congrArg (fun v : H→L[ℂ]H=>v-chargeReal (jointHessian p F z g g)) inner)))
    _=_ := congrArg (fun v : H→L[ℂ]H=>(1/2:ℝ) • v)
      (congrArg₂ (fun a b : H→L[ℂ]H=>a-b)
        (congrArg₂ (fun a b : H→L[ℂ]H=>a-b) (diagonal (f+g)) (diagonal f)) (diagonal g))

/-- This is the same already evaluated full material transfer, now in each internal Green factor. -/
def sourceFirstGreenInsertion (q : PhysicalResponsePoint) (z : ℂ) : H→L[ℂ]H :=
  jointResolvent 0 q.F z 0*(jointGenerator 0 q.F 0 0*sourceFirstCharge-
    sourceFirstCharge*jointGenerator 0 q.F 0 0)*jointResolvent 0 q.F z 0

theorem sourceFirstGreenInsertion_generated (q : PhysicalResponsePoint) (z : ℂ) (nonreal : z.im≠0) :
    jointResolvent 0 q.F z 0*sourceFirstCharge-sourceFirstCharge*jointResolvent 0 q.F z 0=
      -sourceFirstGreenInsertion q z := by
  have paid:=(paidFirstInverseWard%) (jointGenerator 0 q.F 0 0) (jointGenerator 0 q.F 0 0)
    (jointResolvent 0 q.F z 0) (jointResolvent 0 q.F z 0) sourceFirstCharge z z
    (sourceMaterialInverse_left 0 q.F z nonreal) (sourceMaterialInverse_right 0 q.F z nonreal)
  simp only [sub_self,zero_smul] at paid
  exact (eq_neg_iff_add_eq_zero).mpr paid.symm

theorem sourceFirstGreenInsertion_read (q : PhysicalResponsePoint) (z : ℂ) (x y : H) :
    inner ℂ x (sourceFirstGreenInsertion q z y)=
      sourceFirstMaterialChargeRead q.F ((jointResolvent 0 q.F z 0).adjoint x) (jointResolvent 0 q.F z 0 y) := by
  simp only [sourceFirstGreenInsertion,mul_apply_eq_comp]
  rw [←ContinuousLinearMap.adjoint_inner_left,sourceFirstMaterialCharge_return]

/-- The original raw reader has the same finite source input and output restrictions. -/
theorem sourceFirstRawReader_return (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    PreparationVacuumRawJointFeedback.rawReader f p F 0 y=
      sourceApprox F (embed (sourceFirstRawCore f p (sourceTestApprox F y))) := by
  unfold PreparationVacuumRawJointFeedback.rawReader finiteRiesz
  rw [sourceTestApprox_frame]
  simp only [map_sum,map_smul]
  simp_rw [sourceApprox_frame]
  simp only [Finset.smul_sum,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have form : rawForm f p (frameTest F j) (frameTest F i) 0=
      sourcePair (frameTest F j) (sourceFirstRawCore f p (frameTest F i)) := by
    rw [rawForm_original,sourcePair_integral]
    apply integral_congr_ae
    exact Eventually.of_forall fun z=>by
      rw [←pairSample_source]
      rfl
  rw [form]
  unfold sourcePair
  rw [frameTest_embed]
  simp only [smul_smul]
  congr 1
  ring

def sourceFirstRawReaderInsertion (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  PreparationVacuumRawJointFeedback.rawReader f p F 0*sourceFirstCharge-
    sourceFirstCharge*PreparationVacuumRawJointFeedback.rawReader f p F 0

/-- Full weighted current and both true finite-frame discrepancies, before any time or Green factors. -/
theorem sourceFirstRawReaderInsertion_generated (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceFirstRawReaderInsertion f p F y=
      sourceApprox F (embed (sourceFirstRawChargeCore f p (sourceTestApprox F y)))+
      sourceApprox F (embed (sourceFirstRawCore f p
        (sourceTestApprox F (sourceFirstCharge y)-sourceFirstChargeCore (sourceTestApprox F y))))+
      (sourceApprox F (sourceFirstCharge (embed (sourceFirstRawCore f p (sourceTestApprox F y))))-
        sourceFirstCharge (sourceApprox F (embed (sourceFirstRawCore f p (sourceTestApprox F y))))) := by
  simp only [sourceFirstRawReaderInsertion,sub_apply,mul_apply_eq_comp,sourceFirstRawReader_return,map_sub]
  rw [sourceFirstChargeCore_embed]
  simp only [sourceFirstRawChargeCore,LinearMap.sub_apply,LinearMap.comp_apply,map_sub]
  abel

/-- Both ordered words and the independent Hessian acquire their actual full source insertions. -/
def sourceFirstFourPointInsertion (q : PhysicalResponsePoint) (f g : Field289) : H→L[ℂ]H :=
  sourceFirstCurrentInsertion f 0 q.F*jointResolvent 0 q.F q.z 0*jointCurrent 0 q.F q.w 0 g-
  jointCurrent 0 q.F q.z 0 f*sourceFirstGreenInsertion q q.z*jointCurrent 0 q.F q.w 0 g+
  jointCurrent 0 q.F q.z 0 f*jointResolvent 0 q.F q.z 0*sourceFirstCurrentInsertion g 0 q.F+
  sourceFirstCurrentInsertion g 0 q.F*jointResolvent 0 q.F q.w 0*jointCurrent 0 q.F q.w 0 f-
  jointCurrent 0 q.F q.w 0 g*sourceFirstGreenInsertion q q.w*jointCurrent 0 q.F q.w 0 f+
  jointCurrent 0 q.F q.w 0 g*jointResolvent 0 q.F q.w 0*sourceFirstCurrentInsertion f 0 q.F-
  sourceFirstMixedInsertion f g 0 q.F

private theorem triple_charge {R : Type*} [Ring R] (A B C Q : R) :
    (A*B*C)*Q-Q*(A*B*C)=(A*Q-Q*A)*B*C+A*(B*Q-Q*B)*C+A*B*(C*Q-Q*C) := by noncomm_ring

private theorem sum_sub_charge {R : Type*} [Ring R] (A B C Q : R) :
    (A+B-C)*Q-Q*(A+B-C)=(A*Q-Q*A)+(B*Q-Q*B)-(C*Q-Q*C) := by noncomm_ring

private theorem neg_middle {R : Type*} [Ring R] (A B C : R) :
    A*(-B)*C= -(A*B*C) := by noncomm_ring

theorem sourceFirstFourPointInsertion_generated (q : PhysicalResponsePoint) (f g : Field289)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceFourPointCore q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointCore q f g=
      sourceFirstFourPointInsertion q f g := by
  have algebra : (sourceFourPointForward q f g+sourceFourPointReverse q f g-sourceFourPointContact q f g)*sourceFirstCharge-
      sourceFirstCharge*(sourceFourPointForward q f g+sourceFourPointReverse q f g-sourceFourPointContact q f g)=
      (sourceFourPointForward q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointForward q f g)+
      (sourceFourPointReverse q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointReverse q f g)-
      (sourceFourPointContact q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointContact q f g) :=
    sum_sub_charge (sourceFourPointForward q f g) (sourceFourPointReverse q f g) (sourceFourPointContact q f g) sourceFirstCharge
  rw [sourceFourPointCore,algebra]
  simp only [sourceFourPointForward,sourceFourPointReverse,sourceFourPointContact,triple_charge,
    sourceFirstCurrentInsertion_generated,sourceFirstMixedInsertion_generated,
    sourceFirstGreenInsertion_generated q q.z left,sourceFirstGreenInsertion_generated q q.w right,
    sourceFirstFourPointInsertion,neg_middle]
  abel

end LowEnergy.PreparationPhysicalFirstChargeFourPointReturn
