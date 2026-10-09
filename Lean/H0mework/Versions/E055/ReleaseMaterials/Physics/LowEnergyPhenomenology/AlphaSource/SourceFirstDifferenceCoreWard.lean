import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstChargeDifference

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

open PreparationVacuumPhysicalGaussColorTorque PreparationVacuumUncutYukawa
open GaussNativeForm GaussMomentumAdjoint GaussDiagonalHistory
open PreparationVacuumPhysicalHalfAxis PreparationVacuumYukawaTransport
open GaussCoframeSpin

private abbrev End := QuantumTest→ₗ[ℂ]QuantumTest
local instance : Semiring End := Module.End.instSemiring (R:=ℂ) (M:=QuantumTest)

def sourceFirstChargeCore : End :=
  GaussQuantumMultiplier.action (fun _=>sourceFirstChargeMatrix) (fun _=>contDiffAt_const)

def sourceFirstDifferenceCore : End := sourceFirstChargeCore-sourceCoframeChargeCore

theorem sourceFirstDifferenceCore_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstDifferenceCore f z=quantized sourceFirstDifferenceMatrix (f z) := by
  change quantized sourceFirstChargeMatrix (f z)-quantized sourceActualGaussChargeMatrix (f z)=_
  have H:=quantizer.map_sub sourceFirstChargeMatrix sourceActualGaussChargeMatrix
  exact (congrArg (fun T : FockFiber→L[ℂ]FockFiber=>T (f z)) H).symm

theorem sourceFirstChargeCore_embed (f : QuantumTest) :
    sourceFirstCharge (embed f)=embed (sourceFirstChargeCore f) := by
  change lift (quantized sourceFirstChargeMatrix) (embed f)=_
  rw [←paidPhaseGaugeBoundedLift%]
  exact CanonicalGradedCurrent.boundedMatrix_core sourceFirstChargeMatrix f

theorem sourceFirstDifferenceCore_embed (f : QuantumTest) :
    sourceFirstDifference (embed f)=embed (sourceFirstDifferenceCore f) := by
  change sourceFirstCharge (embed f)-sourceActualGaussCharge (embed f)=_
  rw [sourceFirstChargeCore_embed,sourceCoframeChargeCore_embed,←map_sub]
  rfl

theorem sourceFirstDifferenceCore_pair (f g : QuantumTest) :
    sourcePair (sourceFirstDifferenceCore f) g=sourcePair f (sourceFirstDifferenceCore g) := by
  have H:=sourceFirstDifference_pair (embed f) (embed g)
  rw [sourceFirstDifferenceCore_embed,sourceFirstDifferenceCore_embed] at H
  exact H

theorem sourceFirstDifference_directional (v : GaussLiveMomentum.Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (sourceFirstDifferenceCore f) z=quantized sourceFirstDifferenceMatrix (directional v f z) := by
  change fderiv ℝ (fun w=>sourceFirstDifferenceCore f w) z (direction v z)=_
  simp only [sourceFirstDifferenceCore_apply]
  exact (paidRelativeDirectional%) v (quantized sourceFirstDifferenceMatrix) f z

/-- Both original covariant and adjoint legs will consume this source-generated full12 connection insertion. -/
def sourceFirstCovariantTransfer (v : GaussLiveMomentum.Ambient) : End :=
  (covariantMomentum v).comp sourceFirstDifferenceCore-sourceFirstDifferenceCore.comp (covariantMomentum v)

theorem sourceFirstCovariantTransfer_generated (v : GaussLiveMomentum.Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstCovariantTransfer v f z=nativeFock (lie sourceFirstBrokenLie (inverseL z v).1) (f z) := by
  change (-Complex.I) • (directional v (sourceFirstDifferenceCore f) z+
    connection v z (sourceFirstDifferenceCore f z))-sourceFirstDifferenceCore (covariantMomentum v f) z=_
  rw [sourceFirstDifference_directional,sourceFirstDifferenceCore_apply,sourceFirstDifferenceCore_apply]
  change (-Complex.I) • (quantized sourceFirstDifferenceMatrix (directional v f z)+
    connection v z (quantized sourceFirstDifferenceMatrix (f z)))-
      quantized sourceFirstDifferenceMatrix ((-Complex.I) • (directional v f z+connection v z (f z)))=_
  rw [map_smul,map_add]
  have generated:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>(-Complex.I) • A (f z))
    (sourceFirstDifference_connection v z)
  simp only [sub_apply,mul_apply_eq_comp,smul_apply,smul_smul] at generated
  have scalar : (-Complex.I)*Complex.I=(1:ℂ) := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  rw [scalar,one_smul] at generated
  convert generated using 1
  module

private theorem multiply_difference (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
    GaussNativeForm.multiply c smooth (sourceFirstDifferenceCore f)=
      sourceFirstDifferenceCore (GaussNativeForm.multiply c smooth f) := by
  apply DFunLike.ext
  intro z
  simp only [GaussNativeForm.multiply_apply,sourceFirstDifferenceCore_apply,map_smul]

/-- Literal two-leg native correction; neither full inverseL connection is discarded. -/
def sourceFirstNativeSandwich (v w : GaussLiveMomentum.Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) : ℂ :=
  sourcePair (covariantMomentum v f) (GaussNativeForm.multiply c smooth (sourceFirstCovariantTransfer w g))-
    sourcePair (sourceFirstCovariantTransfer v f) (GaussNativeForm.multiply c smooth (covariantMomentum w g))

theorem sourceFirstNativeSandwich_generated (v w : GaussLiveMomentum.Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.sandwich v w c smooth (sourceFirstDifferenceCore g)-
      sourceFirstDifferenceCore (GaussNativeForm.sandwich v w c smooth g))=
        sourceFirstNativeSandwich v w c smooth f g := by
  have cov (u : GaussLiveMomentum.Ambient) (h : QuantumTest) :
      covariantMomentum u (sourceFirstDifferenceCore h)=sourceFirstDifferenceCore (covariantMomentum u h)+sourceFirstCovariantTransfer u h := by
    change _=_+(covariantMomentum u (sourceFirstDifferenceCore h)-sourceFirstDifferenceCore (covariantMomentum u h))
    abel
  change inner ℂ (embed f) (embed (_-_))=_
  rw [map_sub,inner_sub_right]
  change sourcePair f (GaussNativeForm.sandwich v w c smooth (sourceFirstDifferenceCore g))-
    sourcePair f (sourceFirstDifferenceCore (GaussNativeForm.sandwich v w c smooth g))=_
  rw [←sourceFirstDifferenceCore_pair]
  change sourcePair f (GaussMomentumAdjoint.adjoint v (GaussNativeForm.multiply c smooth (covariantMomentum w (sourceFirstDifferenceCore g))))-
    sourcePair (sourceFirstDifferenceCore f) (GaussMomentumAdjoint.adjoint v (GaussNativeForm.multiply c smooth (covariantMomentum w g)))=_
  rw [GaussNativeForm.adjoint_pair,GaussNativeForm.adjoint_pair,cov w g,cov v f,map_add,multiply_difference]
  simp only [sourcePair,map_add,inner_add_left,inner_add_right,sourceFirstNativeSandwich]
  have pair:=sourceFirstDifferenceCore_pair (covariantMomentum v f) (GaussNativeForm.multiply c smooth (covariantMomentum w g))
  simp only [sourcePair] at pair
  rw [←pair]
  ring

private def torqueRead (f g : QuantumTest) : End→ₗ[ℂ]ℂ where
  toFun A:=sourcePair f (A (sourceFirstDifferenceCore g)-sourceFirstDifferenceCore (A g))
  map_add' A B:=by
    simp only [LinearMap.add_apply,map_add,sourcePair,map_sub,inner_add_right,inner_sub_right]
    ring
  map_smul' c A:=by
    simp only [LinearMap.smul_apply,map_smul,←smul_sub,sourcePair,inner_smul_right,RingHom.id_apply,smul_eq_mul]

def sourceFirstNativeTorque (f g : QuantumTest) : ℂ :=
  (1/2:ℂ)*(∑a : GaussNativeForm.ScalarIndex,
    sourceFirstNativeSandwich (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
      GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth f g)+
  (1/2:ℂ)*(∑a : GaussNativeForm.LieIndex,∑i : Fin 3,∑j : Fin 3,
    sourceFirstNativeSandwich (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
      (fun z=>GaussNativeEnergy.gaugeWeight z i j) (GaussNativeEnergy.gaugeWeight_smooth i j) f g)

/-- The complete original native kinetic action returns both computed source-connection insertions. -/
theorem sourceFirstNativeTorque_generated (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.nativeAction (sourceFirstDifferenceCore g)-
      sourceFirstDifferenceCore (GaussNativeForm.nativeAction g))=sourceFirstNativeTorque f g := by
  change torqueRead f g GaussNativeForm.nativeAction=_
  have potential : torqueRead f g (GaussNativeForm.multiply GaussNativePotential.potential GaussNativePotential.potential_smooth)=0 := by
    change sourcePair f (_-_)=0
    rw [multiply_difference,sub_self]
    simp only [sourcePair,map_zero,inner_zero_right]
  simp only [GaussNativeForm.nativeAction,GaussNativeForm.scalarKinetic,GaussNativeForm.gaugeKinetic,
    map_add,map_smul,map_sum,potential,add_zero,smul_eq_mul]
  unfold sourceFirstNativeTorque
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact sourceFirstNativeSandwich_generated _ _ _ _ f g
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact sourceFirstNativeSandwich_generated _ _ _ _ f g

private theorem spin_native (a : Fin 7) (h : NativeLie) :
    GaussCoframeSpin.full a*nativeFull h=nativeFull h*GaussCoframeSpin.full a := by
  have primal : GaussCoframeSpin.primal a*nativePrimal h=nativePrimal h*GaussCoframeSpin.primal a :=
    GaussMatterCore.spin_native_commute _ _
  have dual:=congrArg (fun A : SourceMatrix=>A.map (starRingEnd ℂ)) primal
  rw [Matrix.map_mul,Matrix.map_mul] at dual
  by_cases low : a.val<3
  · simp only [GaussCoframeSpin.full,low,ite_true,nativeFull,LinearMap.coe_mk,AddHom.coe_mk,
      Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add]
    congr 1
  · simp only [GaussCoframeSpin.full,low,ite_false,nativeFull,LinearMap.coe_mk,AddHom.coe_mk,
      Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,neg_mul,mul_neg,neg_zero]
    congr 1
    exact congrArg Neg.neg dual

theorem sourceFirstDifference_spin (a : Fin 7) :
    sourceFirstDifferenceMatrix*GaussCoframeSpin.full a=GaussCoframeSpin.full a*sourceFirstDifferenceMatrix := by
  have relative : sourceRelativeChargeMatrix*GaussCoframeSpin.full a=GaussCoframeSpin.full a*sourceRelativeChargeMatrix :=
    (paidRelativeCore% relative_blocks) _ _
  rw [sourceFirstDifference_native]
  simp only [chargeMatrix,sub_mul,mul_sub,neg_mul,mul_neg,smul_mul_assoc,mul_smul_comm,
    spin_native,relative]

theorem sourceFirstDifference_spinFiber (a : Fin 7) :
    Commute (quantized sourceFirstDifferenceMatrix) (quantized (GaussCoframeSpin.full a)) := by
  have H:=congrArg quantizer (sub_eq_zero.mpr (sourceFirstDifference_spin a))
  rw [paidCoframeQuantizerComm%,map_zero] at H
  exact sub_eq_zero.mp H

private theorem spin_core (a : Fin 7) : Commute sourceFirstDifferenceCore (GaussCoframeSpin.current a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change sourceFirstDifferenceCore (GaussCoframeSpin.current a f) z=GaussCoframeSpin.current a (sourceFirstDifferenceCore f) z
  rw [sourceFirstDifferenceCore_apply]
  change quantized sourceFirstDifferenceMatrix (quantized (GaussCoframeSpin.full a) (f z))=
    quantized (GaussCoframeSpin.full a) (sourceFirstDifferenceCore f z)
  rw [sourceFirstDifferenceCore_apply]
  exact congrArg (fun T : FockFiber→L[ℂ]FockFiber=>T (f z)) (sourceFirstDifference_spinFiber a).eq

private theorem number_core : Commute sourceFirstDifferenceCore GaussCoframeForm.number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have each (g : QuantumTest) : GaussCoframeForm.number g z=SourceQuantumFockGauge.fiberNumber (g z) := by
    apply PiLp.ext
    intro word
    rw [GaussCoframeForm.number_apply,SourceQuantumFockGauge.fiberNumber_apply]
  change sourceFirstDifferenceCore (GaussCoframeForm.number f) z=GaussCoframeForm.number (sourceFirstDifferenceCore f) z
  rw [sourceFirstDifferenceCore_apply,each,each,sourceFirstDifferenceCore_apply]
  exact congrArg (fun T : FockFiber→L[ℂ]FockFiber=>T (f z))
    (GaussQuantumMultiplier.number_commute sourceFirstDifferenceMatrix).symm.eq

private theorem coframe_derivative (v : SourceCoordinateSlice) (f : QuantumTest) :
    GaussCoframeCore.derivative v (sourceFirstDifferenceCore f)=
      sourceFirstDifferenceCore (GaussCoframeCore.derivative v f) := by
  apply DFunLike.ext
  intro z
  rw [sourceFirstDifferenceCore_apply]
  change (TestFunction.lineDerivCLM (n:=⊤) (k:=⊤) ℂ v (sourceFirstDifferenceCore f)) z=
    quantized sourceFirstDifferenceMatrix ((TestFunction.lineDerivCLM (n:=⊤) (k:=⊤) ℂ v f) z)
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp),TestFunction.lineDerivCLM_apply_of_le (by simp),
    (sourceFirstDifferenceCore f).contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv,
    f.contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv]
  have derivative:=((quantized sourceFirstDifferenceMatrix).restrictScalars ℝ).hasFDerivAt.comp z
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change (fderiv ℝ (fun w=>sourceFirstDifferenceCore f w) z) v=_
  simp only [sourceFirstDifferenceCore_apply]
  change (fderiv ℝ (((quantized sourceFirstDifferenceMatrix).restrictScalars ℝ) ∘ f) z) v=_
  rw [derivative.fderiv]
  rfl

private theorem coframe_momentum (i : Fin 6) : Commute sourceFirstDifferenceCore (GaussCoframeCore.momentum i) := by
  apply Commute.symm
  apply LinearMap.ext
  intro f
  change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (sourceFirstDifferenceCore f)=
    sourceFirstDifferenceCore ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f)
  rw [coframe_derivative,map_smul]

private theorem coframe_adjoint (i : Fin 6) : Commute sourceFirstDifferenceCore (GaussCoframeCore.adjoint i) := by
  apply Commute.symm
  apply LinearMap.ext
  intro g
  have pair (f : QuantumTest) :
      sourcePair f (GaussCoframeCore.adjoint i (sourceFirstDifferenceCore g))=
        sourcePair f (sourceFirstDifferenceCore (GaussCoframeCore.adjoint i g)) := by
    rw [GaussCoframeKinetic.adjoint_pair,←sourceFirstDifferenceCore_pair]
    have commute:=LinearMap.congr_fun (coframe_momentum i).eq f
    change sourceFirstDifferenceCore (GaussCoframeCore.momentum i f)=
      GaussCoframeCore.momentum i (sourceFirstDifferenceCore f) at commute
    rw [commute,←GaussCoframeKinetic.adjoint_pair,sourceFirstDifferenceCore_pair]
  apply sub_eq_zero.mp
  apply embed_injective
  rw [map_zero]
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  let d:=GaussCoframeCore.adjoint i (sourceFirstDifferenceCore g)-sourceFirstDifferenceCore (GaussCoframeCore.adjoint i g)
  have paid:=pair d
  change sourcePair d d=0
  unfold d sourcePair
  rw [map_sub,inner_sub_right]
  simpa only [sourcePair,d,map_sub] using sub_eq_zero.mpr paid

private theorem coframe_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute sourceFirstDifferenceCore (GaussCoframeForm.mixed i a c smooth) := by
  apply LinearMap.ext
  intro f
  have spin (v : QuantumTest):=LinearMap.congr_fun (spin_core a).eq v
  have scalar (v : QuantumTest):=(multiply_difference c smooth v).symm
  have momentum (v : QuantumTest):=LinearMap.congr_fun (coframe_momentum i).eq v
  have adjoint (v : QuantumTest):=LinearMap.congr_fun (coframe_adjoint i).eq v
  simp only [Module.End.mul_apply] at spin momentum adjoint
  simp only [Module.End.mul_apply,GaussCoframeForm.mixed,LinearMap.smul_apply,LinearMap.add_apply,
    LinearMap.comp_apply,map_smul,map_add,spin,scalar,momentum,adjoint]

/-- The original coframe action, including its spin and number corrections, genuinely commutes with D. -/
theorem sourceFirstDifference_coframeCore : Commute sourceFirstDifferenceCore GaussCoframeForm.coframeAction := by
  have spin (a : Fin 7) (v : QuantumTest):=LinearMap.congr_fun (spin_core a).eq v
  have scalar (c : SourceCoordinateSlice→ℝ) (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : QuantumTest):=
    (multiply_difference c smooth v).symm
  have momentum (i : Fin 6) (v : QuantumTest):=LinearMap.congr_fun (coframe_momentum i).eq v
  have adjoint (i : Fin 6) (v : QuantumTest):=LinearMap.congr_fun (coframe_adjoint i).eq v
  have number (v : QuantumTest):=LinearMap.congr_fun number_core.eq v
  have mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
      (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : QuantumTest):=
    LinearMap.congr_fun (coframe_mixed i a c smooth).eq v
  simp only [Module.End.mul_apply] at spin momentum adjoint number mixed
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,GaussCoframeForm.coframeAction,GaussCoframeKinetic.kinetic,
    GaussCoframeKinetic.term,GaussCoframeForm.currentAction,GaussCoframeForm.spinSquare,
    GaussCoframeForm.numberShift,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.comp_apply,map_add,map_smul,map_sum,spin,scalar,momentum,adjoint,number,mixed]

/-- The original matter coefficient retains its full native connection bracket. -/
theorem sourceFirstDifference_matterMatrix (b : Fin 3) (a : NativeLie) :
    GaussMatterCore.matrixTerm b a*sourceFirstDifferenceMatrix-sourceFirstDifferenceMatrix*GaussMatterCore.matrixTerm b a=
      Complex.I • GaussMatterCore.matrixTerm b (lie sourceFirstBrokenLie a) := by
  change (Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b)*nativeFull a)*sourceFirstDifferenceMatrix-
    sourceFirstDifferenceMatrix*(Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b)*nativeFull a)=_
  calc
    _=Complex.I • (GaussCoframeSpin.full (Fin.castAdd 4 b)*
        (nativeFull a*sourceFirstDifferenceMatrix-sourceFirstDifferenceMatrix*nativeFull a)) := by
      simp only [smul_mul_assoc,mul_smul_comm,smul_sub,mul_sub]
      congr 1
      · rw [mul_assoc]
      · rw [←mul_assoc sourceFirstDifferenceMatrix,sourceFirstDifference_spin,mul_assoc]
    _=_ := by
      rw [sourceFirstDifference_nativeTransfer]
      change _=Complex.I • ((Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b))*nativeFull (lie sourceFirstBrokenLie a))
      rw [mul_smul_comm,smul_mul_assoc]

def sourceFirstMatterTransferMatrix (z : SourceCoordinateSlice) : FullMatrix :=
  ∑i : Fin 3,∑b : Fin 3,(GaussMatterCore.coefficient i b z:ℂ) •
    GaussMatterCore.matrixTerm b (lie sourceFirstBrokenLie (GaussNativePotential.connectionField z i))

def sourceFirstMatterTransferCore : End :=
  GaussMatterCore.matterAction.comp sourceFirstDifferenceCore-sourceFirstDifferenceCore.comp GaussMatterCore.matterAction

theorem sourceFirstMatterTransfer_generated (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstMatterTransferCore f z=Complex.I • quantized (sourceFirstMatterTransferMatrix z) (f z) := by
  have matrix (i b : Fin 3) :
      GaussMatterCore.localMatrix i b z*sourceFirstDifferenceMatrix-sourceFirstDifferenceMatrix*GaussMatterCore.localMatrix i b z=
        Complex.I • ((GaussMatterCore.coefficient i b z:ℂ) •
          GaussMatterCore.matrixTerm b (lie sourceFirstBrokenLie (GaussNativePotential.connectionField z i))) := by
    simp only [GaussMatterCore.localMatrix,smul_mul_assoc,mul_smul_comm,←smul_sub,
      sourceFirstDifference_matterMatrix,smul_smul]
    rw [mul_comm]
  have fiber (i b : Fin 3) := congrArg quantizer (matrix i b)
  simp only [paidCoframeQuantizerComm%,map_smul] at fiber
  change (∑i : Fin 3,∑b : Fin 3,quantized (GaussMatterCore.localMatrix i b z) (sourceFirstDifferenceCore f z))-
    sourceFirstDifferenceCore (GaussMatterCore.matterAction f) z=_
  rw [sourceFirstDifferenceCore_apply,sourceFirstDifferenceCore_apply]
  change (∑i : Fin 3,∑b : Fin 3,quantizer (GaussMatterCore.localMatrix i b z) (quantizer sourceFirstDifferenceMatrix (f z)))-
    quantizer sourceFirstDifferenceMatrix (∑i : Fin 3,∑b : Fin 3,quantizer (GaussMatterCore.localMatrix i b z) (f z))=
      Complex.I • quantizer (sourceFirstMatterTransferMatrix z) (f z)
  simp only [map_sum,←Finset.sum_sub_distrib,sourceFirstMatterTransferMatrix,map_smul,sum_apply,smul_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun T : FockFiber→L[ℂ]FockFiber=>T (f z)) (fiber i b)

/-- The complete original material core has the two computed native legs and the actual full-connection matter insertion. -/
theorem sourceFirstDifference_diagonalForm (f g : QuantumTest) :
    sourcePair f (GaussDiagonalHistory.diagonalAction (sourceFirstDifferenceCore g)-
      sourceFirstDifferenceCore (GaussDiagonalHistory.diagonalAction g))=
      sourceFirstNativeTorque f g+sourcePair f (sourceFirstMatterTransferCore g) := by
  have coframe:=LinearMap.congr_fun sourceFirstDifference_coframeCore.eq g
  change sourceFirstDifferenceCore (GaussCoframeForm.coframeAction g)=
    GaussCoframeForm.coframeAction (sourceFirstDifferenceCore g) at coframe
  change sourcePair f ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction) (sourceFirstDifferenceCore g)-
    sourceFirstDifferenceCore ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction) g))=_
  simp only [LinearMap.add_apply,map_add,coframe,sourcePair,map_add,map_sub,inner_add_right,inner_sub_right]
  have native:=sourceFirstNativeTorque_generated f g
  simp only [sourcePair,map_sub,inner_sub_right] at native
  change _=sourceFirstNativeTorque f g+sourcePair f (GaussMatterCore.matterAction (sourceFirstDifferenceCore g)-
    sourceFirstDifferenceCore (GaussMatterCore.matterAction g))
  simp only [sourcePair,map_sub,inner_sub_right]
  linear_combination native

private theorem yukawa_primal (phi : SourceQuantumScalarChart.Scalar) :
    GaussYukawaCoefficient.primal phi=(Stage9C.Material.SpinPair.lapse:ℂ) •
      (spinCoordinates diracGammaZero*PreparationVacuumGaugeSourceInjection.scalarLinear phi) := by
  change Quantum.operatorMatrix ((Stage9C.Material.SpinPair.lapse:ℂ) •
    (diracMatrixMatterAction diracGammaZero).comp (StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction
      (StageNineDynamicBreakingVacuum.scalarCoordinateEquiv.symm phi)))=_
  rw [map_smul,Quantum.matrix_composition]
  rfl

private theorem yukawa_native_primal (a : NativeLie) (phi : SourceQuantumScalarChart.Scalar) :
    nativePrimal a*GaussYukawaCoefficient.primal phi-GaussYukawaCoefficient.primal phi*nativePrimal a=
      GaussYukawaCoefficient.primal (SourceQuantumScalarChart.action phi a) := by
  rw [yukawa_primal,yukawa_primal,originalScalar_commutator]
  simp only [mul_smul_comm,smul_mul_assoc,←smul_sub]
  congr 1
  rw [←mul_assoc (nativePrimal a),originalSpin_internal_commute]
  noncomm_ring

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

/-- The original full independent-dual Yukawa Hamiltonian is covariant under the actual broken direction. -/
theorem sourceFirstBrokenYukawa_generated (a : NativeLie) (phi : SourceQuantumScalarChart.Scalar) :
    nativeFull a*GaussYukawaCoefficient.fullMatrix phi-GaussYukawaCoefficient.fullMatrix phi*nativeFull a=
      GaussYukawaCoefficient.fullMatrix (SourceQuantumScalarChart.action phi a) := by
  change Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))*
      Matrix.fromBlocks (GaussYukawaCoefficient.primal phi) 0 0 (-((GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)))-
    Matrix.fromBlocks (GaussYukawaCoefficient.primal phi) 0 0 (-((GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)))*
      Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))=
    Matrix.fromBlocks (GaussYukawaCoefficient.primal (SourceQuantumScalarChart.action phi a)) 0 0
      (-((GaussYukawaCoefficient.primal (SourceQuantumScalarChart.action phi a)).map (starRingEnd ℂ)))
  simp only [Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,mul_neg,neg_mul,neg_zero,blocks_sub]
  rw [←yukawa_native_primal a phi]
  congr 1
  rw [Matrix.map_sub _ (fun x y=>map_sub (starRingEnd ℂ) x y),Matrix.map_mul,Matrix.map_mul]
  abel

theorem sourceFirstDifference_yukawaMatrix (phi : SourceQuantumScalarChart.Scalar) :
    GaussYukawaCoefficient.fullMatrix phi*sourceFirstDifferenceMatrix-sourceFirstDifferenceMatrix*GaussYukawaCoefficient.fullMatrix phi=
      Complex.I • GaussYukawaCoefficient.fullMatrix (SourceQuantumScalarChart.action phi sourceFirstBrokenLie) := by
  have relative : sourceRelativeChargeMatrix*GaussYukawaCoefficient.fullMatrix phi=
      GaussYukawaCoefficient.fullMatrix phi*sourceRelativeChargeMatrix := (paidRelativeCore% relative_blocks) _ _
  rw [sourceFirstDifference_native]
  unfold chargeMatrix
  calc
    _=Complex.I • (nativeFull sourceFirstBrokenLie*GaussYukawaCoefficient.fullMatrix phi-
        GaussYukawaCoefficient.fullMatrix phi*nativeFull sourceFirstBrokenLie)+
      (1/2:ℂ) • (sourceRelativeChargeMatrix*GaussYukawaCoefficient.fullMatrix phi-
        GaussYukawaCoefficient.fullMatrix phi*sourceRelativeChargeMatrix) := by
      simp only [mul_sub,sub_mul,mul_neg,neg_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
      module
    _=_ := by rw [sourceFirstBrokenYukawa_generated,relative,sub_self,smul_zero,add_zero]

def sourceFirstRetainedDifferenceCore (phi : CanonicalGradedLocalCurrent.Localizer) : End :=
  (sourceRetainedYukawaCore phi).comp sourceFirstDifferenceCore-sourceFirstDifferenceCore.comp (sourceRetainedYukawaCore phi)

private theorem retained_apply (phi : CanonicalGradedLocalCurrent.Localizer) (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceRetainedYukawaCore phi f z=(phi z:ℂ) • GaussYukawaCoefficient.sourceMap
      (GaussNativePotential.scalarField (PreparationVacuumFieldConstraintResponse.fieldCoordinateCurve 0 0 z)) (f z) := rfl

theorem sourceFirstRetainedDifference_generated (phi : CanonicalGradedLocalCurrent.Localizer) (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstRetainedDifferenceCore phi f z=(phi z:ℂ) • (Complex.I •
      quantized (GaussYukawaCoefficient.fullMatrix (SourceQuantumScalarChart.action (GaussNativePotential.scalarField z) sourceFirstBrokenLie)) (f z)) := by
  have H:=congrArg quantizer (sourceFirstDifference_yukawaMatrix (GaussNativePotential.scalarField z))
  rw [paidCoframeQuantizerComm%,map_smul] at H
  change (phi z:ℂ) • (GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField (PreparationVacuumFieldConstraintResponse.fieldCoordinateCurve 0 0 z))
    (sourceFirstDifferenceCore f z))-sourceFirstDifferenceCore (sourceRetainedYukawaCore phi f) z=_
  rw [sourceFirstDifferenceCore_apply,sourceFirstDifferenceCore_apply,retained_apply,
    PreparationVacuumGradedTransport.curve_zero]
  have same : GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z)=
      quantized (GaussYukawaCoefficient.fullMatrix (GaussNativePotential.scalarField z)) := rfl
  rw [same]
  rw [map_smul,←smul_sub]
  exact congrArg (fun T : FockFiber→L[ℂ]FockFiber=>(phi z:ℂ) • T (f z)) H

theorem sourceFirstRetainedDifference_return (phi : CanonicalGradedLocalCurrent.Localizer) (f : QuantumTest) :
    (uncutOperator 0 phi 0*sourceFirstDifference-sourceFirstDifference*uncutOperator 0 phi 0) (embed f)=
      embed (sourceFirstRetainedDifferenceCore phi f) := by
  simp only [sub_apply,mul_apply_eq_comp,sourceFirstDifferenceCore_embed,uncutOperator_core]
  change embed (sourceRetainedYukawaCore phi (sourceFirstDifferenceCore f))-
    embed (sourceFirstDifferenceCore (sourceRetainedYukawaCore phi f))=_
  rw [←map_sub]
  rfl

end LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference
