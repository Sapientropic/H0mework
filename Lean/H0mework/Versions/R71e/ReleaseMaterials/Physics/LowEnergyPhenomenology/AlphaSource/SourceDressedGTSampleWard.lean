import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPreparedFieldReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstMaterialVertexReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeCurrentWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalDressedGTVertexReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalFirstPoleGaugeVertex
open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalFirstGaugeMaterialDifference
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice
open GaussCoreHilbert GaussCoreDifferential GaussFockLift GaussQuantumMultiplier
open GaussLiveMomentum GaussNativeMatter GaussDensityCore GaussFockWeights GaussFockPair
open PreparationVacuumSourceActionJets PreparationVacuumActionDecomposition
open PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily PreparationVacuumNativeFieldInjection
open PreparationVacuumFieldConstraintResponse PreparationVacuumFieldCovector
open PreparationVacuumFullFieldRiesz PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatialSource MeasureTheory Filter
open scoped BigOperators InnerProductSpace ContDiff Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _

private abbrev Q : FiberOp:=quantized sourceFirstChargeMatrix

private theorem core_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstChargeCore f z=Q (f z) := rfl

private theorem pair_inner (x : SourceCoordinateSlice) (u v : FockFiber) :
    pairSample x u v=inner ℂ (weight (fun N=>complexDensity N x) u) v := by
  rw [PiLp.inner_apply]
  unfold pairSample
  apply Finset.sum_congr rfl
  intro word _
  rw [RCLike.inner_apply,weight_apply]
  change complexDensity word.card x*star (u word)*v word=
    v word*star (complexDensity word.card x*u word)
  rw [star_mul]
  have real : star (complexDensity word.card x)=complexDensity word.card x := by simp [complexDensity]
  rw [real]
  ring

/-- Number-dependent configuration density is retained before the GT pairing is moved. -/
theorem sourceGTDensity_pair (x : SourceCoordinateSlice) (u v : FockFiber) :
    pairSample x u (Q v)=pairSample x (Q u) v := by
  rw [pair_inner,pair_inner]
  exact weighted_pair _ sourceFirstChargeMatrix sourceFirstCharge_hermitian u v

private theorem quantized_gt (A : Matrix Mode Mode ℂ) :
    quantizer A*Q-Q*quantizer A=Complex.I •
      quantizer (sourceFirstBackgroundFullGenerator*A-A*sourceFirstBackgroundFullGenerator) := by
  have actual:=paidCoframeQuantizerComm% sourceFirstBackgroundFullGenerator A
  have q : Q=(-Complex.I) • quantizer sourceFirstBackgroundFullGenerator :=
    quantizer.map_smul (-Complex.I) sourceFirstBackgroundFullGenerator
  rw [q]
  rw [actual]
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
  module

/-- Full source Hamiltonian variation, including the scalar orbit and independent dual, fixes the insertion. -/
theorem sourceGTActualFiber_generated (p : PhysicalMomentum) (x : GaussHistoryHilbert.physicalChart) :
    actualFiber p x.val*Q-Q*actualFiber p x.val=Complex.I •
      quantizer (symbolFirst p (sourceState x.val) (sourceFirstGaugeState (sourceState x.val))) := by
  have valid:=PreparationVacuumNonlinearFieldCurve.sourceState_valid x
  rw [sourceFirstBackgroundSymbol p _ valid]
  exact quantized_gt (sourceSymbol p (sourceState x.val))

/-- The all-field mixed response includes the derivative of the original gauge tangent itself. -/
theorem sourceGTMixedFiber_generated (p : PhysicalMomentum) (x : GaussHistoryHilbert.physicalChart)
    (f : Field289) :
    fiberFamily f p x.val*Q-Q*fiberFamily f p x.val=
      -Complex.I • quantizer (sourceFirstBackgroundMixed p (sourceState x.val) f) := by
  have generated:=sourceFirstBackgroundCurrent_return p x f
  have q : Q=(-Complex.I) • quantized sourceFirstBackgroundFullGenerator := by
    exact quantizer.map_smul (-Complex.I) sourceFirstBackgroundFullGenerator
  rw [q,generated]
  simp only [mul_smul_comm,smul_mul_assoc,smul_neg,neg_smul,smul_sub]
  module

def sourceGTYukawa (phi : Scalar) : FiberOp :=
  quantizer (GaussYukawaCoefficient.fullMatrix (SourceQuantumScalarChart.action phi sourceFirstTemporalLie))

theorem sourceGTYukawa_generated (phi : Scalar) :
    GaussYukawaCoefficient.sourceMap phi*Q-Q*GaussYukawaCoefficient.sourceMap phi=
      Complex.I • sourceGTYukawa phi := by
  have actual:=quantized_gt (GaussYukawaCoefficient.fullMatrix phi)
  rw [show sourceFirstBackgroundFullGenerator=nativeFull sourceFirstTemporalLie from rfl,
    sourceFirstBrokenYukawa_generated] at actual
  exact actual

/-- The retained subtraction remains the literal original source coefficient. -/
def sourceGTRetained (x : SourceCoordinateSlice) : FiberOp :=
  quantizer (symbolFirst 0 (sourceState x) (sourceFirstGaugeState (sourceState x)))-
    sourceGTYukawa (GaussNativePotential.scalarField x)-
    ∑i : Fin 3,∑b : Fin 3,quantizer (sourceFirstBackgroundFullGenerator*GaussMatterCore.localMatrix i b x-
      GaussMatterCore.localMatrix i b x*sourceFirstBackgroundFullGenerator)

theorem sourceGTRetained_generated (x : GaussHistoryHilbert.physicalChart) :
    retainedCoefficient x.val*Q-Q*retainedCoefficient x.val=Complex.I • sourceGTRetained x.val := by
  have total : (∑i : Fin 3,∑b : Fin 3,quantizer (GaussMatterCore.localMatrix i b x.val))*Q-
      Q*(∑i : Fin 3,∑b : Fin 3,quantizer (GaussMatterCore.localMatrix i b x.val))=
      Complex.I • (∑i : Fin 3,∑b : Fin 3,quantizer
        (sourceFirstBackgroundFullGenerator*GaussMatterCore.localMatrix i b x.val-
          GaussMatterCore.localMatrix i b x.val*sourceFirstBackgroundFullGenerator)) := by
    simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun b _=>quantized_gt _))
  change (actualFiber 0 x.val-GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField x.val)-
    ∑i : Fin 3,∑b : Fin 3,quantizer (GaussMatterCore.localMatrix i b x.val))*Q-
    Q*(actualFiber 0 x.val-GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField x.val)-
    ∑i : Fin 3,∑b : Fin 3,quantizer (GaussMatterCore.localMatrix i b x.val))=_
  have split (A B C : FiberOp) : (A-B-C)*Q-Q*(A-B-C)=
    (A*Q-Q*A)-(B*Q-Q*B)-(C*Q-Q*C) := by
    simp only [sub_mul,mul_sub]
    abel
  rw [split,sourceGTActualFiber_generated 0 x,sourceGTYukawa_generated,total]
  simp only [sourceGTRetained,smul_sub]

private theorem pair_sub (x : SourceCoordinateSlice) (u v w : FockFiber) :
    pairSample x u (v-w)=pairSample x u v-pairSample x u w := by
  simp only [pairSample,PiLp.sub_apply,mul_sub,Finset.sum_sub_distrib]

/-- Actual sample input exchange keeps the full configuration density and uses the computed source insertion. -/
theorem sourceGTActualSample (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice)
    (x : GaussHistoryHilbert.physicalChart) :
    fiberSample (actualFiber p) a (sourceFirstChargeCore b) z x.val-
      fiberSample (actualFiber p) (sourceFirstChargeCore a) b z x.val=
      Complex.I*pairSample x.val (a z)
        (quantizer (symbolFirst p (sourceState x.val) (sourceFirstGaugeState (sourceState x.val))) (b z)) := by
  simp only [fiberSample,core_apply]
  rw [←sourceGTDensity_pair]
  have generated:=congrArg (fun A : FiberOp=>pairSample x.val (a z) (A (b z))) (sourceGTActualFiber_generated p x)
  simpa only [sub_apply,mul_apply_eq_comp,smul_apply,pair_sub,pairSample_smul_right] using generated

open Lean Elab Term in
elab "paidGTSource%" member:ident : term => do
  let (owner,scope):=if member.getId==`native_lie then
    ("_private.SourceFirstChargeDifference.",`LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference)
    else ("_private.SourceFirstDifferenceCoreWard.",`LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference)
  unless member.getId==`native_lie || member.getId==`spin_native do throwError "Unknown GT source payer"
  let wanted:=scope++member.getId
  let all:=(←getEnv).constants.toList
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith owner && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original GT source payer: {name}";return mkConst name
  | _=>throwError "Expected unique original GT source payer {wanted}"

private theorem directional_Q (a : QuantumTest) (z v : SourceCoordinateSlice) :
    fderiv ℝ (sourceFirstChargeCore a) z v=Q (fderiv ℝ a z v) := by
  have generated:=(Q.restrictScalars ℝ).hasFDerivAt.comp z
    ((a.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ ((Q.restrictScalars ℝ) ∘ a) z v=_
  rw [generated.fderiv]
  rfl

private theorem connection_Q (a : NativeLie) :
    nativeFock a*Q-Q*nativeFock a=Complex.I • nativeFock (lie sourceFirstTemporalLie a) := by
  have actual:=quantized_gt (nativeFull a)
  rw [show sourceFirstBackgroundFullGenerator=nativeFull sourceFirstTemporalLie from rfl,
    paidGTSource% native_lie] at actual
  exact actual

/-- The full inverse chart connection, rather than a restricted colour component, generates the native insertion. -/
def sourceGTNativeTransfer (v : Ambient) (x : SourceCoordinateSlice) : FiberOp :=
  nativeFock (lie sourceFirstTemporalLie (inverseL x v).1)

theorem sourceGTMomentum_sample (v : Ambient) (a : QuantumTest) (z x : SourceCoordinateSlice) :
    sampledMomentum v (sourceFirstChargeCore a) z x=
      Q (sampledMomentum v a z x)+sourceGTNativeTransfer v x (a z) := by
  simp only [sampledMomentum,directional_Q,core_apply,map_smul,map_add]
  have bracket:=congrArg (fun T : FiberOp=>T (a z)) (connection_Q (inverseL x v).1)
  change connection v x (Q (a z))-Q (connection v x (a z))=
    Complex.I • sourceGTNativeTransfer v x (a z) at bracket
  rw [sub_eq_iff_eq_add] at bracket
  rw [bracket]
  simp only [smul_add,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  abel

def sourceGTNativeSandwich (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (a b : QuantumTest) (z x : SourceCoordinateSlice) : ℂ :=
  pairSample x (sampledMomentum v a z x) ((c x:ℂ) • sourceGTNativeTransfer w x (b z))-
    pairSample x (sourceGTNativeTransfer v x (a z)) ((c x:ℂ) • sampledMomentum w b z x)

private theorem native_sandwich (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (a b : QuantumTest) (z x : SourceCoordinateSlice) :
    pairSample x (sampledMomentum v a z x) ((c x:ℂ) • sampledMomentum w (sourceFirstChargeCore b) z x)-
      pairSample x (sampledMomentum v (sourceFirstChargeCore a) z x) ((c x:ℂ) • sampledMomentum w b z x)=
      sourceGTNativeSandwich v w c a b z x := by
  rw [sourceGTMomentum_sample,sourceGTMomentum_sample,smul_add,pairSample_add_right,pairSample_add_left]
  rw [←map_smul Q (c x:ℂ),sourceGTDensity_pair]
  unfold sourceGTNativeSandwich
  ring

def sourceGTNativeSample (a b : QuantumTest) (z x : SourceCoordinateSlice) : ℂ :=
  (1/2:ℂ)*(∑v : GaussNativeForm.ScalarIndex,sourceGTNativeSandwich
    (GaussNativeForm.scalarDirection v) (GaussNativeForm.scalarDirection v) GaussNativeEnergy.scalarWeight a b z x)+
  (1/2:ℂ)*(∑v : GaussNativeForm.LieIndex,∑i : Fin 3,∑j : Fin 3,sourceGTNativeSandwich
    (GaussNativeForm.gaugeDirection i v) (GaussNativeForm.gaugeDirection j v)
      (fun x=>GaussNativeEnergy.gaugeWeight x i j) a b z x)

theorem sourceGTNativeSample_generated (a b : QuantumTest) (z x : SourceCoordinateSlice) :
    nativeSample a (sourceFirstChargeCore b) z x-nativeSample (sourceFirstChargeCore a) b z x=
      sourceGTNativeSample a b z x := by
  have potential : pairSample x (a z) ((GaussNativePotential.potential x:ℂ) • sourceFirstChargeCore b z)=
      pairSample x (sourceFirstChargeCore a z) ((GaussNativePotential.potential x:ℂ) • b z) := by
    rw [core_apply,core_apply,←map_smul Q (GaussNativePotential.potential x:ℂ),sourceGTDensity_pair]
  unfold nativeSample sourceGTNativeSample
  rw [potential]
  have eachS (v : GaussNativeForm.ScalarIndex):=native_sandwich
    (GaussNativeForm.scalarDirection v) (GaussNativeForm.scalarDirection v) GaussNativeEnergy.scalarWeight a b z x
  have eachG (v : GaussNativeForm.LieIndex) (i j : Fin 3):=native_sandwich
    (GaussNativeForm.gaugeDirection i v) (GaussNativeForm.gaugeDirection j v)
      (fun x=>GaussNativeEnergy.gaugeWeight x i j) a b z x
  have scalarSum:=Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun v _=>eachS v)
  have gaugeSum:=Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun v _=>
    Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _=>
      Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun j _=>eachG v i j)))
  simp only [Finset.sum_sub_distrib] at scalarSum gaugeSum
  linear_combination (1/2:ℂ)*scalarSum+(1/2:ℂ)*gaugeSum

private theorem momentum_core_Q (i : Fin 6) (a : QuantumTest) :
    GaussCoframeCore.momentum i (sourceFirstChargeCore a)=sourceFirstChargeCore (GaussCoframeCore.momentum i a) := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • fderiv ℝ (sourceFirstChargeCore a) z (GaussCoframeCore.coframeDirection i)=
    Q ((-Complex.I) • fderiv ℝ a z (GaussCoframeCore.coframeDirection i))
  rw [directional_Q,map_smul]

private theorem spin_core_Q (i : Fin 7) (a : QuantumTest) :
    GaussCoframeSpin.current i (sourceFirstChargeCore a)=sourceFirstChargeCore (GaussCoframeSpin.current i a) := by
  have matrix : GaussCoframeSpin.full i*sourceFirstChargeMatrix-sourceFirstChargeMatrix*GaussCoframeSpin.full i=0 := by
    rw [sourceFirstChargeMatrix]
    change _*((-Complex.I) • nativeFull sourceFirstTemporalLie)-
      ((-Complex.I) • nativeFull sourceFirstTemporalLie)*_=0
    rw [mul_smul_comm,smul_mul_assoc,paidGTSource% spin_native,sub_self]
  have full:=congrArg quantizer matrix
  rw [paidCoframeQuantizerComm%,map_zero] at full
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FiberOp=>T (a z)) (sub_eq_zero.mp full)

private theorem number_core_Q (a : QuantumTest) :
    GaussCoframeForm.number (sourceFirstChargeCore a)=sourceFirstChargeCore (GaussCoframeForm.number a) := by
  apply DFunLike.ext
  intro z
  have each (v : QuantumTest) : GaussCoframeForm.number v z=fiberNumber (v z) := by
    apply PiLp.ext
    intro word
    rw [GaussCoframeForm.number_apply,fiberNumber_apply]
  rw [each,core_apply,core_apply,each]
  exact congrArg (fun T : FiberOp=>T (a z)) (number_commute sourceFirstChargeMatrix).eq

private theorem row_core_Q (f : Field289) (c : SourceCoordinateSlice→ℝ) (a b : QuantumTest) (r : ℝ) :
    rowFieldForm f c a (sourceFirstChargeCore b) r=rowFieldForm f c (sourceFirstChargeCore a) b r := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample _ (a z) ((c _:ℂ) • Q (b z))=pairSample _ (Q (a z)) ((c _:ℂ) • b z)
  rw [←map_smul Q,sourceGTDensity_pair]

/-- The actual kinetic, spin, number and volume coframe terms consume the same full charge. -/
theorem sourceGTCoframeForm (f : Field289) (a b : QuantumTest) (r : ℝ) :
    coframeFieldForm f a (sourceFirstChargeCore b) r=coframeFieldForm f (sourceFirstChargeCore a) b r := by
  simp only [coframeFieldForm,mixedFieldForm,momentum_core_Q,spin_core_Q,number_core_Q]
  simp_rw [row_core_Q]

end LowEnergy.PreparationPhysicalDressedGTVertexReturn
