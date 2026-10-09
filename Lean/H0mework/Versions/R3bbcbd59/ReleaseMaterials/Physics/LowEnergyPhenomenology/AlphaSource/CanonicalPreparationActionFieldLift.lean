import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActionStateRestriction
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugePreparedPorts

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumActionFieldLift
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearFieldCurve PreparationVacuumGradedTransport
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
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

def sourceSymbol (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) : FullMatrix :=
  fourierLinear p (stateHamiltonian s)

def symbolFirst (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState) : FullMatrix :=
  fderiv ℝ (sourceSymbol p) s v

def symbolSecond (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v w : ActionState) : FullMatrix :=
  (fderiv ℝ (fderiv ℝ (sourceSymbol p)) s w) v

theorem sourceSymbol_smooth (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (sourceSymbol p) s :=
  (fourierLinear p).toContinuousLinearMap.contDiff.contDiffAt.comp s
    (contDiffAt_pi.mpr fun i=>stateHamiltonian_smooth s valid.1 valid.2 i)

theorem symbolFirst_smooth (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (fun w=>symbolFirst p w v) s :=
  ((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

lemma state_line (s v : ActionState) : HasDerivAt (fun r : ℝ=>s+r • v) v 0 :=by
  convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add s using 1
  simp only [id_eq,one_smul]

theorem symbol_first_generated (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState) (valid : s∈validStates) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (s+r • v)) (symbolFirst p s v) 0 :=by
  have h:=(sourceSymbol_smooth p s valid).differentiableAt (by simp) |>.hasFDerivAt
  convert! h.comp_hasDerivAt_of_eq 0 (state_line s v) (by simp) using 1

theorem symbol_second_generated (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v w : ActionState) (valid : s∈validStates) :
    HasDerivAt (fun r : ℝ=>symbolFirst p (s+r • w) v) (symbolSecond p s v w) 0 :=by
  have first:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have path:=first.comp_hasDerivAt_of_eq 0 (state_line s w) (by simp)
  have generated:=path.clm_apply (hasDerivAt_const (0:ℝ) v)
  convert! generated using 1
  simp only [symbolSecond,map_zero,zero_add,add_zero]

theorem symbol_line_first (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState) (r : ℝ)
    (valid : s+r • v∈validStates) :
    HasDerivAt (fun t : ℝ=>sourceSymbol p (s+t • v)) (symbolFirst p (s+r • v) v) r :=by
  have line : HasDerivAt (fun t : ℝ=>s+t • v) v r :=by
    convert! ((hasDerivAt_id r).smul_const v).const_add s using 1
    simp only [one_smul]
  have native:=(sourceSymbol_smooth p (s+r • v) valid).differentiableAt (by simp) |>.hasFDerivAt
  exact native.comp_hasDerivAt r line

theorem symbol_line_second (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState) (valid : s∈validStates) :
    HasDerivAt (deriv (fun t : ℝ=>sourceSymbol p (s+t • v))) (symbolSecond p s v v) 0 :=by
  have near : ∀ᶠr in 𝓝 (0:ℝ),s+r • v∈validStates :=
    (state_line s v).continuousAt.preimage_mem_nhds (by simpa using validStates_open.mem_nhds valid)
  apply (symbol_second_generated p s v v valid).congr_of_eventuallyEq
  exact near.mono fun r hr=>(symbol_line_first p s v r hr).deriv

theorem symbolFirst_field (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) :
    symbolFirst p s (fieldDirection f)= -fourierLinear p (fun i=>statePhase s*densityVariation f s i) :=by
  have first:=symbol_first_generated p s (fieldDirection f) valid
  have native:=hasDerivAt_pi.mpr (fun i=>state_forcing_generated f s valid.1 valid.2 i)
  have lifted:=(fourierLinear p).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 native
  have eq:=first.unique lifted
  change symbolFirst p s (fieldDirection f)=fourierLinear p (-(fun i=>statePhase s*densityVariation f s i)) at eq
  rw [map_neg] at eq
  exact eq

theorem symbolFirst_actual (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    quantizer (symbolFirst p (sourceState z.val) (fieldDirection f))= -fiberFamily f p z.val :=by
  have h:=symbolFirst_field f p (sourceState z.val)
    ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have lifted:=congrArg quantizer h
  rw [map_neg] at lifted
  exact lifted

theorem coordinate_symbol_first (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (fun x=>sourceSymbol p (sourceState x)) z.val h=symbolFirst p (sourceState z.val) (sliceState h) :=by
  have outer:=(sourceSymbol_smooth p (sourceState z.val) ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩).differentiableAt (by simp)
  have inner:=sourceState_smooth.differentiable (by simp) |>.differentiableAt (x:=z.val)
  have derivative:=outer.hasFDerivAt.comp z.val inner.hasFDerivAt
  have identity:=congrArg (fun D : SourceCoordinateSlice →L[ℝ] FullMatrix=>D h) derivative.fderiv
  rw [sourceState_fderiv] at identity
  exact identity

theorem first_state_split (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) :
    symbolFirst p (sourceState z) (fieldDirection f)=
      symbolFirst p (sourceState z) (sliceState (fieldVector f z))+
      symbolFirst p (sourceState z) (complement f z) :=by
  unfold symbolFirst complement
  rw [map_sub]
  abel

theorem second_state_split (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) :
    symbolSecond p (sourceState z) (fieldDirection f) (fieldDirection f)=
      symbolSecond p (sourceState z) (sliceState (fieldVector f z)) (sliceState (fieldVector f z))+
      symbolSecond p (sourceState z) (sliceState (fieldVector f z)) (complement f z)+
      symbolSecond p (sourceState z) (complement f z) (sliceState (fieldVector f z))+
      symbolSecond p (sourceState z) (complement f z) (complement f z) :=by
  have split : fieldDirection f=sliceState (fieldVector f z)+complement f z :=by rw [complement];abel
  conv_lhs=>rw [split]
  simp only [symbolSecond,map_add,add_apply]
  abel

def symbolSquare (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) (r s : ℝ) : FullMatrix :=
  sourceSymbol p (stateSquare f z r s)

theorem symbolSquare_coordinate (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) (r : ℝ) :
    symbolSquare f p z r 0=sourceSymbol p (sourceState (fieldCoordinateCurve f r z)) :=by
  rw [symbolSquare,stateSquare_coordinate]

theorem symbolSquare_ambient (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) (r : ℝ) :
    symbolSquare f p z r r=sourceSymbol p (sourceState z+r • fieldDirection f) :=by
  rw [symbolSquare,stateSquare_ambient]

theorem ambient_first_generated (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r=>symbolSquare f p z.val r r) (symbolFirst p (sourceState z.val) (fieldDirection f)) 0 :=by
  have h:=symbol_first_generated p (sourceState z.val) (fieldDirection f)
    ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r=>symbolSquare_ambient f p z.val r)

theorem ambient_second_generated (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (deriv (fun r : ℝ=>symbolSquare f p z.val r r))
      (symbolSecond p (sourceState z.val) (fieldDirection f) (fieldDirection f)) 0 :=by
  have same : (fun r : ℝ=>symbolSquare f p z.val r r)=ᶠ[𝓝 (0:ℝ)]
      (fun r=>sourceSymbol p (sourceState z.val+r • fieldDirection f)) :=
    Filter.Eventually.of_forall fun r=>symbolSquare_ambient f p z.val r
  exact (symbol_line_second p (sourceState z.val) (fieldDirection f)
    ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩).congr_of_eventuallyEq same.deriv

def liftedDifference (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) (r : ℝ) : FullMatrix :=
  symbolSquare f p z r r-symbolSquare f p z r 0

theorem liftedDifference_first (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (liftedDifference f p z.val) (symbolFirst p (sourceState z.val) (complement f z.val)) 0 :=by
  have first:=ambient_first_generated f p z
  have coord:=symbol_first_generated p (sourceState z.val) (sliceState (fieldVector f z.val))
    ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have identity (r : ℝ) : symbolSquare f p z.val r 0=
      sourceSymbol p (sourceState z.val+r • sliceState (fieldVector f z.val)) :=by
    rw [symbolSquare_coordinate,fieldCoordinateCurve,sourceState_affine]
  have h:=(first.sub (coord.congr_of_eventuallyEq (Filter.Eventually.of_forall identity)))
  convert! h using 1
  rw [first_state_split]
  abel

-- The original action normalization is retained BEFORE full independent-dual quantization.
def rawActionSymbol (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) : FullMatrix :=
  rawFourier p (fun i=>densityActionMatrix*densityVariation f s i)

theorem rawActionSymbol_smooth (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) : ContDiffAt ℝ ∞ (rawActionSymbol f p) s :=
  (rawFourier p).toContinuousLinearMap.contDiff.contDiffAt.comp s
    (contDiffAt_pi.mpr fun i=>contDiffAt_const.mul (densityVariation_smooth f s valid.1 valid.2 i))

theorem rawActionSymbol_source (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) :
    rawActionSymbol f p s= -(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection f)) :=by
  rw [rawActionSymbol,raw_source_weight f p s valid.1 valid.2,symbolFirst_field f p s valid]
  simp only [mul_neg,smul_neg,neg_smul,neg_neg]

theorem rawActionSymbol_actual (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) :
    quantizer (rawActionSymbol f p (sourceState z))=rawStateFiber f p (sourceState z) :=rfl

def actionWeightFirst (s v : ActionState) : FullMatrix:=fderiv ℝ sourceActionWeight s v

def rawActionContact (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState) : FullMatrix :=
  fderiv ℝ (rawActionSymbol f p) s v

def branchesLinear : SourceMatrix →ₗ[ℝ] FullMatrix where
  toFun:=SourceRealScalarFock.branches
  map_add' A B:=by
    ext u v;cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.fromBlocks,Matrix.map_apply,add_comm]
  map_smul' r A:=by
    ext u v;cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.fromBlocks,Matrix.map_apply]

theorem sourceActionWeight_smooth (s : ActionState) (valid : s∈validStates) : ContDiffAt ℝ ∞ sourceActionWeight s :=by
  have inversePhaseSmooth : ContDiffAt ℝ ∞ inversePhase s :=
    (contDiffAt_const.mul (stateVolume_smooth s valid.1)).smul
      ((principalMatrix_smooth s.1 valid.1).comp s contDiffAt_fst)
  have inside : ContDiffAt ℝ ∞ (fun t=>(Stage9C.Material.SpinPair.spinScale:ℂ) •
      (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase t)) s :=
    (contDiffAt_const.mul inversePhaseSmooth).const_smul _
  exact branchesLinear.toContinuousLinearMap.contDiff.contDiffAt.comp s inside

theorem rawActionContact_generated (f : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s v : ActionState)
    (valid : s∈validStates) :
    rawActionContact f p s v= -(4:ℂ) •
      (actionWeightFirst s v*symbolFirst p s (fieldDirection f)+sourceActionWeight s*symbolSecond p s (fieldDirection f) v) :=by
  have first:=(rawActionSymbol_smooth f p s valid).differentiableAt (by simp) |>.hasFDerivAt
  have firstPath:=first.comp_hasDerivAt_of_eq 0 (state_line s v) (by simp)
  have weight:=(sourceActionWeight_smooth s valid).differentiableAt (by simp) |>.hasFDerivAt
  have weightPath:=weight.comp_hasDerivAt_of_eq 0 (state_line s v) (by simp)
  have h:=((weightPath.mul (symbol_second_generated p s (fieldDirection f) v valid)).const_smul (-(4:ℂ)))
  have near : ∀ᶠr in 𝓝 (0:ℝ),s+r • v∈validStates :=
    (state_line s v).continuousAt.preimage_mem_nhds (by simpa using validStates_open.mem_nhds valid)
  have same : (fun r : ℝ=>rawActionSymbol f p (s+r • v))=ᶠ[𝓝 (0:ℝ)]
      (fun r=> -(4:ℂ) • (sourceActionWeight (s+r • v)*symbolFirst p (s+r • v) (fieldDirection f))) :=
    near.mono fun r hr=>rawActionSymbol_source f p _ hr
  have result:=firstPath.unique (h.congr_of_eventuallyEq same)
  simpa only [Function.comp_apply,zero_smul,add_zero,symbolSecond,actionWeightFirst,rawActionContact] using result

theorem rawActionContact_split (f g : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : SourceCoordinateSlice) :
    rawActionContact f p (sourceState z) (fieldDirection g)=
      rawActionContact f p (sourceState z) (sliceState (fieldVector g z))+
      rawActionContact f p (sourceState z) (complement g z) :=by
  unfold rawActionContact complement
  rw [map_sub]
  abel

theorem rawActionContact_actual (f g : Field289) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    quantizer (rawActionContact f p (sourceState z.val) (fieldDirection g))=rawContactFiber f g p z.val :=by
  have hs:=(rawActionSymbol_smooth f p (sourceState z.val)
    ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩).differentiableAt (by simp)
  change quantizer (fderiv ℝ (rawActionSymbol f p) (sourceState z.val) (fieldDirection g))=
    fderiv ℝ (fun s=>quantizer (rawActionSymbol f p s)) (sourceState z.val) (fieldDirection g)
  have derivative:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp (sourceState z.val) hs.hasFDerivAt
  exact (congrArg (fun D : ActionState →L[ℝ] FiberMap=>D (fieldDirection g)) derivative.fderiv).symm

end LowEnergy.PreparationVacuumActionFieldLift
