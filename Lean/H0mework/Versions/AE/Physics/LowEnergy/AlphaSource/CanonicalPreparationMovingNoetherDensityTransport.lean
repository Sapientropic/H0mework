import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherLegendre

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussQuantumMultiplier GaussHistoryHilbert
open FullQuantum.StateGreen PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
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

def momentumConnection (force : Field289) (s : ActionState) : SourceMatrix:=
  momentumFirst force s*statePhase s

def densityActionInverse : SourceMatrix:=
  (4*(Stage9C.Material.SpinPair.spinScale:ℂ))⁻¹ • Quantum.operatorMatrix YangMills.FullPairing.flipMatter

theorem densityAction_two_sided :
    densityActionMatrix*densityActionInverse=1 ∧ densityActionInverse*densityActionMatrix=1 :=by
  have flip : Quantum.operatorMatrix YangMills.FullPairing.flipMatter*
      Quantum.operatorMatrix YangMills.FullPairing.flipMatter=(1:SourceMatrix):=by
    rw [←Quantum.matrix_composition]
    have source : YangMills.FullPairing.flipMatter.comp YangMills.FullPairing.flipMatter=1:=by
      apply LinearMap.ext
      intro v
      exact YangMills.FullPairing.flipMatter_twice v
    rw [source,map_one]
  have nonzero : 4*(Stage9C.Material.SpinPair.spinScale:ℂ)≠0:=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Stage9C.Material.SpinPair.spinScale_pos.ne')
  constructor <;> simp only [densityActionMatrix,densityActionInverse,smul_mul_smul,flip]
  · rw [mul_inv_cancel₀ nonzero,one_smul]
  · rw [inv_mul_cancel₀ nonzero,one_smul]

def rawMomentumMatrix (s : ActionState) : SourceMatrix:=densityActionMatrix*inversePhase s
def rawMomentumInverse (s : ActionState) : SourceMatrix:=statePhase s*densityActionInverse

theorem rawMomentum_two_sided (s : ActionState) (valid : s∈validStates) :
    rawMomentumMatrix s*rawMomentumInverse s=1 ∧ rawMomentumInverse s*rawMomentumMatrix s=1 :=by
  constructor
  · rw [rawMomentumMatrix,rawMomentumInverse,mul_assoc,←mul_assoc (inversePhase s),
      (momentum_two_sided s valid).1,one_mul,densityAction_two_sided.1]
  · rw [rawMomentumMatrix,rawMomentumInverse,mul_assoc,←mul_assoc densityActionInverse,
      densityAction_two_sided.2,one_mul,(momentum_two_sided s valid).2]

theorem rawMomentum_source_weight (s : ActionState) :
    SourceRealScalarFock.branches (rawMomentumMatrix s)=(4:ℂ) • sourceActionWeight s :=by
  ext i j
  cases i <;> cases j <;>
    simp [rawMomentumMatrix,densityActionMatrix,sourceActionWeight,SourceRealScalarFock.branches,
      Matrix.smul_apply,Matrix.map_apply,smul_mul_assoc,smul_smul,map_ofNat] <;> ring

def rawMomentumConnection (force : Field289) (s : ActionState) : SourceMatrix:=
  densityActionMatrix*momentumFirst force s*statePhase s*densityActionInverse

/-- The moving canonical momentum is held fixed, so chi varies through B inverse. -/
def transportedDensity (reader : Field289) (base candidate : ActionState) (i : Fin 4) : SourceMatrix:=
  rawMomentumMatrix base*rawMomentumInverse candidate*densityActionMatrix*densityVariation reader candidate i

def noetherContactCoefficient (reader force : Field289) (s : ActionState) (i : Fin 4) : SourceMatrix:=
  densityActionMatrix*(densitySecond reader force s i+shellSecond reader force s i)-
    rawMomentumConnection force s*(densityActionMatrix*densityVariation reader s i)

theorem transportedDensity_source (reader : Field289) (s : ActionState) (valid : s∈validStates) (i : Fin 4) :
    transportedDensity reader s s i=densityActionMatrix*densityVariation reader s i :=by
  rw [transportedDensity,(rawMomentum_two_sided s valid).1,one_mul]

theorem transportedDensity_generated (reader force : Field289) (z : physicalChart) (i : Fin 4) :
    HasDerivAt (fun r : ℝ=>transportedDensity reader (sourceState z.val)
      (sourceState z.val+r • fieldDirection force) i)
      (noetherContactCoefficient reader force (sourceState z.val) i) 0 :=by
  let s:=sourceState z.val
  have valid : s∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have inverse:=(inverseMomentumFirst_generated force s valid).mul_const densityActionInverse
  have density:=actual_mixed_family_generated reader force z i
  have product:=(((inverse.const_mul (rawMomentumMatrix s)).mul_const densityActionMatrix).mul density)
  have algebra : rawMomentumMatrix s*(phaseVariation force s*densityActionInverse)*densityActionMatrix*densityVariation reader s i+
      (rawMomentumMatrix s*(statePhase s*densityActionInverse)*densityActionMatrix)*(densitySecond reader force s i+shellSecond reader force s i)=
        noetherContactCoefficient reader force s i :=by
    rw [momentumFirst_inverse force s valid]
    simp only [noetherContactCoefficient,rawMomentumMatrix,rawMomentumConnection,neg_mul,mul_neg,mul_assoc,
      sub_eq_add_neg]
    have middle (M : SourceMatrix) : inversePhase s*(statePhase s*(densityActionInverse*(densityActionMatrix*M)))=M:=by
      rw [←mul_assoc densityActionInverse densityActionMatrix,densityAction_two_sided.2,one_mul,
        ←mul_assoc (inversePhase s) (statePhase s),(momentum_two_sided s valid).1,one_mul]
    rw [middle]
    rw [←mul_assoc (inversePhase s) (statePhase s),(momentum_two_sided s valid).1,one_mul]
    abel
  have generated : HasDerivAt (fun r : ℝ=>transportedDensity reader s (s+r • fieldDirection force) i)
      (rawMomentumMatrix s*(phaseVariation force s*densityActionInverse)*densityActionMatrix*densityVariation reader s i+
        (rawMomentumMatrix s*(statePhase s*densityActionInverse)*densityActionMatrix)*
          (densitySecond reader force s i+shellSecond reader force s i)) 0:=by
    convert! product using 1
    simp only [zero_smul,add_zero]
    rfl
  exact generated.congr_deriv algebra

/-- Both original physical momentum branches are transported before conjugation. -/
def transportedRawSymbol (reader : Field289) (base candidate : ActionState) (p : PhysicalMomentum) : FullMatrix:=
  rawFourier p (transportedDensity reader base candidate)

def noetherContactSymbol (reader force : Field289) (s : ActionState) (p : PhysicalMomentum) : FullMatrix:=
  rawFourier p (noetherContactCoefficient reader force s)

theorem transportedRawSymbol_source (reader : Field289) (s : ActionState) (valid : s∈validStates)
    (p : PhysicalMomentum) : transportedRawSymbol reader s s p=rawActionSymbol reader p s :=by
  rw [transportedRawSymbol,rawActionSymbol]
  exact congrArg (rawFourier p) (funext (transportedDensity_source reader s valid))

theorem noetherContactSymbol_generated (reader force : Field289) (z : physicalChart) (p : PhysicalMomentum) :
    HasDerivAt (fun r : ℝ=>transportedRawSymbol reader (sourceState z.val)
      (sourceState z.val+r • fieldDirection force) p)
      (noetherContactSymbol reader force (sourceState z.val) p) 0 :=
  (rawFourier p).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_pi.mpr (transportedDensity_generated reader force z))

def fullMomentumConnection (force : Field289) (s : ActionState) : FullMatrix:=
  Matrix.fromBlocks (rawMomentumConnection force s) 0 0 ((rawMomentumConnection force s).map star)

theorem noetherContactSymbol_raw_contact (reader force : Field289) (z : physicalChart) (p : PhysicalMomentum) :
    noetherContactSymbol reader force (sourceState z.val) p=
      rawFourier p (fun i=>densityActionMatrix*(densitySecond reader force (sourceState z.val) i+
        shellSecond reader force (sourceState z.val) i))-
      fullMomentumConnection force (sourceState z.val)*rawActionSymbol reader p (sourceState z.val) :=by
  have affine (A : Fin 4→SourceMatrix) (K : SourceMatrix) (q : PhysicalMomentum) :
      affineMatrix (fun i=>A i-K*(densityActionMatrix*densityVariation reader (sourceState z.val) i)) q=
        affineMatrix A q-K*affineMatrix (fun i=>densityActionMatrix*densityVariation reader (sourceState z.val) i) q :=by
    simp only [affineMatrix,smul_sub,Finset.sum_sub_distrib,mul_add,Finset.mul_sum,mul_smul_comm]
    abel
  unfold noetherContactSymbol noetherContactCoefficient fullMomentumConnection rawActionSymbol
  rw [rawFourier_blocks,rawFourier_blocks,rawFourier_blocks,affine,affine,Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.map_apply,Matrix.mul_apply,sub_eq_add_neg,map_sum,map_mul]

/-- Quantized products retain their original four-leg normal term on every occupation. -/
theorem noetherContact_fullCAR (reader force : Field289) (z : physicalChart) (p : PhysicalMomentum)
    (v : FockFiber) :
    fiberCoordinates (quantizer (noetherContactSymbol reader force (sourceState z.val) p) v)=
      fiberCoordinates (rawContactFiber reader force p z.val v)-
        Fermion.quantize (fullMomentumConnection force (sourceState z.val))
          (Fermion.quantize (rawActionSymbol reader p (sourceState z.val)) (fiberCoordinates v))+
        Fermion.normalProduct (fullMomentumConnection force (sourceState z.val))
          (rawActionSymbol reader p (sourceState z.val)) (fiberCoordinates v) :=by
  rw [noetherContactSymbol_raw_contact,raw_contact_source]
  have normal:=LinearMap.congr_fun (Fermion.quantize_normal_order
    (fullMomentumConnection force (sourceState z.val)) (rawActionSymbol reader p (sourceState z.val))) (fiberCoordinates v)
  have subtract (A B : FullMatrix) : Fermion.quantize (A-B)=Fermion.quantize A-Fermion.quantize B:=by
    apply LinearMap.ext
    intro x
    have linear:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>fiberCoordinates (T (fiberCoordinates.symm x)))
      (quantizer.map_sub A B)
    change Fermion.quantize (A-B) x=Fermion.quantize A x-Fermion.quantize B x at linear
    exact linear
  change Fermion.quantize (_-_) (fiberCoordinates v)=_
  rw [subtract,LinearMap.sub_apply]
  change Fermion.quantize _ (fiberCoordinates v)-Fermion.quantize _ (fiberCoordinates v)=
    Fermion.quantize _ (fiberCoordinates v)-_+_
  simp only [LinearMap.add_apply,Module.End.mul_apply] at normal
  rw [normal]
  abel

end LowEnergy.PreparationVacuumNoetherChart
