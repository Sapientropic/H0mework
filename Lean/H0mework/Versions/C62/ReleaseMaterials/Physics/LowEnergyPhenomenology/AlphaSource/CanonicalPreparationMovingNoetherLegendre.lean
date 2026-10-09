import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalDensitySourceFeed

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert CanonicalGradedSpatialSource
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def momentumMother (s : ActionState) : YangMills.FullPairing.Mother:=
  Quantum.operatorMatrix.toLinearEquiv.symm (inversePhase s)

def inverseMomentumMother (s : ActionState) : YangMills.FullPairing.Mother:=
  Quantum.operatorMatrix.toLinearEquiv.symm (statePhase s)

def legendreDual (s : ActionState) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier:=chi.comp (momentumMother s)

def densityDual (s : ActionState) (pi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier:=pi.comp (inverseMomentumMother s)

theorem momentumMother_original (s : ActionState) :
    momentumMother s=(-Complex.I*stateVolume s) • currentCoframeMatterTemporalPrincipal s.1 :=by
  apply Quantum.operatorMatrix.injective
  have inverse (A : SourceMatrix) : Quantum.operatorMatrix (Quantum.operatorMatrix.toLinearEquiv.symm A)=A:=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply A
  rw [momentumMother,inverse,inversePhase,map_smul]
  rfl

theorem legendreDual_original (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (connectionRows : Fin 4→SourceMatrix) (scalar : SourceMatrix)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    legendreDual (C.coframe point,connectionRows,scalar) chi=FullQuantum.normalizedMomentum C point chi :=by
  rw [legendreDual,momentumMother_original]
  apply LinearMap.ext
  intro v
  simp only [FullQuantum.normalizedMomentum,LinearMap.comp_apply,LinearMap.smul_apply,map_smul,stateVolume]

theorem momentum_two_sided (s : ActionState) (valid : s∈validStates) :
    inversePhase s*statePhase s=1 ∧ statePhase s*inversePhase s=1 :=by
  have left:=inversePhase_source s valid.1 valid.2
  exact ⟨left,mul_eq_one_comm.mp left⟩

theorem mother_two_sided (s : ActionState) (valid : s∈validStates) :
    (momentumMother s).comp (inverseMomentumMother s)=1 ∧
      (inverseMomentumMother s).comp (momentumMother s)=1 :=by
  have source:=momentum_two_sided s valid
  have inverse (A : SourceMatrix) : Quantum.operatorMatrix (Quantum.operatorMatrix.toLinearEquiv.symm A)=A:=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply A
  constructor <;> apply Quantum.operatorMatrix.injective
  · rw [Quantum.matrix_composition,momentumMother,inverseMomentumMother,
      inverse,inverse,
      source.1,map_one]
  · rw [Quantum.matrix_composition,momentumMother,inverseMomentumMother,
      inverse,inverse,
      source.2,map_one]

theorem densityDual_legendre (s : ActionState) (valid : s∈validStates)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) : densityDual s (legendreDual s chi)=chi :=by
  apply LinearMap.ext
  intro v
  change chi (momentumMother s (inverseMomentumMother s v))=chi v
  have same:=LinearMap.congr_fun (mother_two_sided s valid).1 v
  change momentumMother s (inverseMomentumMother s v)=v at same
  rw [same]

theorem legendreDual_density (s : ActionState) (valid : s∈validStates)
    (pi : Module.Dual ℂ DiracExteriorMatterCarrier) : legendreDual s (densityDual s pi)=pi :=by
  apply LinearMap.ext
  intro v
  change pi (inverseMomentumMother s (momentumMother s v))=pi v
  have same:=LinearMap.congr_fun (mother_two_sided s valid).2 v
  change inverseMomentumMother s (momentumMother s v)=v at same
  rw [same]

theorem inversePhase_smooth (s : ActionState) (valid : s∈validStates) : ContDiffAt ℝ ∞ inversePhase s :=
  (contDiffAt_const.mul (stateVolume_smooth s valid.1)).smul
    ((principalMatrix_smooth s.1 valid.1).comp s contDiffAt_fst)

def momentumFirst (force : Field289) (s : ActionState) : SourceMatrix:=
  fderiv ℝ inversePhase s (fieldDirection force)

theorem momentumFirst_generated (force : Field289) (s : ActionState) (valid : s∈validStates) :
    HasDerivAt (fun r : ℝ=>inversePhase (s+r • fieldDirection force)) (momentumFirst force s) 0 :=by
  have path : HasDerivAt (fun r : ℝ=>s+r • fieldDirection force) (fieldDirection force) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (fieldDirection force)).const_add s using 1
    simp
  exact (inversePhase_smooth s valid).differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp)

theorem inverseMomentumFirst_generated (force : Field289) (s : ActionState) (valid : s∈validStates) :
    HasDerivAt (fun r : ℝ=>statePhase (s+r • fieldDirection force)) (phaseVariation force s) 0 :=by
  have path : HasDerivAt (fun r : ℝ=>s+r • fieldDirection force) (fieldDirection force) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (fieldDirection force)).const_add s using 1
    simp
  exact (statePhase_smooth s valid.1 valid.2).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp)

theorem momentumFirst_inverse (force : Field289) (s : ActionState) (valid : s∈validStates) :
    phaseVariation force s= -(statePhase s*momentumFirst force s*statePhase s) :=by
  have product:=(momentumFirst_generated force s valid).mul (inverseMomentumFirst_generated force s valid)
  have ray : Continuous (fun r : ℝ=>s+r • fieldDirection force):=continuous_const.add (continuous_id.smul continuous_const)
  have near : ∀ᶠr : ℝ in 𝓝 0,s+r • fieldDirection force∈validStates:=
    ray.continuousAt.preimage_mem_nhds (by simpa only [zero_smul,add_zero] using validStates_open.mem_nhds valid)
  have same : (fun r : ℝ=>inversePhase (s+r • fieldDirection force)*statePhase (s+r • fieldDirection force))
      =ᶠ[𝓝 0] (fun _=> (1:SourceMatrix)):=near.mono (fun r hr=>(momentum_two_sided _ hr).1)
  have zero:=product.unique ((hasDerivAt_const (0:ℝ) (1:SourceMatrix)).congr_of_eventuallyEq same)
  simp only [zero_smul,add_zero] at zero
  have solved:=congrArg (fun M : SourceMatrix=>statePhase s*M) zero
  rw [mul_add,←mul_assoc (statePhase s) (inversePhase s),(momentum_two_sided s valid).2,one_mul,mul_zero] at solved
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [mul_assoc,add_comm] using solved

end LowEnergy.PreparationVacuumNoetherChart
