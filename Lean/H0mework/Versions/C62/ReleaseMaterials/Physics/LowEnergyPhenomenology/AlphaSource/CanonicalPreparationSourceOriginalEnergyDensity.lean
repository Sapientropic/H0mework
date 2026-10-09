import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActionTimeMatrix
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.RawActionDensity

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActionUnits
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

def originalEnergyCoefficient (s : ActionState) (i : Fin 4) : SourceMatrix :=
  densityActionMatrix*Fin.cases (-stateDensityLower s)
    (fun j=>(-Complex.I) • statePrincipal j.succ s) i

theorem originalEnergyCoefficient_time_generated (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) :
    inversePhase s*stateHamiltonian s 0= -stateDensityLower s :=by
  simp only [stateHamiltonian,Fin.cases_zero,timeSymbol,inversePhase,smul_mul_smul,mul_assoc]
  rw [←mul_assoc (principalMatrix s.1),
    Ring.mul_inverse_cancel _ (principalMatrix_regular s.1 regular),one_mul]
  have factor : (-Complex.I*stateVolume s)*(-Complex.I)= -stateVolume s :=by
    calc
      _=(Complex.I*Complex.I)*stateVolume s :=by ring
      _=_ :=by rw [Complex.I_mul_I,neg_one_mul]
  rw [←mul_assoc (-Complex.I),factor,neg_smul]
  rfl

theorem originalEnergyCoefficient_spatial_generated (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (j : Fin 3) :
    inversePhase s*stateHamiltonian s j.succ=(-Complex.I) • statePrincipal j.succ s :=by
  simp only [stateHamiltonian,Fin.cases_succ,inversePhase,smul_mul_assoc]
  rw [←mul_assoc,Ring.mul_inverse_cancel _ (principalMatrix_regular s.1 regular),one_mul]
  simp only [statePrincipal,smul_smul]

theorem originalEnergyCoefficient_generated (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    originalEnergyCoefficient s i=sourcePreparedTimeMatrix s*stateHamiltonian s i :=by
  rw [sourcePreparedTimeMatrix,sourceTimeMomentum_matrix,mul_assoc]
  refine Fin.cases ?_ (fun j=>?_) i
  · rw [originalEnergyCoefficient,Fin.cases_zero,originalEnergyCoefficient_time_generated s regular]
  · rw [originalEnergyCoefficient,Fin.cases_succ,originalEnergyCoefficient_spatial_generated s regular j]

def originalEnergySymbol (p : PhysicalMomentum) (s : ActionState) : FullMatrix :=
  rawFourier p (originalEnergyCoefficient s)

private theorem affine_left (M : SourceMatrix) (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) :
    affineMatrix (fun i=>M*A i) p=M*affineMatrix A p :=by
  simp only [affineMatrix,Matrix.mul_add,Matrix.mul_sum,Matrix.mul_smul]

theorem originalEnergySymbol_generated (p : PhysicalMomentum) (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) :
    originalEnergySymbol p s=
      SourceRealScalarFock.branches (sourcePreparedTimeMatrix s)*fourierLinear p (stateHamiltonian s) :=by
  have coefficients : originalEnergyCoefficient s=fun i=>sourcePreparedTimeMatrix s*stateHamiltonian s i :=
    funext (originalEnergyCoefficient_generated s regular)
  rw [originalEnergySymbol,coefficients,rawFourier_blocks,affine_left,affine_left]
  change _=SourceRealScalarFock.branches _*realFourierMatrix _ p
  rw [SourceRealScalarFock.branches,realFourierMatrix,Matrix.fromBlocks_multiply]
  ext u v
  cases u <;> cases v <;>
    simp [Matrix.map_apply,Matrix.mul_apply]

private theorem branches_real_smul (r : ℝ) (M : SourceMatrix) :
    SourceRealScalarFock.branches ((r:ℂ) • M)=(r:ℂ) • SourceRealScalarFock.branches M :=by
  ext u v
  cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.smul_apply]

def sourceTimeWeight (s : ActionState) : FullMatrix :=
  SourceRealScalarFock.branches (sourcePreparedTimeMatrix s)

theorem sourceTimeWeight_original (s : ActionState) :
    sourceTimeWeight s=(4:ℂ) • sourceActionWeight s :=by
  rw [sourceTimeWeight,sourcePreparedTimeMatrix_generated,branches_real_smul,
    sourceActionWeight,branches_real_smul,smul_smul]
  congr 1
  rw [Stage10.ActionNormalization.phaseMomentum_source]
  push_cast
  rfl

theorem originalEnergySymbol_phase_return (p : PhysicalMomentum) (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) :
    originalEnergySymbol p s=(Stage10.ActionNormalization.phaseMomentum:ℂ) •
      (SourceRealScalarFock.branches (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s)*
        fourierLinear p (stateHamiltonian s)) :=by
  rw [originalEnergySymbol_generated p s regular,sourcePreparedTimeMatrix_generated,
    branches_real_smul,smul_mul_assoc]

theorem originalEnergySymbol_normalized (p : PhysicalMomentum) (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) :
    (Stage10.ActionNormalization.actionScale:ℂ) • originalEnergySymbol p s=
      SourceRealScalarFock.branches (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s)*
        fourierLinear p (stateHamiltonian s) :=by
  rw [originalEnergySymbol_phase_return p s regular,smul_smul,sourceActionScale_momentum,one_smul]

def originalEnergyDensity (p : PhysicalMomentum) (s : ActionState) : FockEnd :=
  rawPairDensity (affineMatrix (originalEnergyCoefficient s) p)
    (affineMatrix (originalEnergyCoefficient s) (-p))

theorem originalEnergyDensity_quantized (p : PhysicalMomentum) (s : ActionState) :
    originalEnergyDensity p s=Fermion.quantize (originalEnergySymbol p s) :=by
  rw [originalEnergyDensity,rawPairDensity_quantize,originalEnergySymbol,rawFourier_blocks]

def originalEnergyFiber (p : PhysicalMomentum) (s : ActionState) : FiberMap :=
  quantizer (originalEnergySymbol p s)

theorem originalEnergyFiber_original_halves (p : PhysicalMomentum) (s : ActionState) (v : FockFiber) :
    fiberCoordinates (originalEnergyFiber p s v)=
      (1/2:ℂ) •
        (plusDensity (affineMatrix (originalEnergyCoefficient s) p) (fiberCoordinates v)-
          oppositeDensity (affineMatrix (originalEnergyCoefficient s) (-p)) (fiberCoordinates v)) :=by
  change fiberCoordinates (fiberCoordinates.symm (Fermion.quantize _ (fiberCoordinates v)))=_
  rw [LinearEquiv.apply_symm_apply,←originalEnergyDensity_quantized]
  simp only [originalEnergyDensity,rawPairDensity,LinearMap.smul_apply,LinearMap.sub_apply]

theorem originalEnergyFiber_normalized (p : PhysicalMomentum) (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) :
    (Stage10.ActionNormalization.actionScale:ℂ) • originalEnergyFiber p s=
      quantizer (SourceRealScalarFock.branches
        (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s)*fourierLinear p (stateHamiltonian s)) :=by
  rw [originalEnergyFiber,←map_smul,originalEnergySymbol_normalized p s regular]

end LowEnergy.PreparationPhysicalActionUnits
