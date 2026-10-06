import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Parameter

/-! Coframe variation changes the initial canonical momentum normalization.
Its volume and principal contributions are generated together. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator ContDiff
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StateGreen StageNineCoframeVariation
noncomputable section
local instance weightIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _
local instance weightCoframeNormed : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance weightCoframeSeminormed : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance weightCoframeReal : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance weightSourceReal : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

def volumeDirection (point : BasePoint) (direction : LorentzianCoframe) : ℝ :=
  fderiv ℝ (fun e : LorentzianCoframe => |e.det|) (actual.coframe point) direction

theorem volume_parameter (point : BasePoint) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => |(coframePath point direction epsilon).det|)
      (volumeDirection point direction) 0 := by
  have smooth := (coframe_volume_contDiffAt (actual.coframe point)
    (actual_coframe_nondegenerate point)).differentiableAt (by simp)
  exact smooth.hasFDerivAt.comp_hasDerivAt_of_eq 0 (coframePath_derivative point direction)
    (coframePath_zero point direction).symm

def weightMatrix (e : LorentzianCoframe) : SourceMatrix :=
  (-Complex.I*(spinScale : ℂ)) • (((|e.det| : ℝ) : ℂ) •
    (Quantum.operatorMatrix Quantum.spinExchange*principalMatrix e))

theorem weightMatrix_original (point : BasePoint) (e : LorentzianCoframe) :
    weightMatrix e=Quantum.operatorMatrix (boundaryWeight (coframeConfiguration e) point) := by
  simp only [weightMatrix,boundaryWeight,coframeConfiguration,map_smul,Quantum.matrix_composition,smul_smul]
  change _ • (Quantum.operatorMatrix Quantum.spinExchange*principalMatrix e)=
    _ • (Quantum.operatorMatrix Quantum.spinExchange*principalMatrix e)
  congr 1
  ring

def weightDirection (point : BasePoint) (direction : LorentzianCoframe) : SourceMatrix :=
  (-Complex.I*(spinScale : ℂ)) •
    (((|(actual.coframe point).det| : ℝ) : ℂ) •
      (Quantum.operatorMatrix Quantum.spinExchange*principalDirection point direction)+
    (volumeDirection point direction : ℂ) •
      (Quantum.operatorMatrix Quantum.spinExchange*principalMatrix (actual.coframe point)))

theorem weight_parameter (point : BasePoint) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => weightMatrix (coframePath point direction epsilon))
      (weightDirection point direction) 0 := by
  have volume := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (volume_parameter point direction)
  have principal := (principal_parameter point direction).const_mul (Quantum.operatorMatrix Quantum.spinExchange)
  have generated := (volume.smul principal).const_smul (-Complex.I*(spinScale : ℂ))
  unfold weightDirection weightMatrix
  convert! generated using 1
  simp only [Function.comp_apply,Complex.ofRealCLM_apply,coframePath_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
