import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Source
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Weight

/-! The original volume multiplies the temporal principal before variation.
Its extra contacts and the boundary-momentum normalization are retained. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StateGreen StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section
local instance densityIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _
local instance densitySourceReal : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

def densitizedPrincipalDirection (point : BasePoint) (direction : LorentzianCoframe) : SourceMatrix :=
  ((|(actual.coframe point).det| : ℝ) : ℂ) • principalDirection point direction+
    (volumeDirection point direction : ℂ) • principalMatrix (actual.coframe point)

def densitizedLowerDirection (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe) : SourceMatrix :=
  ((|(actual.coframe point).det| : ℝ) : ℂ) • lowerDirection point k direction+
    (volumeDirection point direction : ℂ) • lowerMatrix point k (actual.coframe point)

theorem densitizedPrincipal_parameter (point : BasePoint) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => ((|(coframePath point direction epsilon).det| : ℝ) : ℂ) •
      principalMatrix (coframePath point direction epsilon))
      (densitizedPrincipalDirection point direction) 0 := by
  have volume := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (volume_parameter point direction)
  have generated := volume.smul (principal_parameter point direction)
  unfold densitizedPrincipalDirection
  convert! generated using 1
  simp only [Function.comp_apply,Complex.ofRealCLM_apply,coframePath_zero]

theorem densitizedLower_parameter (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => ((|(coframePath point direction epsilon).det| : ℝ) : ℂ) •
      lowerMatrix point k (coframePath point direction epsilon))
      (densitizedLowerDirection point k direction) 0 := by
  have volume := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (volume_parameter point direction)
  have generated := volume.smul (lower_parameter point k direction)
  unfold densitizedLowerDirection
  convert! generated using 1
  simp only [Function.comp_apply,Complex.ofRealCLM_apply,coframePath_zero]

theorem original_weight_contact (point : BasePoint) (direction : LorentzianCoframe) :
    weightDirection point direction=(-Complex.I*(spinScale : ℂ)) •
      (Quantum.operatorMatrix Quantum.spinExchange*densitizedPrincipalDirection point direction) := by
  simp only [weightDirection,densitizedPrincipalDirection,Matrix.mul_add,Matrix.mul_smul]

def densitizedGreen (point : BasePoint) (k : Fin 3 → ℝ) (energy damping : ℝ) : SourceMatrix :=
  (((|(actual.coframe point).det| : ℝ) : ℂ)⁻¹) •
    Quantum.operatorMatrix (Triangular.diracResolvent actual point k (Retarded.spectralParameter energy damping))

theorem original_density_contact (point : BasePoint) (k : Fin 3 → ℝ)
    (direction : LorentzianCoframe) (energy damping : ℝ) (positive : 0<damping) :
    derivativeVertex (densitizedPrincipalDirection point direction) (densitizedLowerDirection point k direction)
        (Retarded.spectralParameter energy damping)*densitizedGreen point k energy damping=
      onShellVertex (densitizedPrincipalDirection point direction) (densitizedLowerDirection point k direction)
        (coframeHamiltonian point k (actual.coframe point))*densitizedGreen point k energy damping+
      densitizedPrincipalDirection point direction*
        ((((|(actual.coframe point).det| : ℝ) : ℂ)⁻¹) •
          Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))) := by
  have original := original_Dirac_contact point k energy damping positive
    (densitizedPrincipalDirection point direction) (densitizedLowerDirection point k direction)
  dsimp only at original
  have scaled := congrArg (fun M : SourceMatrix => (((|(actual.coframe point).det| : ℝ) : ℂ)⁻¹) • M) original
  rw [coframeHamiltonian_actual]
  simpa only [densitizedGreen,smul_add,Matrix.mul_smul] using scaled

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
