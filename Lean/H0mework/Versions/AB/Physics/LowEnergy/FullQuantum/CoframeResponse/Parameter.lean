import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Coframe

set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StateGreen
noncomputable section
local instance parameterIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

theorem coframeHamiltonian_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => coframeHamiltonian point k (coframePath point direction epsilon))
      (hamiltonianDirection point k direction) 0 := by
  have regular : IsUnit (principalMatrix (coframePath point direction 0)) := by
    rw [coframePath_zero]
    exact principalMatrix_regular (actual.coframe point) (actual_noncharacteristic point)
  have generated := timeSymbol_parameter (fun epsilon => principalMatrix (coframePath point direction epsilon))
    (fun epsilon => lowerMatrix point k (coframePath point direction epsilon))
    (principalDirection point direction) (lowerDirection point k direction) 0 regular
    (principal_parameter point direction) (lower_parameter point k direction)
  unfold hamiltonianDirection coframeHamiltonian
  rw [coframePath_zero] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
