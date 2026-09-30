import H0mework.Physics.LowEnergy.LightSpace.Radial

/-! The source rotation theorem generates one shared spin-lift parameter pair for a momentum and its opposite. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightSpace
open Rotation ProofFreeRicherAnholonomicSource
noncomputable section

def alignmentParameters (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : ℝ × ℝ :=
  let generated := momentum_alignment momentum nonzero
  ⟨Classical.choose generated,Classical.choose (Classical.choose_spec generated)⟩

def spatialRotation (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : LorentzianCoframe :=
  let parameters := alignmentParameters momentum nonzero
  rotateY (circleCos parameters.1) (circleSin parameters.1)*rotateZ (circleCos parameters.2) (circleSin parameters.2)

theorem spatialRotation_generated (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    (spatialRotation momentum nonzero).transpose*spatialRotation momentum nonzero=1 ∧
    (spatialRotation momentum nonzero).det=1 ∧
    spatialRotation momentum nonzero *ᵥ ![0,momentum 0,momentum 1,momentum 2]=
      ![0,0,0,momentumRadius momentum] :=
  Classical.choose_spec (Classical.choose_spec (momentum_alignment momentum nonzero))

theorem same_frame_opposite (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    spatialRotation momentum nonzero *ᵥ ![0,-momentum 0,-momentum 1,-momentum 2]=
      ![0,0,0,-momentumRadius momentum] := by
  have negative : (![0,-momentum 0,-momentum 1,-momentum 2] : Fin 4 → ℝ)= - ![0,momentum 0,momentum 1,momentum 2] := by
    ext i
    fin_cases i <;> simp
  rw [negative,Matrix.mulVec_neg,(spatialRotation_generated momentum nonzero).2.2]
  ext i
  fin_cases i <;> simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightSpace
