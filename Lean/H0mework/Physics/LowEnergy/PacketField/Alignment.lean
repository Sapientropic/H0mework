import H0mework.Physics.LowEnergy.PacketField.Reflection

/-! The paired Borel frame aligns the original momentum with its signed
axial radius, so the same native source identity applies at both orientations. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open Rotation ProofFreeRicherAnholonomicSource
noncomputable section

def pairedRotation (momentum : Fin 3 → ℝ) : LorentzianCoframe := borelRotation (representative momentum)

theorem pairedRotation_negative (momentum : Fin 3 → ℝ) : pairedRotation (-momentum)=pairedRotation momentum := by
  rw [pairedRotation,representative_negative]
  rfl

theorem pairedRotation_alignment (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    pairedRotation momentum *ᵥ ![0,momentum 0,momentum 1,momentum 2]=
      ![0,0,0,lineSign momentum*momentumRadius momentum] := by
  have recover : lineSign momentum • representative momentum=momentum := by
    rw [representative,smul_smul,← pow_two,lineSign_square momentum nonzero,one_smul]
  have coordinate (j : Fin 3) : lineSign momentum*(representative momentum j)=momentum j := congrFun recover j
  have lift : (![0,momentum 0,momentum 1,momentum 2] : Fin 4 → ℝ)=
      lineSign momentum • ![0,representative momentum 0,representative momentum 1,representative momentum 2] := by
    ext j
    fin_cases j <;> simp [coordinate]
  rw [pairedRotation,lift,Matrix.mulVec_smul,
    (borelRotation_generated _ (representative_nonzero momentum nonzero)).2.2,
    representative_radius momentum nonzero]
  ext j
  fin_cases j <;> simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
