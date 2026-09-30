import H0mework.Physics.LowEnergy.PacketFourier.Quadrature

/-! The second quadrature is the actual real sine profile in physical position space. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise
noncomputable section

theorem phase_sine (angle : ℝ) :
    (2*Complex.I)⁻¹*(Complex.exp ((angle : ℂ)*Complex.I)-Complex.exp (((-angle : ℝ) : ℂ)*Complex.I))=
      (Real.sin angle : ℂ) := by
  rw [Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  field_simp
  ring

theorem positionPhase_sine (shift x : Position) :
    (2*Complex.I)⁻¹*(positionPhase shift x-positionPhase (-shift) x)=
      (Real.sin (2*Real.pi*inner ℝ shift x) : ℂ) := by
  simpa only [positionPhase,inner_neg_left,mul_neg] using phase_sine (2*Real.pi*inner ℝ shift x)

def sineShift (shift : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (2*Complex.I)⁻¹ • ((phaseShift shift).toContinuousLinearMap-(phaseShift (-shift)).toContinuousLinearMap)

theorem sineShift_position (shift : Position) (field : FullMatterL2) :
    sineShift shift field =ᵐ[volume] fun x => (Real.sin (2*Real.pi*inner ℝ shift x) : ℂ) • field x := by
  filter_upwards [phaseShift_position shift field,phaseShift_position (-shift) field,
    Lp.coeFn_sub (phaseShift shift field) (phaseShift (-shift) field),
    Lp.coeFn_smul ((2*Complex.I)⁻¹) (phaseShift shift field-phaseShift (-shift) field)]
    with x plus minus difference scaled
  change ((2*Complex.I)⁻¹ • (phaseShift shift field-phaseShift (-shift) field) : FullMatterL2) x=_
  rw [scaled]
  simp only [Pi.smul_apply,difference,Pi.sub_apply,plus,minus,← sub_smul,smul_smul]
  change ((2*Complex.I)⁻¹*(positionPhase shift x-positionPhase (-shift) x)) • field x=_
  rw [positionPhase_sine]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
