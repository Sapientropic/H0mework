import H0mework.Physics.LowEnergy.PacketField.PhysicalExtension
import H0mework.Physics.LowEnergy.PacketPairResponse.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The source Fourier measure and the actual zero extension identify spatial
Hilbert pairs with the physical light-band integral, retaining its volume. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem extendBand_pair (left right : LightBand → E) :
    (∫ position : Position, (inner ℂ (extendBand left position) (extendBand right position)).re)=
      ∫ point : LightBand, (inner ℂ (left point) (right point)).re ∂bandMeasure := by
  have zeroOutside (point : Position) (outside : point∉{p : Position | ‖p‖≤bandRadius}) :
      (inner ℂ (extendBand left point) (extendBand right point)).re=0 := by
    rw [extendBand_outside left point outside,inner_zero_left,Complex.zero_re]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero zeroOutside]
  rw [← integral_subtype_comap band_measurable]
  simp_rw [extendBand_inside]
  rfl

theorem physicalBand_pair (left right : LightBand → E) :
    (∫ frequency : Position, (inner ℂ (physicalBand left frequency) (physicalBand right frequency)).re)=
      fourierDensity*∫ point : LightBand, (inner ℂ (left point) (right point)).re ∂bandMeasure := by
  have generated := physicalFourier_measure
    (fun position : Position => (inner ℂ (extendBand left position) (extendBand right position)).re)
  rw [extendBand_pair] at generated
  simpa only [physicalBand,fourierDensity,one_div,smul_eq_mul] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
