import H0mework.Physics.LowEnergy.PacketField.Extension
import Mathlib.MeasureTheory.Group.Integral

/-! Reflection preserves the actual full light-band measure. Averaging the
two opposite spatial orders does not insert an extra factor into its integral. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def reflectPoint (point : LightBand) : LightBand := ⟨-point.val,by simpa only [norm_neg] using point.property⟩

theorem reflectPoint_continuous : Continuous reflectPoint := continuous_subtype_val.neg.subtype_mk _

theorem extendBand_integral (field : LightBand → E) :
    (∫ momentum : Position, extendBand field momentum)=∫ point : LightBand, field point ∂bandMeasure := by
  have outside (point : Position) (nonmember : point∉{p : Position | ‖p‖≤bandRadius}) :
      extendBand field point=0 := extendBand_outside field point nonmember
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero outside,← integral_subtype_comap band_measurable]
  simp_rw [extendBand_inside]
  rfl

omit [NormedSpace ℝ E] in
theorem extendBand_reflection (field : LightBand → E) (momentum : Position) :
    extendBand (fun point => field (reflectPoint point)) momentum=extendBand field (-momentum) := by
  by_cases member : ‖momentum‖≤bandRadius
  · let point : LightBand := ⟨momentum,member⟩
    change extendBand (fun p => field (reflectPoint p)) point.val=extendBand field (reflectPoint point).val
    rw [extendBand_inside,extendBand_inside]
  · rw [extendBand_outside _ momentum member,extendBand_outside _ (-momentum) (by simpa only [norm_neg] using member)]

theorem band_reflection (field : LightBand → E) :
    (∫ point : LightBand, field (reflectPoint point) ∂bandMeasure)=∫ point : LightBand, field point ∂bandMeasure := by
  rw [← extendBand_integral,← extendBand_integral]
  simp_rw [extendBand_reflection]
  exact integral_neg_eq_self _ _

theorem band_nonzero_ae : ∀ᵐ point : LightBand ∂bandMeasure, point.val≠0 := by
  have ambient : ∀ᵐ point : Position ∂volume, point≠0 := by
    exact (volume : Measure Position).ae_ne 0
  exact (ae_restrict_iff_subtype band_measurable).mp (ae_restrict_of_ae ambient)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
