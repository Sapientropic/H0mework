import H0mework.Physics.LowEnergy.PacketPairResponse.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! A bounded strongly measurable field on the actual light band generates
its genuine ambient L² extension, equal to zero outside that same band. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

def extendBand (field : LightBand → E) : Position → E :=
  Function.extend (Subtype.val : LightBand → Position) field (fun _ => 0)

theorem extendBand_inside (field : LightBand → E) (point : LightBand) : extendBand field point.val=field point :=
  Subtype.val_injective.extend_apply field (fun _ => 0) point

theorem extendBand_outside (field : LightBand → E) (point : Position) (outside : ¬‖point‖≤bandRadius) :
    extendBand field point=0 := by
  apply Function.extend_apply'
  rintro ⟨inside,equal⟩
  exact outside (equal ▸ inside.property)

theorem extendBand_stronglyMeasurable (field : LightBand → E) (measurable : StronglyMeasurable field) :
    StronglyMeasurable (extendBand field) :=
  (MeasurableEmbedding.subtype_coe band_measurable).stronglyMeasurable_extend measurable stronglyMeasurable_const

theorem extendBand_compact (field : LightBand → E) : HasCompactSupport (extendBand field) :=
  HasCompactSupport.intro band_compact (fun point outside => extendBand_outside field point outside)

theorem extendBand_bound (field : LightBand → E) (bound : ℝ) (nonnegative : 0≤bound)
    (bounded : ∀ point, ‖field point‖≤bound) (point : Position) : ‖extendBand field point‖≤bound := by
  by_cases inside : ‖point‖≤bandRadius
  · rw [show point=(⟨point,inside⟩ : LightBand).val from rfl,extendBand_inside]
    exact bounded _
  · rw [extendBand_outside field point inside,norm_zero]
    exact nonnegative

theorem extendBand_memLp (field : LightBand → E) (measurable : StronglyMeasurable field)
    (bound : ℝ) (nonnegative : 0≤bound) (bounded : ∀ point, ‖field point‖≤bound) :
    MemLp (extendBand field) 2 (volume : Measure Position) :=
  (extendBand_compact field).memLp_of_bound (extendBand_stronglyMeasurable field measurable).aestronglyMeasurable bound
    (Filter.Eventually.of_forall (extendBand_bound field bound nonnegative bounded))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
