import H0mework.Physics.LowEnergy.PacketField.Extension
import H0mework.Physics.LowEnergy.PacketField.PhysicalMeasure

/-! The actual bounded band field is extended in physical momentum and then
pulled to the source Fourier frequency h=k/(2π), preserving genuine L² data. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

def physicalBand (field : LightBand → E) (frequency : Position) : E :=
  extendBand field ((2*Real.pi) • frequency)

theorem physicalBand_stronglyMeasurable (field : LightBand → E) (measurable : StronglyMeasurable field) :
    StronglyMeasurable (physicalBand field) := by
  have scaling : Measurable (fun point : Position => (2*Real.pi) • point) :=
    ((continuous_const (y := (2*Real.pi : ℝ))).smul (continuous_id : Continuous (id : Position → Position))).measurable
  exact (extendBand_stronglyMeasurable field measurable).comp_measurable scaling

theorem physicalBand_compact (field : LightBand → E) : HasCompactSupport (physicalBand field) := by
  let scaling : Position ≃ₜ Position := Homeomorph.smul (Units.mk0 (2*Real.pi) (by positivity))
  exact (extendBand_compact field).comp_homeomorph scaling

theorem physicalBand_memLp (field : LightBand → E) (measurable : StronglyMeasurable field)
    (bound : ℝ) (nonnegative : 0≤bound) (bounded : ∀ point, ‖field point‖≤bound) :
    MemLp (physicalBand field) 2 (volume : Measure Position) :=
  (physicalBand_compact field).memLp_of_bound (physicalBand_stronglyMeasurable field measurable).aestronglyMeasurable bound
    (Filter.Eventually.of_forall (fun frequency => extendBand_bound field bound nonnegative bounded ((2*Real.pi) • frequency)))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
