import H0mework.Physics.LowEnergy.PacketField.PoleContinuity
import H0mework.Physics.LowEnergy.PacketField.Reflection
import H0mework.Physics.LowEnergy.PacketField.Lift
import H0mework.Physics.LowEnergy.PacketPairResponse.Measure

/-! The actual radial root and paired native circles generate measurable,
bounded complete pole columns on the physical light ball. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open PacketPairResponse LightSpace
noncomputable section
attribute [local irreducible] poleValue
variable {ι : Type*} [Fintype ι]

def radialPoint (point : LightBand) : RadialBand :=
  ⟨radialMomentum (bandMomentum point),radial_small _ (band_small point)⟩

theorem radialPoint_continuous : Continuous radialPoint :=
  (VertexTensor.radialMomentum_continuous.comp bandMomentum_continuous).subtype_mk _

def bandParameters (point : LightBand) : ℝ×ℝ := pairedParameters (bandMomentum point)

theorem bandParameters_measurable : Measurable bandParameters :=
  pairedParameters_measurable.comp bandMomentum_continuous.measurable

def bandOrientation (point : LightBand) : ℝ := -lineSign (bandMomentum point)

theorem bandOrientation_measurable : Measurable bandOrientation :=
  (lineSign_measurable.comp bandMomentum_continuous.measurable).neg

theorem bandOrientation_bound (point : LightBand) : |bandOrientation point|≤1 := by
  rcases Real.sign_apply_eq (firstNonzero (bandMomentum point)) with negative | zero | positive
  · norm_num [bandOrientation,lineSign,negative]
  · norm_num [bandOrientation,lineSign,zero]
  · norm_num [bandOrientation,lineSign,positive]

def axialColumn (numerator : ι → List PoleTerm) (sign : Bool) (point : LightBand) (row : ι) : ℂ :=
  poleValue (numerator row) sign (bandOrientation point) (radialPoint point).val

def poleColumn (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sign : Bool) (point : LightBand) : ι → ℂ :=
  circleAction circleZ (bandParameters point).2
    (circleAction circleY (bandParameters point).1 (axialColumn numerator sign point))

omit [Fintype ι] in
theorem axialColumn_measurable (numerator : ι → List PoleTerm) (sign : Bool) (row : ι) :
    Measurable (fun point : LightBand => axialColumn numerator sign point row) := by
  have path : Measurable (fun point : LightBand => (radialPoint point,bandOrientation point)) :=
    radialPoint_continuous.measurable.prodMk bandOrientation_measurable
  exact (poleValue_continuous (numerator row) sign).measurable.comp path

theorem poleColumn_measurable (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sign : Bool) (row : ι) : Measurable (fun point : LightBand => poleColumn circleY circleZ numerator sign point row) :=
  circleAction_measurable circleZ _ bandParameters_measurable.snd _
    (fun column => circleAction_measurable circleY _ bandParameters_measurable.fst _
      (axialColumn_measurable numerator sign) column) row

theorem poleColumn_bounded (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm) (sign : Bool) :
    ∃ bound : ι → ℝ, ∀ point : LightBand, ∀ row, ‖poleColumn circleY circleZ numerator sign point row‖≤bound row := by
  choose bound _ bounded using (fun row => poleValue_bounded (numerator row) sign)
  refine ⟨transportedBound circleZ (transportedBound circleY bound),?_⟩
  intro point row
  apply circleAction_bound
  intro column
  apply circleAction_bound
  intro coordinate
  exact bounded coordinate (radialPoint point) (bandOrientation point) (bandOrientation_bound point)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
