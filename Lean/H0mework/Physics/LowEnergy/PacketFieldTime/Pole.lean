import H0mework.Physics.LowEnergy.PacketFieldTime.Lift
import H0mework.Physics.LowEnergy.PacketFieldTime.Source

/-! The native finite pole bounds produce the weighted L² operator, and its
application is exactly the existing source spectrum, not a replacement field. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
open FullQuantum FullSpace PacketPairResponse PacketField
noncomputable section
variable {ι : Type*} [Fintype ι]
attribute [local irreducible] poleColumn

def poleBound (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm) (sign : Bool) (row : ι) : ℝ :=
  max ((Classical.choose (poleColumn_bounded circleY circleZ numerator sign)) row) 0

theorem poleBound_nonnegative (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sign : Bool) (row : ι) : 0≤poleBound circleY circleZ numerator sign row := le_max_right _ _

theorem poleBound_bounds (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sign : Bool) (row : ι) (point : LightBand) :
    ‖poleColumn circleY circleZ numerator sign point row‖≤poleBound circleY circleZ numerator sign row :=
  (Classical.choose_spec (poleColumn_bounded circleY circleZ numerator sign) point row).trans (le_max_left _ _)

def poleLift (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm) (sign : Bool) (row : ι) :
    C(LightBand,FullMatterL2) →L[ℂ] FieldSpace FullMatterL2 :=
  weightedLift (fun point => poleColumn circleY circleZ numerator sign point row)
    (poleColumn_measurable circleY circleZ numerator sign row).stronglyMeasurable
    (poleBound circleY circleZ numerator sign row) (poleBound_nonnegative circleY circleZ numerator sign row)
    (poleBound_bounds circleY circleZ numerator sign row)

theorem poleLift_ae (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm) (sign : Bool) (row : ι)
    (field : C(LightBand,FullMatterL2)) :
    poleLift circleY circleZ numerator sign row field=ᵐ[volume]
      physicalBand (fun point => poleColumn circleY circleZ numerator sign point row • field point) :=
  weightedLift_ae _ _ _ _ _ field

theorem polePair_ae (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm) (row : ι)
    (field : Bool → C(LightBand,FullMatterL2)) :
    -(∑ sign : Bool, poleLift circleY circleZ numerator sign row (field sign))=ᵐ[volume]
      physicalBand (fun point => -(∑ sign : Bool, poleColumn circleY circleZ numerator sign point row • field sign point)) := by
  simp only [Fintype.sum_bool]
  filter_upwards [poleLift_ae circleY circleZ numerator true row (field true),
    poleLift_ae circleY circleZ numerator false row (field false),
    Lp.coeFn_add (poleLift circleY circleZ numerator true row (field true))
      (poleLift circleY circleZ numerator false row (field false)),
    Lp.coeFn_neg (poleLift circleY circleZ numerator true row (field true)+
      poleLift circleY circleZ numerator false row (field false))] with frequency plus minus sum neg
  rw [neg]
  simp only [Pi.neg_apply]
  rw [sum]
  simp only [Pi.add_apply]
  rw [plus,minus]
  by_cases inside : ‖(2*Real.pi) • frequency‖≤bandRadius
  · simp only [physicalBand_inside _ _ inside]
  · simp only [physicalBand_outside _ _ inside,add_zero,neg_zero]

theorem spectrum_as_lift (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    spectrum circleY circleZ numerator energy damping positive time row=
      -(∑ sign : Bool, poleLift circleY circleZ numerator sign row (branchCurve energy damping positive sign time)) := by
  apply Lp.ext
  filter_upwards [spectrum_ae circleY circleZ numerator energy damping positive time row,
    polePair_ae circleY circleZ numerator row (fun sign => branchCurve energy damping positive sign time)]
      with frequency source lifted
  rw [source,lifted]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
