import H0mework.Chemistry.LAlanineBandCall128.FieldRegistered

/-! Two original call addresses share their input rectangle and full source calculation. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Call160

open SourceGaussianModel SourceSignedEvaluator WholeBandSource WholeBandMatrix

theorem same_original_box : callBox 160 = callBox 128 := rfl
theorem same_original_reductions : callReductions 160 = callReductions 128 := rfl
theorem same_original_report : callReportedDensity 160 = callReportedDensity 128 := rfl
theorem same_original_field : recordedCallField 160 = recordedCallField 128 := rfl
theorem registered_keys_distinct : (160 : FullBandCall) ≠ 128 := by decide +kernel

theorem calculated_field_holds (x : Point) (inside : InRectangle (callBox 160) x) :
    IntervalParameterMap.FieldHolds (calculatedField Call128.matrixRows) x := by
  rw [same_original_box] at inside
  exact Call128.calculated_field_holds x inside

theorem actual_field (x : Point) (inside : InRectangle (callBox 160) x) :
    IntervalParameterMap.FieldHolds (recordedCallField 160) x := by
  rw [same_original_field]
  rw [same_original_box] at inside
  exact Call128.actual_field x inside

end LAlanine40K2025.BasinRefinement.WholeBandCell2.Call160
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
