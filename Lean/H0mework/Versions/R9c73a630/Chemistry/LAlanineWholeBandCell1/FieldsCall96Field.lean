import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCall064.FieldField

/-! The two registered first-initial calls have identical source material and distinct addresses. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCache.Call96

open SourceGaussianModel SourceSignedEvaluator WholeBandSource

theorem same_original_box : callBox 96 = callBox 64 := rfl
theorem same_original_reductions : callReductions 96 = callReductions 64 := rfl
theorem same_original_report : callReportedDensity 96 = callReportedDensity 64 := rfl
theorem same_original_field : recordedCallField 96 = recordedCallField 64 := rfl
theorem registered_keys_distinct : (96 : FullBandCall) ≠ 64 := by decide

theorem actual_field (x : Point) (inside : InRectangle (callBox 96) x) :
    IntervalParameterMap.FieldHolds (recordedCallField 96) x := by
  rw [same_original_field]
  rw [same_original_box] at inside
  exact Call64.actual_field x inside

end LAlanine40K2025.BasinRefinement.WholeBandCache.Call96
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
