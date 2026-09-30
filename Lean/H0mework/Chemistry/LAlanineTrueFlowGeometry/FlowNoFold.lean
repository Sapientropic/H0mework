import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowSourceNoFold
import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowPlane
import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowShiftUniqueness
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedInjective
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceSeedColumns

/-!
The actual transverse section and autonomous-flow uniqueness exclude meetings at distinct
times. Returning equal-time meetings to the section then recovers both seed parameters.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual WholeCellPartition Set
noncomputable section

/-- Same-source transversality and uniqueness classify the original occurrence times. -/
theorem fullFlow_meeting_time_eq (p q : BandPoint) (a b : Time)
    (meeting : fullFlow p a = fullFlow q b) : (a : ℝ) = b :=
  rawFlow_meeting_time_eq (ContinuousParameterMap.initialMap 0 4 p.val)
    (ContinuousParameterMap.initialMap 0 4 q.val) (seed_plane_zero p.val) (seed_plane_zero q.val)
    (fullFlow_plane_strictMono p) (fullFlow_plane_strictMono q) a b meeting

/-- The full actual parameter map has no folds on the original closed parameter carrier. -/
theorem trueParameterMap_injective :
    Function.Injective (fun p : BandPoint => trueParameterMap p.val) := by
  intro p q meeting
  let a := actualParameterTime p
  let b := actualParameterTime q
  have actual_meeting : fullFlow p a = fullFlow q b := meeting
  have time_eq : (a : ℝ) = b := fullFlow_meeting_time_eq p q a b actual_meeting
  have seed_eq : fullFlow p 0 = fullFlow q 0 := by
    by_cases nonnegative : 0 ≤ (b : ℝ)
    · have same := fullFlow_meeting_nonneg p q a b nonnegative time_eq.symm.le actual_meeting
      simpa only [time_eq, sub_self] using same
    · have same := fullFlow_meeting_nonpos p q a b (le_of_lt (lt_of_not_ge nonnegative))
        time_eq.le actual_meeting
      simpa only [time_eq, sub_self] using same
  rw [fullFlow_starts, fullFlow_starts] at seed_eq
  have coordinates := seed_coordinates_of_eq p q seed_eq
  apply Subtype.ext
  funext i
  fin_cases i
  · exact coordinates.1
  · exact coordinates.2
  · exact time_eq

theorem trueParameterMap_injOn : InjOn trueParameterMap fullDomain := by
  intro p hp q hq meeting
  have same : (⟨p, hp⟩ : BandPoint) = ⟨q, hq⟩ := trueParameterMap_injective meeting
  exact congrArg Subtype.val same

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
