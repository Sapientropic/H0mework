import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.FlowSourceMeeting
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.FlowPlane

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential Set
noncomputable section

private theorem rawFlow_meeting_not_lt (p q : Point)
    (p_start : planeCoordinate p = 0) (q_start : planeCoordinate q = 0)
    (p_rises : StrictMonoOn (fun t => planeCoordinate (rawFlow p t)) (Icc (-(1/2 : ℝ)) (1/2)))
    (q_rises : StrictMonoOn (fun t => planeCoordinate (rawFlow q t)) (Icc (-(1/2 : ℝ)) (1/2)))
    (a b : Time) (earlier : (a : ℝ) < b) (meeting : rawFlow p a = rawFlow q b) : False := by
  have zero_mem : (0 : ℝ) ∈ Icc (-(1/2 : ℝ)) (1/2) := by constructor <;> norm_num
  by_cases nonnegative : 0 ≤ (a : ℝ)
  · have returns := rawFlow_meeting_nonneg q p b a nonnegative earlier.le meeting.symm
    have difference_mem : (b : ℝ) - a ∈ Icc (-(1/2 : ℝ)) (1/2) := by
      constructor <;> linarith [b.property.2]
    have rise := q_rises zero_mem difference_mem (sub_pos.mpr earlier)
    have impossible : (0 : ℝ) < 0 := by
      simpa only [returns, rawFlow_starts, p_start, q_start] using rise
    exact lt_irrefl 0 impossible
  · by_cases nonpositive : (b : ℝ) ≤ 0
    · have returns := rawFlow_meeting_nonpos p q a b nonpositive earlier.le meeting
      have difference_mem : (a : ℝ) - b ∈ Icc (-(1/2 : ℝ)) (1/2) := by
        constructor <;> linarith [a.property.1]
      have rise := p_rises difference_mem zero_mem (sub_neg.mpr earlier)
      have impossible : (0 : ℝ) < 0 := by
        simpa only [returns, rawFlow_starts, p_start, q_start] using rise
      exact lt_irrefl 0 impossible
    · have left : planeCoordinate (rawFlow p a) < 0 := by
        simpa only [rawFlow_starts, p_start] using
          p_rises a.property zero_mem (lt_of_not_ge nonnegative)
      have right : 0 < planeCoordinate (rawFlow q b) := by
        simpa only [rawFlow_starts, q_start] using
          q_rises zero_mem b.property (lt_of_not_ge nonpositive)
      rw [meeting] at left
      exact (not_lt_of_ge right.le) left

theorem rawFlow_meeting_time_eq (p q : Point)
    (p_start : planeCoordinate p = 0) (q_start : planeCoordinate q = 0)
    (p_rises : StrictMonoOn (fun t => planeCoordinate (rawFlow p t)) (Icc (-(1/2 : ℝ)) (1/2)))
    (q_rises : StrictMonoOn (fun t => planeCoordinate (rawFlow q t)) (Icc (-(1/2 : ℝ)) (1/2)))
    (a b : Time) (meeting : rawFlow p a = rawFlow q b) : (a : ℝ) = b := by
  rcases lt_trichotomy (a : ℝ) (b : ℝ) with earlier | same | later
  · exact False.elim (rawFlow_meeting_not_lt p q p_start q_start p_rises q_rises a b earlier meeting)
  · exact same
  · exact False.elim (rawFlow_meeting_not_lt q p q_start p_start q_rises p_rises b a later meeting.symm)

theorem rawFlow_meeting_classification (p q : Point)
    (p_start : planeCoordinate p = 0) (q_start : planeCoordinate q = 0)
    (p_rises : StrictMonoOn (fun t => planeCoordinate (rawFlow p t)) (Icc (-(1/2 : ℝ)) (1/2)))
    (q_rises : StrictMonoOn (fun t => planeCoordinate (rawFlow q t)) (Icc (-(1/2 : ℝ)) (1/2)))
    (a b : Time) : rawFlow p a = rawFlow q b ↔ p = q ∧ (a : ℝ) = b := by
  constructor
  · intro meeting
    have time_eq := rawFlow_meeting_time_eq p q p_start q_start p_rises q_rises a b meeting
    have seed_eq : rawFlow p 0 = rawFlow q 0 := by
      by_cases nonnegative : 0 ≤ (b : ℝ)
      · have same := rawFlow_meeting_nonneg p q a b nonnegative time_eq.symm.le meeting
        simpa only [time_eq, sub_self] using same
      · have same := rawFlow_meeting_nonpos p q a b (le_of_lt (lt_of_not_ge nonnegative))
          time_eq.le meeting
        simpa only [time_eq, sub_self] using same
    exact ⟨by simpa only [rawFlow_starts] using seed_eq, time_eq⟩
  · rintro ⟨rfl, same⟩
    rw [same]

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
