import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.FlowSourceMeeting

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual TrueTubeContinuation Set
noncomputable section

theorem fullFlow_meeting_nonneg (p q : BandPoint) (a b : Time)
    (nonnegative : 0 ≤ (b : ℝ)) (ordered : (b : ℝ) ≤ a)
    (meeting : fullFlow p a = fullFlow q b) :
    fullFlow p ((a : ℝ) - b) = fullFlow q 0 :=
  rawFlow_meeting_nonneg (ContinuousParameterMap.initialMap 0 4 p.val)
    (ContinuousParameterMap.initialMap 0 4 q.val) a b nonnegative ordered meeting

theorem fullFlow_meeting_nonpos (p q : BandPoint) (a b : Time)
    (nonpositive : (b : ℝ) ≤ 0) (ordered : (a : ℝ) ≤ b)
    (meeting : fullFlow p a = fullFlow q b) :
    fullFlow p ((a : ℝ) - b) = fullFlow q 0 :=
  rawFlow_meeting_nonpos (ContinuousParameterMap.initialMap 0 4 p.val)
    (ContinuousParameterMap.initialMap 0 4 q.val) a b nonpositive ordered meeting

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
