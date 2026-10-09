import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceNearby
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceRecognition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual Filter
open scoped Topology
noncomputable section

def sourceResponse (p : BandPoint) : Space →L[ℝ] Path :=
  (1 - volterraHessian p).inverse.comp pathConst

theorem nearbySolution_eq_rawPath (p : BandPoint) :
    nearbySolution p =ᶠ[𝓝 (ContinuousParameterMap.initialMap 0 4 p.val)] rawPath := by
  filter_upwards [nearbySolution_solves p, nearbySolution_in_cube p] with x equation inside
  exact solvedPath_eq_rawPath x (nearbySolution p x) equation inside

theorem rawPath_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt rawPath (sourceResponse p) (ContinuousParameterMap.initialMap 0 4 p.val) := by
  have generated : HasStrictFDerivAt (nearbySolution p) (sourceResponse p)
      (ContinuousParameterMap.initialMap 0 4 p.val) := by
    simpa only [sourceResponse, residualDerivative, ContinuousLinearMap.coprod_comp_inr,
      ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.comp_neg, neg_neg] using
      nearbySolution_hasStrictFDerivAt p
  exact generated.congr_of_eventuallyEq (nearbySolution_eq_rawPath p)

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
