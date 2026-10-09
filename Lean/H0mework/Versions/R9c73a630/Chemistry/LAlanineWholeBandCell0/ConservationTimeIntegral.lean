import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ConservationVolumeEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeCellBoundary
open Matrix Set MeasureTheory
noncomputable section

theorem cell0_evolvingJacobian_continuous (p : Cell0Point) : Continuous (cell0_evolvingJacobian p) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp
    (continuous_extendPath (cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1))))

theorem cell0_evolvingJacobian_det_continuous (p : Cell0Point) :
    Continuous (fun t => (cell0_evolvingJacobian p t).det) :=
  (cell0_evolvingJacobian_continuous p).matrix_det

def cell0_signedVolumeRate (p : Cell0Point) (t : ℝ) : ℝ :=
  laplacian sourceTerms densityMatrix (rawFlow (cellSeed 0 p.val) t) * (cell0_evolvingJacobian p t).det

theorem cell0_signedVolumeRate_continuousOn (p : Cell0Point) :
    ContinuousOn (cell0_signedVolumeRate p) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
  ((laplacian_contDiff sourceTerms densityMatrix 0).continuous.comp_continuousOn
    (cell0_full_original p).continuousOn).mul (cell0_evolvingJacobian_det_continuous p).continuousOn

/-- The original Laplacian-volume current pays the difference between the two time endpoints. -/
theorem cell0_actual_time_integral_eq_det_difference (p : Cell0Point) :
    (∫ t in (-(1 / 2) : ℝ)..(1 / 2), cell0_signedVolumeRate p t) =
      (cell0_evolvingJacobian p (1 / 2)).det - (cell0_evolvingJacobian p (-(1 / 2))).det := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (cell0_evolvingJacobian_det_continuous p).continuousOn
  · intro t inside
    exact (cell0_evolvingJacobian_determinant_evolution p ⟨t, Ioo_subset_Icc_self inside⟩).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)
  · exact (cell0_signedVolumeRate_continuousOn p).intervalIntegrable_of_Icc (by norm_num)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
