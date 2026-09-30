import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceVolumeEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient TrueFlowDifferential
open TrueFlowGeometry TrueTubeWholeActual Set MeasureTheory
open scoped Interval
noncomputable section

theorem evolvingJacobian_continuous (p : BandPoint) : Continuous (evolvingJacobian p) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp
    (continuous_extendPath (sourceResponse p (seedFlowDerivative p (Pi.single j 1))))

theorem evolvingJacobian_det_continuous (p : BandPoint) :
    Continuous (fun t => (evolvingJacobian p t).det) :=
  (evolvingJacobian_continuous p).matrix_det

def signedVolumeRate (p : BandPoint) (t : ℝ) : ℝ :=
  laplacian sourceTerms densityMatrix (fullFlow p t) * (evolvingJacobian p t).det

theorem signedVolumeRate_continuousOn (p : BandPoint) :
    ContinuousOn (signedVolumeRate p) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
  ((laplacian_contDiff sourceTerms densityMatrix 0).continuous.comp_continuousOn
    (fullFlow_original p).continuousOn).mul (evolvingJacobian_det_continuous p).continuousOn

/-- The original Laplacian-volume current pays the difference between the two time endpoints. -/
theorem actual_time_integral_eq_det_difference (p : BandPoint) :
    (∫ t in (-(1 / 2) : ℝ)..(1 / 2), signedVolumeRate p t) =
      (evolvingJacobian p (1 / 2)).det - (evolvingJacobian p (-(1 / 2))).det := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (evolvingJacobian_det_continuous p).continuousOn
  · intro t inside
    exact (evolvingJacobian_determinant_evolution p ⟨t, Ioo_subset_Icc_self inside⟩).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)
  · exact (signedVolumeRate_continuousOn p).intervalIntegrable_of_Icc (by norm_num)

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
