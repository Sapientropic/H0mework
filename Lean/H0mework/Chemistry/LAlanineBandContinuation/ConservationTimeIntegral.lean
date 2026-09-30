import H0mework.Chemistry.LAlanineBandContinuation.ConservationVolumeEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandGeometry
open TrueFlowDifferential WholeBandContinuation WholeBandContinuationDifferential
open WholeBandContinuationParameter Matrix Set MeasureTheory
noncomputable section

theorem evolvingJacobian_continuous (c : FullBandCell) (p : Point) : Continuous (evolvingJacobian c p) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp
    (continuous_extendPath (sourceResponse c p (seedFlowDerivative c p (Pi.single j 1))))

theorem evolvingJacobian_det_continuous (c : FullBandCell) (p : Point) :
    Continuous (fun t => (evolvingJacobian c p t).det) := (evolvingJacobian_continuous c p).matrix_det

def signedVolumeRate (c : FullBandCell) (p : Point) (t : ℝ) : ℝ :=
  laplacian sourceTerms densityMatrix (rawFlow (cellSeed c p) t) * (evolvingJacobian c p t).det

theorem signedVolumeRate_continuousOn (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    ContinuousOn (signedVolumeRate c p) (Icc (-(1/2 : ℝ)) (1/2)) :=
  ((laplacian_contDiff sourceTerms densityMatrix 0).continuous.comp_continuousOn
    (full_original c fields p inside).continuousOn).mul (evolvingJacobian_det_continuous c p).continuousOn

theorem actual_time_integral_eq_det_difference (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    (∫ t in (-(1/2 : ℝ))..(1/2), signedVolumeRate c p t) =
      (evolvingJacobian c p (1/2)).det - (evolvingJacobian c p (-(1/2))).det := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (evolvingJacobian_det_continuous c p).continuousOn
  · intro t ht
    exact (evolvingJacobian_determinant_evolution c fields bounds p inside ⟨t,Ioo_subset_Icc_self ht⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact (signedVolumeRate_continuousOn c fields p inside).intervalIntegrable_of_Icc (by norm_num)

end
end LAlanine40K2025.BasinRefinement.WholeBandConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
