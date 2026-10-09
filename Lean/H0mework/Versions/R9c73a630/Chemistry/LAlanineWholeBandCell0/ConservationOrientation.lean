import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ConservationCapTransport
import Mathlib.Topology.Order.IntermediateValue

/-!
The original seed frame fixes the orientation. The generated, everywhere nonsingular
continuous Jacobian preserves that orientation through the full closed time window.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeBandCell0Spatial WholeBandCell0Boundary WholeCellBoundary
open Matrix Set MeasureTheory
open scoped Matrix
noncomputable section

theorem cell0_seedFlowDerivative_det (p : Cell0Point) :
    LinearMap.det (cell0_seedFlowDerivative p).toLinearMap =
      bandWidth 0 (Geometry.Source.epsilon 0) (p.val 1) *
        (seedNormal ⬝ᵥ sourceGradient (cellSeed 0 p.val)) := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_three, seedNormal_eq_cross]
  simp [LinearMap.toMatrix'_apply, cell0_seedFlowDerivative, bandSeedDerivative, bandUDerivative,
    cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem cell0_seedFlowDerivative_det_pos (p : Cell0Point) :
    0 < LinearMap.det (cell0_seedFlowDerivative p).toLinearMap := by
  rw [cell0_seedFlowDerivative_det]
  have transverse := cell0_full_transverse p 0 (by constructor <;> norm_num)
  rw [rawFlow_starts] at transverse
  exact mul_pos (cell0_seed_width_positive p) ((by norm_num : (0 : ℝ) < 1/20).trans transverse)

theorem cell0_evolvingJacobian_zero (p : Cell0Point) :
    cell0_evolvingJacobian p 0 = LinearMap.toMatrix' (cell0_seedFlowDerivative p).toLinearMap := by
  ext i j
  change extendPath (cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1)))
    (zeroTime : ℝ) i = cell0_seedFlowDerivative p (Pi.single j 1) i
  rw [extendPath_coe, cell0_sourceResponse_starts]

/-- Nonvanishing and continuity transport the positive original seed orientation to every time. -/
theorem cell0_evolvingJacobian_det_pos (p : Cell0Point) (s : Time) :
    0 < (cell0_evolvingJacobian p s).det := by
  have positive : 0 < (cell0_evolvingJacobian p 0).det := by
    rw [cell0_evolvingJacobian_zero, LinearMap.det_toMatrix']
    exact cell0_seedFlowDerivative_det_pos p
  by_contra failed
  have zero_mem : (0 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by constructor <;> norm_num
  obtain ⟨t, ht, vanished⟩ :=
    (isPreconnected_Icc.intermediate_value s.property zero_mem
      (cell0_evolvingJacobian_det_continuous p).continuousOn) ⟨le_of_not_gt failed, positive.le⟩
  exact cell0_evolvingJacobian_det_ne_zero p ⟨t, ht⟩ vanished

theorem cell0_trueJacobian_det_pos (p : Cell0Point) :
    0 < LinearMap.det (cell0_trueJacobian p).toLinearMap := by
  rw [← cell0_evolvingJacobian_det_is_actual]
  exact cell0_evolvingJacobian_det_pos p (cell0_actualParameterTime p)

theorem cell0_true_upper_cap_flux_pos (p : FacePoint) (inside : p ∈ cell0_faceDomain 2) :
    0 < cell0_trueFaceFlux (2, true) p inside := by
  rw [cell0_trueCapFlux_eq_oriented_det _ _ _ rfl]
  simpa using cell0_trueJacobian_det_pos (cell0_trueFaceParameter (2, true) p inside)

theorem cell0_true_lower_cap_flux_neg (p : FacePoint) (inside : p ∈ cell0_faceDomain 2) :
    cell0_trueFaceFlux (2, false) p inside < 0 := by
  rw [cell0_trueCapFlux_eq_oriented_det _ _ _ rfl]
  simpa using neg_lt_zero.mpr (cell0_trueJacobian_det_pos (cell0_trueFaceParameter (2, false) p inside))

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
