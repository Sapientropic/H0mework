import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceCapTransport
import Mathlib.Topology.Order.IntermediateValue

/-!
The original seed frame fixes the orientation. The generated, everywhere nonsingular
continuous Jacobian preserves that orientation through the full closed time window.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowBoundary TrueTubeActual TrueTubeWholeActual WholeCellBoundary Set Matrix
open scoped Matrix
noncomputable section

theorem seedFlowDerivative_det (p : BandPoint) :
    LinearMap.det (seedFlowDerivative p).toLinearMap =
      bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) *
        (seedNormal ⬝ᵥ sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val)) := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_three, seedNormal_eq_cross]
  simp [LinearMap.toMatrix'_apply, seedFlowDerivative, bandSeedDerivative, bandUDerivative,
    cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem seedFlowDerivative_det_pos (p : BandPoint) :
    0 < LinearMap.det (seedFlowDerivative p).toLinearMap := by
  rw [seedFlowDerivative_det]
  exact mul_pos (actual_seed_width_positive p)
    (original_gradient_transverse (ContinuousParameterMap.initialMap 0 4 p.val)
      ((TrueTubeChecks.initial_field_eq 0).symm ▸ actual_seed_initial 0 p.val p.property))

theorem evolvingJacobian_zero (p : BandPoint) :
    evolvingJacobian p 0 = LinearMap.toMatrix' (seedFlowDerivative p).toLinearMap := by
  ext i j
  change extendPath (sourceResponse p (seedFlowDerivative p (Pi.single j 1)))
    (zeroTime : ℝ) i = seedFlowDerivative p (Pi.single j 1) i
  rw [extendPath_coe, sourceResponse_starts]

/-- Nonvanishing and continuity transport the positive original seed orientation to every time. -/
theorem evolvingJacobian_det_pos (p : BandPoint) (s : Time) :
    0 < (evolvingJacobian p s).det := by
  have positive : 0 < (evolvingJacobian p 0).det := by
    rw [evolvingJacobian_zero, LinearMap.det_toMatrix']
    exact seedFlowDerivative_det_pos p
  by_contra failed
  have zero_mem : (0 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by constructor <;> norm_num
  obtain ⟨t, ht, vanished⟩ :=
    (isPreconnected_Icc.intermediate_value s.property zero_mem
      (evolvingJacobian_det_continuous p).continuousOn) ⟨le_of_not_gt failed, positive.le⟩
  exact evolvingJacobian_det_ne_zero p ⟨t, ht⟩ vanished

theorem trueJacobian_det_pos (p : BandPoint) :
    0 < LinearMap.det (trueJacobian p).toLinearMap := by
  rw [← evolvingJacobian_det_is_actual]
  exact evolvingJacobian_det_pos p (actualParameterTime p)

theorem true_upper_cap_flux_pos (p : FacePoint) (inside : p ∈ faceDomain 2) :
    0 < trueFaceFlux (2, true) p inside := by
  rw [trueCapFlux_eq_oriented_det _ _ _ rfl]
  simpa using trueJacobian_det_pos (trueFaceParameter (2, true) p inside)

theorem true_lower_cap_flux_neg (p : FacePoint) (inside : p ∈ faceDomain 2) :
    trueFaceFlux (2, false) p inside < 0 := by
  rw [trueCapFlux_eq_oriented_det _ _ _ rfl]
  simpa using neg_lt_zero.mpr (trueJacobian_det_pos (trueFaceParameter (2, false) p inside))

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
