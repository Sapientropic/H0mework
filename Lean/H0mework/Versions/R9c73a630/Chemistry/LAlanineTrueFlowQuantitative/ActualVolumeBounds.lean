import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.ActualVolumeRatio
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.SourceSeedBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential TrueFlowGeometry TrueFlowConservation
open TrueTubeWholeActual Set
noncomputable section

theorem determinant_exponential_window :
    (2 / 3 : ℝ) < Real.exp (-(3 / 8) : ℝ) ∧ Real.exp (3 / 8 : ℝ) < 3 / 2 := by
  have upper : Real.exp (3 / 8 : ℝ) < 3 / 2 :=
    (Real.exp_lt_two_add_div_two_sub (x := (3 / 8 : ℝ)) (by norm_num) (by norm_num)).trans_le
      (by norm_num)
  refine ⟨?_, upper⟩
  rw [Real.exp_neg]
  have lower := one_div_lt_one_div_of_lt (Real.exp_pos (3 / 8 : ℝ)) upper
  norm_num at lower
  exact lower

theorem evolvingJacobian_det_bounds (p : BandPoint) (s : Time) :
    (1 / 80000 : ℝ) < (evolvingJacobian p s).det ∧
      (evolvingJacobian p s).det < 31 / 1000000 := by
  have seed := seedFlowDerivative_det_bounds p
  have positive := seedFlowDerivative_det_pos p
  have compared := actual_determinant_seed_bounds p s
  have lower := mul_lt_mul_of_pos_right determinant_exponential_window.1 positive
  have upper := mul_lt_mul_of_pos_right determinant_exponential_window.2 positive
  constructor
  · apply lt_of_lt_of_le _ compared.1
    exact (show (1 / 80000 : ℝ) < (2 / 3) * LinearMap.det (seedFlowDerivative p).toLinearMap by
      linarith [seed.1]).trans lower
  · apply lt_of_le_of_lt compared.2
    exact upper.trans (by linarith [seed.2])

theorem trueJacobian_det_bounds (p : BandPoint) :
    (1 / 80000 : ℝ) < LinearMap.det (trueJacobian p).toLinearMap ∧
      LinearMap.det (trueJacobian p).toLinearMap < 31 / 1000000 := by
  rw [← evolvingJacobian_det_is_actual]
  exact evolvingJacobian_det_bounds p (actualParameterTime p)

theorem actualDerivative_det_bounds (p : Point) (inside : p ∈ WholeCellPartition.fullDomain) :
    (1 / 80000 : ℝ) < (actualDerivative p).det ∧ (actualDerivative p).det < 31 / 1000000 := by
  rw [actualDerivative_eq_trueJacobian ⟨p, inside⟩]
  exact trueJacobian_det_bounds ⟨p, inside⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
