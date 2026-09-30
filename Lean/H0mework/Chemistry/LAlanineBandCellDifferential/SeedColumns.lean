import H0mework.Chemistry.LAlanineBandCellDifferential.TimeColumn
import H0mework.Chemistry.LAlanineBandCellDifferential.Variational

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandGeometry WholeBandActual
open WholeBandCell0Geometry TrueFlowDifferential Set
noncomputable section

theorem cell0_trueJacobian_seed_column (p : Cell0Point) (j : Fin 3) (hj : j ≠ 2) :
    cell0_trueJacobian p (Pi.single j 1) =
      cell0_initialFlowDerivative p (cell0_actualParameterTime p)
        (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val (Pi.single j 1)) := by
  have curve_same : cell0ParameterMap ∘ Function.update p.val j =
      (fun q => rawPath (cellSeed 0 q) (cell0_actualParameterTime p)) ∘ Function.update p.val j := by
    funext r
    change rawFlow (cellSeed 0 (Function.update p.val j r)) (Function.update p.val j r 2) =
      rawFlow (cellSeed 0 (Function.update p.val j r)) (p.val 2)
    rw [Function.update_of_ne (Ne.symm hj)]
  have parameter_derivative := (cell0_actualMap_hasFDerivWithinAt p).comp_hasDerivWithinAt_of_eq
    (p.val j) (hasDerivAt_update p.val j (p.val j)).hasDerivWithinAt (cell0_line_inside p j) (by simp)
  rw [curve_same] at parameter_derivative
  have initial_derivative := (cell0_initialFlow_hasStrictFDerivAt p (cell0_actualParameterTime p)).hasFDerivAt.comp
    p.val (bandSeed_hasFDerivAt 0 (Geometry.Source.epsilon 0) p.val)
  have seed_derivative := initial_derivative.comp_hasDerivAt_of_eq
    (p.val j) (hasDerivAt_update p.val j (p.val j)) (by simp)
  have unique := uniqueDiffOn_Icc (cell0_axis_strict j) (p.val j) (cell0_coordinate_mem p j)
  exact (parameter_derivative.derivWithin unique).symm.trans
    (seed_derivative.hasDerivWithinAt.derivWithin unique)

theorem cell0_trueJacobian_decomposition (p : Cell0Point) (h : Point) :
    cell0_trueJacobian p h = cell0_initialFlowDerivative p (cell0_actualParameterTime p)
      (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val h) +
        h 2 • sourceGradient (cell0ParameterMap p.val) := by
  let response : Point →L[ℝ] Point :=
    (cell0_initialFlowDerivative p (cell0_actualParameterTime p)).comp
        (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val) +
      (ContinuousLinearMap.proj 2).smulRight (sourceGradient (cell0ParameterMap p.val))
  have columns (j : Fin 3) : cell0_trueJacobian p (Pi.single j 1) = response (Pi.single j 1) := by
    by_cases hj : j = 2
    · subst j
      rw [cell0_trueJacobian_time_column]
      simp [response, bandSeedDerivative, bandUDerivative]
    · rw [cell0_trueJacobian_seed_column p j hj]
      simp [response, Pi.single_eq_of_ne (Ne.symm hj)]
  have equality : (cell0_trueJacobian p).toLinearMap = response.toLinearMap := by
    apply LinearMap.pi_ext
    intro j r
    have basis : Pi.single j r = r • Pi.single j (1 : ℝ) := by
      ext i
      by_cases hi : i = j <;> simp [hi]
    change cell0_trueJacobian p (Pi.single j r) = response (Pi.single j r)
    rw [basis, map_smul, map_smul, columns]
  exact LinearMap.congr_fun equality h

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
