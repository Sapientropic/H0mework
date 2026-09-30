import H0mework.Chemistry.LAlanineBandContinuation.ParameterDomain
import H0mework.Chemistry.LAlanineBandContinuation.ParameterParameterMap
import H0mework.Chemistry.LAlanineBandContinuation.DifferentialEvolution
import Mathlib.Analysis.Calculus.Deriv.Pi

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandSource WholeBandGeometry
open TrueFlowDifferential WholeBandContinuation WholeBandContinuationDifferential Set
noncomputable section

theorem trueJacobian_time_column (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    trueJacobian c p (Pi.single 2 1) = sourceGradient (sourceParameterMap c p) := by
  have seed_same (t : ℝ) : cellSeed c (Function.update p 2 t) = cellSeed c p := by
    simp [cellSeed, bandSeed, bandU]
  have curve_same : sourceParameterMap c ∘ Function.update p 2 = rawFlow (cellSeed c p) := by
    funext t
    change rawFlow (cellSeed c (Function.update p 2 t)) ((Function.update p 2 t) 2) = rawFlow (cellSeed c p) t
    rw [seed_same, Function.update_self]
  have mapped : MapsTo (Function.update p 2) (Icc (-(1/2) : ℝ) (1/2)) (cellDomain c) :=
    line_inside c p inside 2
  have parameter_derivative := (actualMap_hasFDerivWithinAt c fields bounds p inside).comp_hasDerivWithinAt_of_eq
    (p 2) (hasDerivAt_update p (2 : Fin 3) (p 2)).hasDerivWithinAt mapped (by simp)
  rw [curve_same] at parameter_derivative
  have unique := uniqueDiffOn_Icc (show (-(1/2) : ℝ) < 1/2 by norm_num) _ inside.2.2
  exact (parameter_derivative.derivWithin unique).symm.trans
    ((full_original c fields p inside (p 2) inside.2.2).derivWithin unique)

theorem trueJacobian_seed_column (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (j : Fin 3) (hj : j ≠ 2) :
    trueJacobian c p (Pi.single j 1) = initialFlowDerivative c p (actualParameterTime c p inside)
      (bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p (Pi.single j 1)) := by
  have curve_same : sourceParameterMap c ∘ Function.update p j =
      (fun q => rawPath (cellSeed c q) (actualParameterTime c p inside)) ∘ Function.update p j := by
    funext r
    change rawFlow (cellSeed c (Function.update p j r)) (Function.update p j r 2) =
      rawFlow (cellSeed c (Function.update p j r)) (p 2)
    rw [Function.update_of_ne (Ne.symm hj)]
  have parameter_derivative := (actualMap_hasFDerivWithinAt c fields bounds p inside).comp_hasDerivWithinAt_of_eq
    (p j) (hasDerivAt_update p j (p j)).hasDerivWithinAt (line_inside c p inside j) (by simp)
  rw [curve_same] at parameter_derivative
  have initial_derivative := (initialFlow_hasStrictFDerivAt c fields bounds p inside
    (actualParameterTime c p inside)).hasFDerivAt.comp p
      (bandSeed_hasFDerivAt (cellSegment c) (Geometry.Source.epsilon 0) p)
  have seed_derivative := initial_derivative.comp_hasDerivAt_of_eq
    (p j) (hasDerivAt_update p j (p j)) (by simp)
  have unique := uniqueDiffOn_Icc (axis_strict c j) (p j) (coordinate_mem c p inside j)
  exact (parameter_derivative.derivWithin unique).symm.trans
    (seed_derivative.hasDerivWithinAt.derivWithin unique)

theorem trueJacobian_decomposition (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (h : Point) :
    trueJacobian c p h = initialFlowDerivative c p (actualParameterTime c p inside)
      (bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h) +
        h 2 • sourceGradient (sourceParameterMap c p) := by
  let response : Point →L[ℝ] Point :=
    (initialFlowDerivative c p (actualParameterTime c p inside)).comp
        (bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p) +
      (ContinuousLinearMap.proj 2).smulRight (sourceGradient (sourceParameterMap c p))
  have columns (j : Fin 3) : trueJacobian c p (Pi.single j 1) = response (Pi.single j 1) := by
    by_cases hj : j = 2
    · subst j
      rw [trueJacobian_time_column c fields bounds p inside]
      simp [response, bandSeedDerivative, bandUDerivative]
    · rw [trueJacobian_seed_column c fields bounds p inside j hj]
      simp [response, Pi.single_eq_of_ne (Ne.symm hj)]
  have equality : (trueJacobian c p).toLinearMap = response.toLinearMap := by
    apply LinearMap.pi_ext
    intro j r
    have basis : Pi.single j r = r • Pi.single j (1 : ℝ) := by
      ext i
      by_cases hi : i = j <;> simp [hi]
    change trueJacobian c p (Pi.single j r) = response (Pi.single j r)
    rw [basis, map_smul, map_smul, columns]
  exact LinearMap.congr_fun equality h

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
