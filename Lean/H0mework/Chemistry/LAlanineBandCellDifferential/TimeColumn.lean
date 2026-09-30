import H0mework.Chemistry.LAlanineBandCellDifferential.Domain
import H0mework.Chemistry.LAlanineBandCellDifferential.ParameterMap
import Mathlib.Analysis.Calculus.Deriv.Pi

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandGeometry WholeBandActual
open WholeBandCell0Geometry WholeBandCell0Continuation TrueFlowDifferential Set
noncomputable section

theorem cell0_trueJacobian_time_column (p : Cell0Point) :
    cell0_trueJacobian p (Pi.single 2 1) = sourceGradient (cell0ParameterMap p.val) := by
  have seed_same (t : ℝ) : cellSeed 0 (Function.update p.val 2 t) = cellSeed 0 p.val := by
    simp [cellSeed, bandSeed, bandU]
  have curve_same : cell0ParameterMap ∘ Function.update p.val 2 = rawFlow (cellSeed 0 p.val) := by
    funext t
    change rawFlow (cellSeed 0 (Function.update p.val 2 t)) ((Function.update p.val 2 t) 2) =
      rawFlow (cellSeed 0 p.val) t
    rw [seed_same, Function.update_self]
  have line_inside : MapsTo (Function.update p.val 2) (Icc (-(1/2) : ℝ) (1/2)) (cellDomain 0) :=
    cell0_line_inside p 2
  have parameter_derivative := (cell0_actualMap_hasFDerivWithinAt p).comp_hasDerivWithinAt_of_eq
    (p.val 2) (hasDerivAt_update p.val (2 : Fin 3) (p.val 2)).hasDerivWithinAt
    line_inside (by simp)
  rw [curve_same] at parameter_derivative
  have unique := uniqueDiffOn_Icc (show (-(1/2) : ℝ) < 1/2 by norm_num) _ p.property.2.2
  exact (parameter_derivative.derivWithin unique).symm.trans
    ((cell0_full_original p (p.val 2) p.property.2.2).derivWithin unique)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
