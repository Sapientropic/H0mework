import H0mework.Chemistry.LAlanineParametric.Seed
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousSeed

open SourceGaussianModel
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry

noncomputable section

def slope (values : Data.Knot → ℚ) (segment : Segment) : ℝ :=
  ((values (lastKnot segment) : ℝ) - values (firstKnot segment)) /
    ((knotCoordinate (lastKnot segment) : ℝ) - knotCoordinate (firstKnot segment))

theorem interpolate_hasDerivAt (values : Data.Knot → ℚ) (segment : Segment) (v : ℝ) :
    HasDerivAt (interpolate values segment) (slope values segment) v := by
  have fraction := ((hasDerivAt_id v).sub_const (knotCoordinate (firstKnot segment) : ℝ)).div_const
    ((knotCoordinate (lastKnot segment) : ℝ) - knotCoordinate (firstKnot segment))
  convert! ((fraction.const_sub 1).mul_const (values (firstKnot segment) : ℝ)).add
    (fraction.mul_const (values (lastKnot segment) : ℝ)) using 1
  unfold slope
  ring

def bandUDerivative (segment : Segment) (epsilon : ℝ) (p : Point) : Point →L[ℝ] ℝ :=
  bandWidth segment epsilon (p 1) • ContinuousLinearMap.proj 0 +
    (slope Source.lower segment + p 0 * (slope Source.upper segment - slope Source.lower segment)) •
      ContinuousLinearMap.proj 1

def bandSeedDerivative (segment : Segment) (epsilon : ℝ) (p : Point) : Point →L[ℝ] Point :=
  (bandUDerivative segment epsilon p).smulRight (basisVector 0) +
    (ContinuousLinearMap.proj 1).smulRight (basisVector 1)

theorem bandU_hasFDerivAt (segment : Segment) (epsilon : ℝ) (p : Point) :
    HasFDerivAt (bandU segment epsilon) (bandUDerivative segment epsilon p) p := by
  have lower := (interpolate_hasDerivAt Source.lower segment (p 1)).comp_hasFDerivAt p
    (ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ).hasFDerivAt
  have upper := (interpolate_hasDerivAt Source.upper segment (p 1)).comp_hasFDerivAt p
    (ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ).hasFDerivAt
  have width := (upper.sub lower).add_const (2 * epsilon)
  have alpha := (ContinuousLinearMap.proj (0 : Fin 3) : Point →L[ℝ] ℝ).hasFDerivAt (x := p)
  convert! (lower.sub_const epsilon).add (alpha.mul width) using 1
  ext q
  simp only [bandUDerivative, bandWidth, add_apply, smul_apply, sub_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Function.comp_apply, Pi.sub_apply]
  ring

theorem bandSeed_hasFDerivAt (segment : Segment) (epsilon : ℝ) (p : Point) :
    HasFDerivAt (bandSeed segment epsilon) (bandSeedDerivative segment epsilon p) p := by
  have first := (bandU_hasFDerivAt segment epsilon p).smul_const (basisVector 0)
  have second := ((ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ).hasFDerivAt (x := p)).smul_const
    (basisVector 1)
  convert! (first.const_add centre).add second using 1

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousSeed
