import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ErrorDefect
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeError

open SourceGaussianModel ContinuousGradient ContinuousParameterMap WholeCellPartition Set
open scoped NNReal
noncomputable section

def parameterLine (base : Point) (t : ℝ) : Point := base + t • Pi.single 2 1
def finiteTrajectory (base : Point) (t : ℝ) : Point := parameterMap 0 4 (parameterLine base t)
def finiteVelocity (base : Point) (t : ℝ) : Point := parameterJacobian 0 4 (parameterLine base t) (Pi.single 2 1)

attribute [local irreducible] parameterMap parameterJacobian

theorem parameterLine_hasDerivAt (base : Point) (t : ℝ) :
    HasDerivAt (parameterLine base) (Pi.single 2 1) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [parameterLine, Pi.add_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq, zero_add, one_mul] using
    (hasDerivAt_const t (base i)).add ((hasDerivAt_id t).mul_const ((Pi.single (2 : Fin 3) (1 : ℝ) : Point) i))

theorem finiteTrajectory_hasDerivAt (base : Point) (t : ℝ) :
    HasDerivAt (finiteTrajectory base) (finiteVelocity base t) t :=
  (parameterMap_hasFDerivAt 0 4 (parameterLine base t)).comp_hasDerivAt t (parameterLine_hasDerivAt base t)

theorem finiteTrajectory_continuous (base : Point) : Continuous (finiteTrajectory base) :=
  (show Differentiable ℝ (finiteTrajectory base) from
    fun t => (finiteTrajectory_hasDerivAt base t).differentiableAt).continuous

/-- This consumer takes an actual comparison trajectory, not its distance bound. The finite-map
    derivative and defect are supplied by the already generated source map. -/
theorem compare_actual_trajectory (base : Point) (q : Quarter) (a b : ℝ)
    (parameters : ∀ t ∈ Icc a b, parameterLine base t ∈ quarterDomain q)
    (region : Set Point) (K : ℝ≥0) (lipschitz : LipschitzOnWith K sourceGradient region)
    (finiteInside : ∀ t ∈ Ico a b, finiteTrajectory base t ∈ region)
    (actual : ℝ → Point) (continuous : ContinuousOn actual (Icc a b))
    (evolves : ∀ t ∈ Ico a b, HasDerivWithinAt actual (sourceGradient (actual t)) (Ici t) t)
    (actualInside : ∀ t ∈ Ico a b, actual t ∈ region) :
    ∀ t ∈ Icc a b, dist (finiteTrajectory base t) (actual t) ≤
      gronwallBound (dist (finiteTrajectory base a) (actual a)) K (quarterDefectBound q) (t - a) := by
  have comparison := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ => sourceGradient) (s := fun _ => region)
    (f' := finiteVelocity base) (g' := fun t => sourceGradient (actual t))
    (εf := (quarterDefectBound q : ℝ)) (εg := 0)
    (fun _ _ => lipschitz) (finiteTrajectory_continuous base).continuousOn
    (fun t _ => (finiteTrajectory_hasDerivAt base t).hasDerivWithinAt)
    (fun t ht => by
      rw [dist_eq_norm]
      exact actual_defect_norm_le q (parameterLine base t) (parameters t (Ico_subset_Icc_self ht)))
    finiteInside continuous evolves (fun _ _ => by simp only [dist_self, le_refl]) actualInside le_rfl
  simpa only [add_zero] using comparison

end
end LAlanine40K2025.BasinRefinement.TrueTubeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
