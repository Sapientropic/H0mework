import H0mework.Versions.R9c73a630.Chemistry.LAlanineFlow.Source

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousFlow

open SourceGaussianModel ContinuousGradient Set Metric ODE
open scoped Topology NNReal
open scoped BigOperators

noncomputable section

def initialAmplification : ℝ≥0 :=
  Classical.choose (FunSpace.exists_forall_closedBall_funSpace_dist_le_mul sourcePicard)

theorem fixedPoint_distance (first second : InitialPoint) :
    dist (fixedPoint first) (fixedPoint second) ≤ (initialAmplification : ℝ) * dist first.val second.val :=
  Classical.choose_spec (FunSpace.exists_forall_closedBall_funSpace_dist_le_mul sourcePicard)
    first.val second.val first.property second.property (fixedPoint first) (fixedPoint second)
    (fixedPoint_isFixed first) (fixedPoint_isFixed second)

theorem initial_dist_bound (first second : InitialPoint) (time : ℝ)
    (inside : time ∈ Icc (-timeRadius) timeRadius) :
    dist (sourceFlow first time) (sourceFlow second time) ≤
      (initialAmplification : ℝ) * dist first.val second.val := by
  let : Nonempty (Icc (-timeRadius) timeRadius) := ⟨zeroTime⟩
  have bound : dist (fixedPoint first).toContinuousMap (fixedPoint second).toContinuousMap ≤
      (initialAmplification : ℝ) * dist first.val second.val := fixedPoint_distance first second
  simpa only [sourceFlow, FunSpace.compProj_of_mem inside, FunSpace.toContinuousMap_apply_eq_apply] using
    (ContinuousMap.dist_le_iff_of_nonempty.mp bound ⟨time, inside⟩)

theorem forward_gronwall (first second : InitialPoint) (time : ℝ)
    (inside : time ∈ Icc 0 timeRadius) :
    dist (sourceFlow first time) (sourceFlow second time) ≤
      dist first.val second.val * Real.exp ((sourceLipschitzBound : ℝ) * time) := by
  have within : Ico 0 time ⊆ Ioo (-timeRadius) timeRadius := by
    intro t ht
    constructor <;> linarith [timeRadius_positive, inside.1, inside.2, ht.1, ht.2]
  have bound := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ => sourceGradient) (s := fun _ => sourceCube)
    (fun _ _ => sourceGradient_lipschitzOn_cube)
    (sourceFlow_continuous first).continuousOn
    (fun t ht => (sourceFlow_evolves first t (within ht)).hasDerivWithinAt)
    (fun t _ => sourceFlow_stays first t)
    (sourceFlow_continuous second).continuousOn
    (fun t ht => (sourceFlow_evolves second t (within ht)).hasDerivWithinAt)
    (fun t _ => sourceFlow_stays second t)
    (by simpa only [sourceFlow_starts] using
      (le_rfl : dist first.val second.val ≤ dist first.val second.val))
    time ⟨inside.1, le_rfl⟩
  simpa only [sub_zero] using bound

/-- Uniqueness is a consumer of another curve's ODE, never an input to the generated source flow. -/
theorem same_field_unique (initial : InitialPoint) (curve : ℝ → Point)
    (starts : curve 0 = initial.val)
    (evolves : ∀ t ∈ Ioo (-timeRadius) timeRadius,
      HasDerivAt curve (sourceGradient (curve t)) t ∧ curve t ∈ sourceCube) :
    EqOn curve (sourceFlow initial) (Ioo (-timeRadius) timeRadius) :=
  ODE_solution_unique_of_mem_Ioo (fun _ _ => sourceGradient_lipschitzOn_cube)
    (by constructor <;> linarith [timeRadius_positive]) evolves
    (fun t ht => ⟨sourceFlow_evolves initial t ht, sourceFlow_stays initial t⟩)
    (starts.trans (sourceFlow_starts initial).symm)

theorem injective_at (time : ℝ) (inside : time ∈ Ioo (-timeRadius) timeRadius) :
    Function.Injective (fun initial : InitialPoint => sourceFlow initial time) := by
  intro first second equality
  have coincides := ODE_solution_unique_of_mem_Ioo
    (fun _ _ => sourceGradient_lipschitzOn_cube) inside
    (fun t ht => ⟨sourceFlow_evolves first t ht, sourceFlow_stays first t⟩)
    (fun t ht => ⟨sourceFlow_evolves second t ht, sourceFlow_stays second t⟩) equality
  apply Subtype.ext
  simpa only [sourceFlow_starts] using
    (coincides (show 0 ∈ Ioo (-timeRadius) timeRadius by constructor <;> linarith [timeRadius_positive]))

theorem densityAlongFlow_derivative (initial : InitialPoint) (time : ℝ)
    (inside : time ∈ Ioo (-timeRadius) timeRadius) :
    HasDerivAt (fun t => sourceDensity (sourceFlow initial t))
      (∑ axis : Fin 3, (sourceGradient (sourceFlow initial time) axis) ^ 2) time := by
  convert! (sourceDensity_hasFDerivAt (sourceFlow initial time)).comp_hasDerivAt time
    (sourceFlow_evolves initial time inside) using 1
  simp only [sourceDensityLinear, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, pow_two]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousFlow
