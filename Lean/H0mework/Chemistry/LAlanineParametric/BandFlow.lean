import H0mework.Chemistry.LAlanineParametric.Seed
import H0mework.Chemistry.LAlanineFlow.Restart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousBandFlow

open SourceGaussianModel ContinuousGradient ContinuousSeed ContinuousFlow Set Metric
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry

noncomputable section

def SeedParameters (segment : Segment) : Type :=
  {p : Point // p 0 ∈ Icc (0 : ℝ) 1 ∧
    p 1 ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))}

def generatedBandInitial (run : Data.RunIndex) (segment : Segment) (p : SeedParameters segment) : InitialPoint :=
  ⟨bandSeed segment (Source.epsilon run) p.val,
    halfBall_subset_initialBall (bandSeed_source_neighbourhood segment run p.val p.property.1 p.property.2)⟩

def generatedBandFlow (run : Data.RunIndex) (segment : Segment) (p : SeedParameters segment) : ℝ → Point :=
  sourceFlow (generatedBandInitial run segment p)

theorem generatedBandFlow_starts (run : Data.RunIndex) (segment : Segment) (p : SeedParameters segment) :
    generatedBandFlow run segment p 0 = bandSeed segment (Source.epsilon run) p.val :=
  sourceFlow_starts _

theorem generatedBandFlow_evolves (run : Data.RunIndex) (segment : Segment) (p : SeedParameters segment)
    (time : ℝ) (inside : time ∈ Ioo (-timeRadius) timeRadius) :
    HasDerivAt (generatedBandFlow run segment p) (sourceGradient (generatedBandFlow run segment p time)) time ∧
      generatedBandFlow run segment p time ∈ sourceCube :=
  ⟨sourceFlow_evolves _ time inside, sourceFlow_stays _ time⟩

theorem generatedBandFlow_separates (run : Data.RunIndex) (segment : Segment)
    (first second : SeedParameters segment) (time : ℝ) (inside : time ∈ Ioo (-timeRadius) timeRadius)
    (different : bandSeed segment (Source.epsilon run) first.val ≠ bandSeed segment (Source.epsilon run) second.val) :
    generatedBandFlow run segment first time ≠ generatedBandFlow run segment second time := by
  intro equality
  exact different (congrArg Subtype.val ((injective_at time inside) equality))

theorem generatedBandFlow_distance (run : Data.RunIndex) (segment : Segment)
    (first second : SeedParameters segment) (time : ℝ) (inside : time ∈ Icc 0 timeRadius) :
    dist (generatedBandFlow run segment first time) (generatedBandFlow run segment second time) ≤
      dist (bandSeed segment (Source.epsilon run) first.val) (bandSeed segment (Source.epsilon run) second.val) *
        Real.exp ((sourceLipschitzBound : ℝ) * time) :=
  forward_gronwall _ _ time inside

theorem generatedBandFlow_restart (run : Data.RunIndex) (segment : Segment) (p : SeedParameters segment)
    (start : ℝ) (inside : start ∈ Icc (-timeRadius / 2) (timeRadius / 2)) :
    EqOn (sourceFlow (restartInitial (generatedBandInitial run segment p)
      (bandSeed_source_neighbourhood segment run p.val p.property.1 p.property.2) start inside))
      (fun time => generatedBandFlow run segment p (start + time)) (Ioo (-timeRadius / 2) (timeRadius / 2)) :=
  safe_restart _ _ start inside

def sourceBandEndpoint (segment : Segment) (side : Fin 2) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    SeedParameters segment :=
  ⟨![(side.val : ℝ), v, 0], by
    constructor
    · change (side.val : ℝ) ∈ Icc (0 : ℝ) 1
      fin_cases side <;> norm_num
    · exact inside⟩

theorem sourceBandEndpoints_different (run : Data.RunIndex) (segment : Segment) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    bandSeed segment (Source.epsilon run) (sourceBandEndpoint segment 0 v inside).val ≠
      bandSeed segment (Source.epsilon run) (sourceBandEndpoint segment 1 v inside).val := by
  have epsilon : (0 : ℝ) < (Source.epsilon run : ℝ) := by
    exact_mod_cast (show ∀ r : Data.RunIndex, 0 < Source.epsilon r from by decide +kernel) run
  have width := bandWidth_positive segment (Source.epsilon run) v epsilon inside
  have basis : (Source.basis 0 0 : ℝ) ≠ 0 := by
    exact_mod_cast (show Source.basis 0 0 ≠ 0 from by decide +kernel)
  intro equality
  have coordinate := congrFun equality 0
  norm_num [bandSeed, bandU, sourceBandEndpoint, basisVector] at coordinate
  rcases coordinate with zeroWidth | zeroBasis
  · exact width.ne' zeroWidth
  · exact basis (by exact_mod_cast zeroBasis)

theorem sourceBandEndpoint_difference (run : Data.RunIndex) (segment : Segment) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    bandSeed segment (Source.epsilon run) (sourceBandEndpoint segment 1 v inside).val -
      bandSeed segment (Source.epsilon run) (sourceBandEndpoint segment 0 v inside).val =
        bandWidth segment (Source.epsilon run) v • basisVector 0 := by
  ext axis
  simp only [bandSeed, bandU, sourceBandEndpoint, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, one_mul, smul_eq_mul]
  ring

theorem sourceBandFlow_noncollapse (run : Data.RunIndex) (segment : Segment) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment)))
    (time : ℝ) (timeInside : time ∈ Ioo (-timeRadius) timeRadius) :
    generatedBandFlow run segment (sourceBandEndpoint segment 0 v inside) time ≠
      generatedBandFlow run segment (sourceBandEndpoint segment 1 v inside) time :=
  generatedBandFlow_separates run segment _ _ time timeInside (sourceBandEndpoints_different run segment v inside)

theorem sourceBandFlow_width_bound (run : Data.RunIndex) (segment : Segment) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment)))
    (time : ℝ) (timeInside : time ∈ Icc 0 timeRadius) :
    dist (generatedBandFlow run segment (sourceBandEndpoint segment 1 v inside) time)
      (generatedBandFlow run segment (sourceBandEndpoint segment 0 v inside) time) ≤
      bandWidth segment (Source.epsilon run) v * ‖basisVector 0‖ *
        Real.exp ((sourceLipschitzBound : ℝ) * time) := by
  have epsilon : (0 : ℝ) < (Source.epsilon run : ℝ) := by
    exact_mod_cast (show ∀ r : Data.RunIndex, 0 < Source.epsilon r from by decide +kernel) run
  have width := bandWidth_positive segment (Source.epsilon run) v epsilon inside
  have bound := generatedBandFlow_distance run segment
    (sourceBandEndpoint segment 1 v inside) (sourceBandEndpoint segment 0 v inside) time timeInside
  have initial_distance :
      dist (bandSeed segment (Source.epsilon run) (sourceBandEndpoint segment 1 v inside).val)
        (bandSeed segment (Source.epsilon run) (sourceBandEndpoint segment 0 v inside).val) =
      bandWidth segment (Source.epsilon run) v * ‖basisVector 0‖ := by
    rw [dist_eq_norm, sourceBandEndpoint_difference, norm_smul, Real.norm_eq_abs, abs_of_pos width]
  rwa [initial_distance] at bound

def flowWidthBudget (run : Data.RunIndex) (segment : Segment) (v time : ℝ) : ℝ :=
  bandWidth segment (Source.epsilon run) v * ‖basisVector 0‖ *
    Real.exp ((sourceLipschitzBound : ℝ) * time)

theorem source_basis_norm_positive : 0 < ‖basisVector 0‖ := by
  apply norm_pos_iff.mpr
  intro zero
  have atZero := congrFun zero 0
  have original : (Source.basis 0 0 : ℝ) ≠ 0 := by
    exact_mod_cast (show Source.basis 0 0 ≠ 0 from by decide +kernel)
  exact original atZero

theorem actual_flow_budget_reduction (segment : Segment) (v time : ℝ) :
    flowWidthBudget 4 segment v time = flowWidthBudget 3 segment v time -
      (Source.epsilon 3 : ℝ) * ‖basisVector 0‖ * Real.exp ((sourceLipschitzBound : ℝ) * time) ∧
    flowWidthBudget 4 segment v time < flowWidthBudget 3 segment v time := by
  have halves : (Source.epsilon 4 : ℝ) = (Source.epsilon 3 : ℝ) / 2 := by
    have original : Source.epsilon 3 = 2 * Source.epsilon 4 := by decide +kernel
    have casted : (Source.epsilon 3 : ℝ) = 2 * (Source.epsilon 4 : ℝ) := by exact_mod_cast original
    linarith
  have epsilon : (0 : ℝ) < (Source.epsilon 3 : ℝ) := by
    exact_mod_cast (show 0 < Source.epsilon 3 from by decide +kernel)
  have equality : flowWidthBudget 4 segment v time = flowWidthBudget 3 segment v time -
      (Source.epsilon 3 : ℝ) * ‖basisVector 0‖ * Real.exp ((sourceLipschitzBound : ℝ) * time) := by
    unfold flowWidthBudget
    rw [halves, bandWidth_refinement]
    ring
  refine ⟨equality, ?_⟩
  rw [equality]
  exact sub_lt_self _ (mul_pos (mul_pos epsilon source_basis_norm_positive) (Real.exp_pos _))

def bandFlowClosure : Prop :=
  type_of% generatedBandFlow_starts ∧ type_of% generatedBandFlow_evolves ∧
  type_of% generatedBandFlow_restart ∧ type_of% sourceBandFlow_noncollapse ∧
  type_of% sourceBandFlow_width_bound ∧ type_of% actual_flow_budget_reduction

theorem sourceGeneratedActualBandFlow : bandFlowClosure :=
  ⟨generatedBandFlow_starts, generatedBandFlow_evolves, generatedBandFlow_restart,
    sourceBandFlow_noncollapse, sourceBandFlow_width_bound, actual_flow_budget_reduction⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousBandFlow
