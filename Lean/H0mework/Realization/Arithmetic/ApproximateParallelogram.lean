import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.GroupTheory.Descent
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import H0mework.Realization.Arithmetic.CofinalQuadratic

/-!
# Approximate-parallelogram cofinal quadratic producer

This T1 kernel compiles a finite real evaluation satisfying one uniform
approximate parallelogram law into the cofinal doubling limit

`q(P) = lim_n h((2^n)P) / 4^n`.

The output is an actual `QuadraticMap ℤ V ℝ`; its exact parallelogram law,
integer quadraticity and bilinear polarization are generated theorems.  This
file introduces no height source constructor and accepts no canonical value,
pairing, matrix, basis or regulator.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ApproximateParallelogramQuadratic

open Filter
open CofinalQuadraticEvaluation
open scoped Topology

universe u v w

variable {V : Type u} [AddCommGroup V]

noncomputable section

/-- The finite readout on the source-generated doubling stage. -/
def doublingNormalizedValue (evaluation : V → ℝ)
    (stage : Nat) (point : V) : ℝ :=
  evaluation ((2 ^ stage) • point) / (4 : ℝ) ^ stage

/-- The additive functional-equation defect whose boundedness generates the
canonical quadratic state. -/
def parallelogramDefect (evaluation : V → ℝ) (left right : V) : ℝ :=
  evaluation (left + right) + evaluation (left - right) -
    2 * (evaluation left + evaluation right)

theorem doubling_defect_le
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (stage : Nat) (point : V) :
    |evaluation ((2 ^ (stage + 1)) • point) + evaluation 0 -
      4 * evaluation ((2 ^ stage) • point)| ≤ bound := by
  have raw := approximate ((2 ^ stage) • point) ((2 ^ stage) • point)
  simp only [parallelogramDefect, sub_self, pow_succ, mul_nsmul,
    two_nsmul] at raw ⊢
  ring_nf at raw ⊢
  exact raw

theorem doublingNormalizedValue_dist_succ_le
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (stage : Nat) (point : V) :
    dist (doublingNormalizedValue evaluation stage point)
        (doublingNormalizedValue evaluation (stage + 1) point) ≤
      ((bound + |evaluation 0|) / 4) * (1 / 4 : ℝ) ^ stage := by
  have defect := doubling_defect_le evaluation bound approximate stage point
  have numerator :
      |4 * evaluation ((2 ^ stage) • point) -
          evaluation ((2 ^ (stage + 1)) • point)| ≤
        bound + |evaluation 0| := by
    calc
      |4 * evaluation ((2 ^ stage) • point) -
          evaluation ((2 ^ (stage + 1)) • point)| =
          |evaluation 0 -
            (evaluation ((2 ^ (stage + 1)) • point) + evaluation 0 -
              4 * evaluation ((2 ^ stage) • point))| := by
            congr 1
            ring
      _ ≤ |evaluation 0| +
          |evaluation ((2 ^ (stage + 1)) • point) + evaluation 0 -
            4 * evaluation ((2 ^ stage) • point)| :=
        abs_sub _ _
      _ ≤ bound + |evaluation 0| := by linarith
  calc
    dist (doublingNormalizedValue evaluation stage point)
        (doublingNormalizedValue evaluation (stage + 1) point) =
        |4 * evaluation ((2 ^ stage) • point) -
          evaluation ((2 ^ (stage + 1)) • point)| /
            (4 : ℝ) ^ (stage + 1) := by
      rw [Real.dist_eq, doublingNormalizedValue, doublingNormalizedValue]
      have inside :
          evaluation ((2 ^ stage) • point) / (4 : ℝ) ^ stage -
              evaluation ((2 ^ (stage + 1)) • point) /
                (4 : ℝ) ^ (stage + 1) =
            (4 * evaluation ((2 ^ stage) • point) -
              evaluation ((2 ^ (stage + 1)) • point)) /
                (4 : ℝ) ^ (stage + 1) := by
        rw [pow_succ]
        field_simp
        ring
      rw [inside, abs_div,
        abs_of_pos (by positivity : 0 < (4 : ℝ) ^ (stage + 1))]
    _ ≤ (bound + |evaluation 0|) / (4 : ℝ) ^ (stage + 1) := by
      exact div_le_div_of_nonneg_right numerator (by positivity)
    _ = ((bound + |evaluation 0|) / 4) * (1 / 4 : ℝ) ^ stage := by
      rw [div_pow, one_pow, pow_succ]
      field_simp

/-- The normalized doubling observations form a Cauchy sequence solely from
the bounded approximate parallelogram law. -/
theorem doublingNormalizedValue_cauchy
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    CauchySeq fun stage =>
      doublingNormalizedValue evaluation stage point :=
  cauchySeq_of_le_geometric (1 / 4)
    ((bound + |evaluation 0|) / 4) (by norm_num)
    (fun stage =>
      doublingNormalizedValue_dist_succ_le evaluation bound approximate
        stage point)

/-- The cofinal real evaluation generated by the finite source readouts. -/
noncomputable def canonicalValue
    (evaluation : V → ℝ) (point : V) : ℝ :=
  limUnder atTop fun stage =>
    doublingNormalizedValue evaluation stage point

theorem doublingNormalizedValue_tendsto
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    Tendsto
      (fun stage => doublingNormalizedValue evaluation stage point)
      atTop (𝓝 (canonicalValue evaluation point)) :=
  (doublingNormalizedValue_cauchy evaluation bound approximate point).tendsto_limUnder

/-- Nonnegativity of finite source evaluations is preserved by the generated
cofinal value. -/
theorem canonicalValue_nonneg
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (evaluation_nonneg : ∀ point, 0 ≤ evaluation point)
    (point : V) :
    0 ≤ canonicalValue evaluation point := by
  exact ge_of_tendsto'
    (doublingNormalizedValue_tendsto evaluation bound approximate point)
    (fun stage => div_nonneg (evaluation_nonneg _) (by positivity))

/-- Uniform radius between the finite seed evaluation and its generated
canonical value. -/
def approximationRadius (evaluation : V → ℝ) (bound : ℝ) : ℝ :=
  ((bound + |evaluation 0|) / 4) / (1 - (1 / 4 : ℝ))

theorem dist_evaluation_canonicalValue_le
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    dist (evaluation point) (canonicalValue evaluation point) ≤
      approximationRadius evaluation bound := by
  have estimate := dist_le_of_le_geometric_of_tendsto₀
    (r := (1 / 4 : ℝ))
    (C := (bound + |evaluation 0|) / 4)
    (f := fun stage => doublingNormalizedValue evaluation stage point)
    (by norm_num)
    (fun stage =>
      doublingNormalizedValue_dist_succ_le evaluation bound approximate
        stage point)
    (doublingNormalizedValue_tendsto evaluation bound approximate point)
  simpa only [doublingNormalizedValue, pow_zero, one_smul, div_one,
    approximationRadius] using estimate

/-- Northcott finiteness survives the root-owned cofinal normalization.  A
canonical-height sublevel lies inside one uniformly enlarged seed-height
sublevel. -/
theorem canonicalValue_northcott
    (evaluation : V → ℝ) [Northcott evaluation]
    (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound) :
    Northcott (canonicalValue evaluation) where
  finite_le := fun threshold =>
    (Northcott.finite_le
      (h := evaluation) (threshold + approximationRadius evaluation bound)
      ).subset <| by
        intro point point_mem
        change canonicalValue evaluation point ≤ threshold at point_mem
        have distance :=
          dist_evaluation_canonicalValue_le evaluation bound approximate point
        have difference_le :
            evaluation point - canonicalValue evaluation point ≤
              approximationRadius evaluation bound := by
          exact (le_abs_self _).trans <| by
            simpa [Real.dist_eq] using distance
        change evaluation point ≤
          threshold + approximationRadius evaluation bound
        linarith

/-- A uniformly bounded change of finite presentation disappears after
quadratic doubling normalization. -/
theorem doublingNormalizedValue_sub_tendsto_zero_of_boundedDifference
    (leftEvaluation rightEvaluation : V → ℝ) (differenceBound : ℝ)
    (boundedDifference : ∀ point,
      |leftEvaluation point - rightEvaluation point| ≤ differenceBound)
    (point : V) :
    Tendsto
      (fun stage =>
        doublingNormalizedValue leftEvaluation stage point -
          doublingNormalizedValue rightEvaluation stage point)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero
    (f := fun stage =>
      |doublingNormalizedValue leftEvaluation stage point -
        doublingNormalizedValue rightEvaluation stage point|)
    (g := fun stage => differenceBound / (4 : ℝ) ^ stage) ?_ ?_ ?_
  · exact fun _stage => abs_nonneg _
  · intro stage
    have normalized_sub :
        doublingNormalizedValue leftEvaluation stage point -
            doublingNormalizedValue rightEvaluation stage point =
          (leftEvaluation ((2 ^ stage) • point) -
            rightEvaluation ((2 ^ stage) • point)) / (4 : ℝ) ^ stage := by
      simp only [doublingNormalizedValue]
      ring
    rw [normalized_sub, abs_div,
      abs_of_pos (by positivity : 0 < (4 : ℝ) ^ stage)]
    exact div_le_div_of_nonneg_right
      (boundedDifference ((2 ^ stage) • point)) (by positivity)
  · exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))

/-- Canonical quadratic evaluation is independent of every bounded finite
presentation change.  In particular, a projective frame or basis change does
not require a caller-supplied independence theorem. -/
theorem canonicalValue_eq_of_boundedDifference
    (leftEvaluation rightEvaluation : V → ℝ)
    (leftBound rightBound differenceBound : ℝ)
    (leftApproximate : ∀ left right : V,
      |parallelogramDefect leftEvaluation left right| ≤ leftBound)
    (rightApproximate : ∀ left right : V,
      |parallelogramDefect rightEvaluation left right| ≤ rightBound)
    (boundedDifference : ∀ point,
      |leftEvaluation point - rightEvaluation point| ≤ differenceBound)
    (point : V) :
    canonicalValue leftEvaluation point =
      canonicalValue rightEvaluation point := by
  have differenceLimit :=
    (doublingNormalizedValue_tendsto leftEvaluation leftBound
      leftApproximate point).sub
      (doublingNormalizedValue_tendsto rightEvaluation rightBound
        rightApproximate point)
  have differenceZero :=
    doublingNormalizedValue_sub_tendsto_zero_of_boundedDifference
      leftEvaluation rightEvaluation differenceBound boundedDifference point
  exact sub_eq_zero.mp
    (tendsto_nhds_unique differenceLimit differenceZero)

theorem parallelogramDefect_add
    (leftEvaluation rightEvaluation : V → ℝ)
    (left right : V) :
    parallelogramDefect
        (fun point => leftEvaluation point + rightEvaluation point)
        left right =
      parallelogramDefect leftEvaluation left right +
        parallelogramDefect rightEvaluation left right := by
  simp only [parallelogramDefect]
  ring

/-- Every actual quadratic occurrence has zero parallelogram defect.  This is
generated by the `QuadraticMap` laws; no separate symmetry or bilinearity
premise is accepted. -/
theorem parallelogramDefect_quadraticMap
    (quadratic : QuadraticMap ℤ V ℝ) (left right : V) :
    parallelogramDefect quadratic left right = 0 := by
  rw [parallelogramDefect,
    QuadraticMap.map_add (quadratic : V → ℝ) left right,
    show left - right = left + (-right) by exact sub_eq_add_neg _ _,
    QuadraticMap.map_add (quadratic : V → ℝ) left (-right),
    quadratic.map_neg right,
    QuadraticMap.polar_neg_right]
  ring

/-- A finite presentation at uniform distance `C` from an exact quadratic
source occurrence has automatically bounded parallelogram defect.  The
constant `6 * C` is generated from the four presentation errors; callers do
not provide an approximate-parallelogram theorem. -/
theorem approximateParallelogram_of_boundedDifference_quadraticMap
    (evaluation : V → ℝ) (quadratic : QuadraticMap ℤ V ℝ)
    (differenceBound : ℝ)
    (boundedDifference : ∀ point,
      |evaluation point - quadratic point| ≤ differenceBound)
    (left right : V) :
    |parallelogramDefect evaluation left right| ≤ 6 * differenceBound := by
  let error : V → ℝ := fun point => evaluation point - quadratic point
  have defect_eq :
      parallelogramDefect evaluation left right =
        parallelogramDefect quadratic left right +
          parallelogramDefect error left right := by
    simp only [parallelogramDefect, error]
    ring
  rw [defect_eq, parallelogramDefect_quadraticMap, zero_add]
  have add_error_bound :
      |error (left + right) + error (left - right)| ≤
        |error (left + right)| + |error (left - right)| :=
    abs_add_le _ _
  have doubled_error_bound :
      |2 * (error left + error right)| ≤
        2 * (|error left| + |error right|) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _)
      (by norm_num : (0 : ℝ) ≤ 2)
  have defect_triangle :
      |parallelogramDefect error left right| ≤
        (|error (left + right)| + |error (left - right)|) +
          2 * (|error left| + |error right|) := by
    calc
      |parallelogramDefect error left right| =
          |(error (left + right) + error (left - right)) -
            2 * (error left + error right)| := rfl
      _ ≤ |error (left + right) + error (left - right)| +
          |2 * (error left + error right)| := abs_sub _ _
      _ ≤ (|error (left + right)| + |error (left - right)|) +
          2 * (|error left| + |error right|) :=
        add_le_add add_error_bound doubled_error_bound
  have left_add_right_bound := boundedDifference (left + right)
  have left_sub_right_bound := boundedDifference (left - right)
  have left_bound := boundedDifference left
  have right_bound := boundedDifference right
  change |error (left + right)| ≤ differenceBound at left_add_right_bound
  change |error (left - right)| ≤ differenceBound at left_sub_right_bound
  change |error left| ≤ differenceBound at left_bound
  change |error right| ≤ differenceBound at right_bound
  exact defect_triangle.trans (by linarith)

theorem parallelogramDefect_sub_const
    (evaluation : V → ℝ) (constant : ℝ) (left right : V) :
    parallelogramDefect (fun point => evaluation point - constant) left right =
      parallelogramDefect evaluation left right + 2 * constant := by
  simp only [parallelogramDefect]
  ring

theorem approximateParallelogram_sub_const
    (evaluation : V → ℝ) (bound constant : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (left right : V) :
    |parallelogramDefect (fun point => evaluation point - constant)
      left right| ≤ bound + 2 * |constant| := by
  rw [parallelogramDefect_sub_const]
  calc
    |parallelogramDefect evaluation left right + 2 * constant| ≤
        |parallelogramDefect evaluation left right| + |2 * constant| :=
      abs_add_le _ _
    _ ≤ bound + 2 * |constant| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact add_le_add (approximate left right) le_rfl

/-- Northcott finiteness generates a global minimum. After shifting by that
minimum, the descent height is nonnegative and its approximate-parallelogram
bound is generated algebraically. Thus finite weak Mordell--Weil index
produces finite generation without a caller-owned nonnegativity theorem or
chosen basis. -/
theorem fg_of_northcott_approximateParallelogram
    (evaluation : V → ℝ) [Northcott evaluation]
    (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (doublingFiniteIndex :
      (nsmulAddMonoidHom 2 : V →+ V).range.FiniteIndex) :
    AddGroup.FG V := by
  obtain ⟨minimumPoint, _minimumPoint_mem, minimum⟩ :=
    Northcott.exists_min_image evaluation Set.univ Set.univ_nonempty
  let shifted : V → ℝ := fun point => evaluation point - evaluation minimumPoint
  let shiftedNorthcott : Northcott shifted :=
    { finite_le := fun threshold =>
      (Northcott.finite_le
        (h := evaluation) (threshold + evaluation minimumPoint)).subset (by
          intro point point_mem
          change evaluation point - evaluation minimumPoint ≤ threshold at point_mem
          change evaluation point ≤ threshold + evaluation minimumPoint
          linarith) }
  let _ : Northcott shifted := shiftedNorthcott
  have shifted_nonneg : ∀ point, 0 ≤ shifted point := by
    intro point
    dsimp only [shifted]
    have minimum_le := minimum point (Set.mem_univ point)
    linarith
  have shifted_approximate : ∀ left right : V,
      |parallelogramDefect shifted left right| ≤
        bound + 2 * |evaluation minimumPoint| := by
    exact approximateParallelogram_sub_const evaluation bound
      (evaluation minimumPoint) approximate
  exact AddCommGroup.fg_of_descent' doublingFiniteIndex shifted_nonneg
    shifted_approximate

/-! ## Compact cubical defect occurrences -/

/-- A source-native cubical metric presents every functional-equation defect
as the readout of one actual point in a compact parameter occurrence.  The
compact occurrence, rather than a caller-provided numerical bound, owns the
boundedness responsibility. -/
structure CompactCubicalDefectFace
    (evaluation : V → ℝ) where
  parameterSpace : CompHaus.{w}
  defectReadout : ContinuousMap parameterSpace ℝ
  parameterExposure : V → V → RootedAccountedUnfolding parameterSpace
  defect_eq : ∀ left right,
    parallelogramDefect evaluation left right =
      defectReadout (parameterExposure left right).root

namespace CompactCubicalDefectFace

variable {evaluation : V → ℝ}

/-- Compactness generates a uniform defect bound; the source does not choose
or certify a bound. -/
theorem exists_defectBound
    (face : CompactCubicalDefectFace evaluation) :
    ∃ bound : ℝ, ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound := by
  have compactRange :
      IsCompact (Set.range fun parameter : face.parameterSpace =>
        |face.defectReadout parameter|) :=
    isCompact_range face.defectReadout.continuous.abs
  rcases compactRange.bddAbove with ⟨bound, bound_spec⟩
  refine ⟨bound, fun left right => ?_⟩
  rw [face.defect_eq]
  exact bound_spec
    (Set.mem_range_self (face.parameterExposure left right).root)

/-- Canonical noncomputable bound selected from the compact source
occurrence. -/
noncomputable def defectBound
    (face : CompactCubicalDefectFace evaluation) : ℝ :=
  face.exists_defectBound.choose

theorem approximate
    (face : CompactCubicalDefectFace evaluation)
    (left right : V) :
    |parallelogramDefect evaluation left right| ≤ face.defectBound :=
  face.exists_defectBound.choose_spec left right

end CompactCubicalDefectFace

/-- Parallel finite evaluations carry the sum of their local defect bounds. -/
theorem approximateParallelogram_add
    (leftEvaluation rightEvaluation : V → ℝ)
    (leftBound rightBound : ℝ)
    (leftApproximate : ∀ left right : V,
      |parallelogramDefect leftEvaluation left right| ≤ leftBound)
    (rightApproximate : ∀ left right : V,
      |parallelogramDefect rightEvaluation left right| ≤ rightBound)
    (left right : V) :
    |parallelogramDefect
      (fun point => leftEvaluation point + rightEvaluation point)
      left right| ≤ leftBound + rightBound := by
  rw [parallelogramDefect_add]
  exact (abs_add_le _ _).trans
    (add_le_add (leftApproximate left right)
      (rightApproximate left right))

/-- Cofinal quadratic evaluation respects source-parallel addition. -/
theorem canonicalValue_add
    (leftEvaluation rightEvaluation : V → ℝ)
    (leftBound rightBound : ℝ)
    (leftApproximate : ∀ left right : V,
      |parallelogramDefect leftEvaluation left right| ≤ leftBound)
    (rightApproximate : ∀ left right : V,
      |parallelogramDefect rightEvaluation left right| ≤ rightBound)
    (point : V) :
    canonicalValue
        (fun value => leftEvaluation value + rightEvaluation value) point =
      canonicalValue leftEvaluation point +
        canonicalValue rightEvaluation point := by
  apply tendsto_nhds_unique
    (doublingNormalizedValue_tendsto
      (fun value => leftEvaluation value + rightEvaluation value)
      (leftBound + rightBound)
      (approximateParallelogram_add leftEvaluation rightEvaluation
        leftBound rightBound leftApproximate rightApproximate) point)
  have separate :=
    (doublingNormalizedValue_tendsto leftEvaluation leftBound
      leftApproximate point).add
      (doublingNormalizedValue_tendsto rightEvaluation rightBound
        rightApproximate point)
  exact separate.congr'
    (Filter.Eventually.of_forall fun stage => by
      simp only [doublingNormalizedValue]
      ring)

theorem parallelogramDefect_const_mul
    (scalar : ℝ) (evaluation : V → ℝ)
    (left right : V) :
    parallelogramDefect (fun point => scalar * evaluation point) left right =
      scalar * parallelogramDefect evaluation left right := by
  simp only [parallelogramDefect]
  ring

theorem approximateParallelogram_const_mul
    (scalar : ℝ) (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (left right : V) :
    |parallelogramDefect (fun point => scalar * evaluation point)
      left right| ≤ |scalar| * bound := by
  rw [parallelogramDefect_const_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (approximate left right) (abs_nonneg scalar)

/-- Cofinal quadratic evaluation respects scalar installation on finite
readouts. -/
theorem canonicalValue_const_mul
    (scalar : ℝ) (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    canonicalValue (fun value => scalar * evaluation value) point =
      scalar * canonicalValue evaluation point := by
  apply tendsto_nhds_unique
    (doublingNormalizedValue_tendsto
      (fun value => scalar * evaluation value) (|scalar| * bound)
      (approximateParallelogram_const_mul scalar evaluation bound approximate)
      point)
  have scaled :=
    (doublingNormalizedValue_tendsto evaluation bound approximate point).const_mul
      scalar
  exact scaled.congr'
    (Filter.Eventually.of_forall fun stage => by
      simp only [doublingNormalizedValue]
      ring)

def finiteSumEvaluation
    {ι : Type*} (indices : Finset ι)
    (evaluation : ι → V → ℝ) (point : V) : ℝ :=
  ∑ index ∈ indices, evaluation index point

theorem parallelogramDefect_finiteSum
    {ι : Type*} (indices : Finset ι)
    (evaluation : ι → V → ℝ) (left right : V) :
    parallelogramDefect (finiteSumEvaluation indices evaluation) left right =
      ∑ index ∈ indices,
        parallelogramDefect (evaluation index) left right := by
  classical
  simp only [parallelogramDefect, finiteSumEvaluation,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]

/-- A finite family of local evaluations generates the sum of its local
defect bounds. -/
theorem approximateParallelogram_finiteSum
    {ι : Type*} (indices : Finset ι)
    (evaluation : ι → V → ℝ) (bound : ι → ℝ)
    (approximate : ∀ index ∈ indices, ∀ left right : V,
      |parallelogramDefect (evaluation index) left right| ≤ bound index)
    (left right : V) :
    |parallelogramDefect (finiteSumEvaluation indices evaluation) left right| ≤
      ∑ index ∈ indices, bound index := by
  rw [parallelogramDefect_finiteSum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun index index_mem =>
      approximate index index_mem left right)

/-- Cofinal evaluation of a finite local-place family is the sum of the
canonical local evaluations. -/
theorem canonicalValue_finiteSum
    {ι : Type*} (indices : Finset ι)
    (evaluation : ι → V → ℝ) (bound : ι → ℝ)
    (approximate : ∀ index ∈ indices, ∀ left right : V,
      |parallelogramDefect (evaluation index) left right| ≤ bound index)
    (point : V) :
    canonicalValue (finiteSumEvaluation indices evaluation) point =
      ∑ index ∈ indices, canonicalValue (evaluation index) point := by
  classical
  apply tendsto_nhds_unique
    (doublingNormalizedValue_tendsto
      (finiteSumEvaluation indices evaluation)
      (∑ index ∈ indices, bound index)
      (approximateParallelogram_finiteSum indices evaluation bound approximate)
      point)
  have separate :
      Tendsto
        (fun stage => ∑ index ∈ indices,
          doublingNormalizedValue (evaluation index) stage point)
        atTop
        (𝓝 (∑ index ∈ indices, canonicalValue (evaluation index) point)) := by
    apply tendsto_finsetSum indices
    intro index index_mem
    exact doublingNormalizedValue_tendsto (evaluation index) (bound index)
      (approximate index index_mem) point
  exact separate.congr'
    (Filter.Eventually.of_forall fun stage => by
      simp only [doublingNormalizedValue, finiteSumEvaluation]
      exact (Finset.sum_div indices
        (fun index => evaluation index ((2 ^ stage) • point))
        ((4 : ℝ) ^ stage)).symm)

/-! ## Point-dependent finite local support -/

/-- Additive total of a finitely supported local family. -/
def finsuppTotal {ι : Type*} : (ι →₀ ℝ) →+ ℝ :=
  Finsupp.liftAddHom (fun _index => AddMonoidHom.id ℝ)

@[simp] theorem finsuppTotal_apply
    {ι : Type*} (value : ι →₀ ℝ) :
    finsuppTotal value = value.sum (fun _index localValue => localValue) :=
  rfl

/-- Global finite evaluation generated by the actual support carried by each
point's local family. -/
def finitelySupportedEvaluation
    {ι : Type*} (localEvaluation : V → ι →₀ ℝ) : V → ℝ :=
  fun point => finsuppTotal (localEvaluation point)

/-- Placewise functional-equation defect, still finitely supported because
it is generated by finite algebra on four actual local families. -/
def finitelySupportedParallelogramDefect
    {ι : Type*} (localEvaluation : V → ι →₀ ℝ)
    (left right : V) : ι →₀ ℝ :=
  localEvaluation (left + right) + localEvaluation (left - right) -
    2 • (localEvaluation left + localEvaluation right)

@[simp] theorem finitelySupportedParallelogramDefect_apply
    {ι : Type*} (localEvaluation : V → ι →₀ ℝ)
    (left right : V) (index : ι) :
    finitelySupportedParallelogramDefect localEvaluation left right index =
      parallelogramDefect (fun point => localEvaluation point index)
        left right := by
  simp only [finitelySupportedParallelogramDefect, parallelogramDefect,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply]
  ring

theorem parallelogramDefect_finitelySupportedEvaluation
    {ι : Type*} (localEvaluation : V → ι →₀ ℝ)
    (left right : V) :
    parallelogramDefect (finitelySupportedEvaluation localEvaluation)
        left right =
      finsuppTotal
        (finitelySupportedParallelogramDefect localEvaluation left right) := by
  simp only [parallelogramDefect, finitelySupportedEvaluation,
    finitelySupportedParallelogramDefect, map_sub, map_add, map_nsmul,
    nsmul_eq_mul]
  ring

/-- Pointwise domination of a finitely supported local family generates the
global absolute-value bound. -/
theorem abs_finsuppTotal_le_finsuppTotal
    {ι : Type*} (value bound : ι →₀ ℝ)
    (dominated : ∀ index, |value index| ≤ bound index) :
    |finsuppTotal value| ≤ finsuppTotal bound := by
  classical
  let indices := value.support ∪ bound.support
  have value_eq :
      finsuppTotal value = ∑ index ∈ indices, value index := by
    exact Finsupp.sum_of_support_subset value Finset.subset_union_left
      (fun _index localValue => localValue) (by simp)
  have bound_eq :
      finsuppTotal bound = ∑ index ∈ indices, bound index := by
    exact Finsupp.sum_of_support_subset bound Finset.subset_union_right
      (fun _index localValue => localValue) (by simp)
  rw [value_eq, bound_eq]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun index _index_mem => dominated index)

/-- Per-place bounded defects generate one global bounded defect even when
the finite nonzero place support depends on the point.  No global height or
global approximate-parallelogram law is supplied. -/
theorem approximateParallelogram_finitelySupported
    {ι : Type*} (localEvaluation : V → ι →₀ ℝ)
    (defectBound : ι →₀ ℝ)
    (localApproximate : ∀ index left right,
      |parallelogramDefect (fun point => localEvaluation point index)
        left right| ≤ defectBound index)
    (left right : V) :
    |parallelogramDefect
      (finitelySupportedEvaluation localEvaluation) left right| ≤
        finsuppTotal defectBound := by
  rw [parallelogramDefect_finitelySupportedEvaluation]
  apply abs_finsuppTotal_le_finsuppTotal
  intro index
  rw [finitelySupportedParallelogramDefect_apply]
  exact localApproximate index left right

theorem doublingNormalizedValue_parallelogramDefect
    (evaluation : V → ℝ) (stage : Nat) (left right : V) :
    parallelogramDefect (doublingNormalizedValue evaluation stage)
        left right =
      parallelogramDefect evaluation ((2 ^ stage) • left)
          ((2 ^ stage) • right) / (4 : ℝ) ^ stage := by
  simp only [parallelogramDefect, doublingNormalizedValue,
    nsmul_add, nsmul_sub]
  field_simp

theorem doublingNormalizedValue_parallelogramDefect_tendsto_zero
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (left right : V) :
    Tendsto
      (fun stage => parallelogramDefect
        (doublingNormalizedValue evaluation stage) left right)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero
    (f := fun stage =>
      |parallelogramDefect
        (doublingNormalizedValue evaluation stage) left right|)
    (g := fun stage => bound / (4 : ℝ) ^ stage) ?_ ?_ ?_
  · exact fun _stage => abs_nonneg _
  · intro stage
    rw [doublingNormalizedValue_parallelogramDefect, abs_div,
      abs_of_pos (by positivity : 0 < (4 : ℝ) ^ stage)]
    exact div_le_div_of_nonneg_right
      (approximate ((2 ^ stage) • left) ((2 ^ stage) • right))
      (by positivity)
  · exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))

/-- The bounded finite defect vanishes at the cofinal value. -/
theorem canonicalValue_parallelogram
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (left right : V) :
    canonicalValue evaluation (left + right) +
        canonicalValue evaluation (left - right) =
      2 * (canonicalValue evaluation left +
        canonicalValue evaluation right) := by
  have limit :
      Tendsto
        (fun stage => parallelogramDefect
          (doublingNormalizedValue evaluation stage) left right)
        atTop
        (𝓝 (parallelogramDefect (canonicalValue evaluation) left right)) := by
    simpa only [parallelogramDefect] using
      (((doublingNormalizedValue_tendsto evaluation bound approximate
          (left + right)).add
        (doublingNormalizedValue_tendsto evaluation bound approximate
          (left - right))).sub
        ((doublingNormalizedValue_tendsto evaluation bound approximate left).add
          (doublingNormalizedValue_tendsto evaluation bound approximate right)
            |>.const_mul 2))
  have zero :=
    doublingNormalizedValue_parallelogramDefect_tendsto_zero
      evaluation bound approximate left right
  have defect_zero :
      parallelogramDefect (canonicalValue evaluation) left right = 0 :=
    tendsto_nhds_unique limit zero
  exact sub_eq_zero.mp defect_zero

theorem canonicalValue_zero
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound) :
    canonicalValue evaluation 0 = 0 := by
  have identity :=
    canonicalValue_parallelogram evaluation bound approximate (0 : V) 0
  simp only [zero_add, zero_sub, neg_zero] at identity
  linarith

theorem canonicalValue_neg
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    canonicalValue evaluation (-point) = canonicalValue evaluation point := by
  have identity :=
    canonicalValue_parallelogram evaluation bound approximate (0 : V) point
  rw [zero_add, zero_sub,
    canonicalValue_zero evaluation bound approximate] at identity
  linarith

theorem canonicalValue_nsmul
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (natural : Nat) (point : V) :
    canonicalValue evaluation (natural • point) =
      (natural : ℝ) ^ 2 * canonicalValue evaluation point := by
  induction natural using Nat.twoStepInduction with
  | zero => simp [canonicalValue_zero evaluation bound approximate]
  | one => simp
  | more natural previous successor =>
      have identity := canonicalValue_parallelogram evaluation bound approximate
        ((natural + 1) • point) point
      have add_point :
          ((natural + 1) • point) + point = (natural + 2) • point := by
        simp only [add_nsmul, one_nsmul]
        abel
      have sub_point :
          ((natural + 1) • point) - point = natural • point := by
        simp only [add_nsmul, one_nsmul]
        abel
      rw [add_point, sub_point, previous, successor] at identity
      push_cast at identity ⊢
      nlinarith

theorem canonicalValue_zsmul
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (integer : ℤ) (point : V) :
    canonicalValue evaluation (integer • point) =
      (integer : ℝ) ^ 2 * canonicalValue evaluation point := by
  cases integer with
  | ofNat natural =>
      simpa using
        canonicalValue_nsmul evaluation bound approximate natural point
  | negSucc natural =>
      rw [Int.negSucc_eq, neg_smul,
        canonicalValue_neg evaluation bound approximate]
      have smul_eq :
          ((natural : ℤ) + 1) • point = (natural + 1 : Nat) • point := by
        simp [add_zsmul, add_nsmul]
      rw [smul_eq, canonicalValue_nsmul evaluation bound approximate]
      push_cast
      ring

/-- Northcott finiteness of the finite seed forces every zero of the generated
canonical quadratic value to be torsion.  The proof uses the bounded distance
from the seed to the canonical value and the actual integral-multiple orbit;
no positivity or nondegeneracy premise is supplied. -/
theorem canonicalValue_zero_mem_torsion_of_northcott
    (evaluation : V → ℝ) [Northcott evaluation]
    (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V)
    (value_zero : canonicalValue evaluation point = 0) :
    point ∈ Submodule.torsion ℤ V := by
  let radius := approximationRadius evaluation bound
  have orbit_small : ∀ natural : Nat,
      evaluation (natural • point) ≤ radius := by
    intro natural
    have distance := dist_evaluation_canonicalValue_le evaluation bound
      approximate (natural • point)
    have canonical_zero :
        canonicalValue evaluation (natural • point) = 0 := by
      rw [show natural • point = (natural : ℤ) • point by simp]
      rw [canonicalValue_zsmul evaluation bound approximate, value_zero]
      simp
    rw [canonical_zero] at distance
    exact (le_abs_self _).trans (by simpa [Real.dist_eq] using distance)
  let small : Set V := {candidate | evaluation candidate ≤ radius}
  have small_finite : small.Finite := Northcott.finite_le radius
  let orbit : Nat → small := fun natural =>
    ⟨natural • point, orbit_small natural⟩
  let _ : Finite small := small_finite
  have orbit_not_injective : ¬ Function.Injective orbit :=
    not_injective_infinite_finite orbit
  obtain ⟨left, right, same, distinct⟩ :=
    Function.not_injective_iff.mp orbit_not_injective
  have same_point : left • point = right • point :=
    congrArg Subtype.val same
  rw [Submodule.mem_torsion_iff]
  let annihilator : ℤ := (left : ℤ) - (right : ℤ)
  have annihilator_ne : annihilator ≠ 0 := by
    intro zero
    apply distinct
    exact_mod_cast sub_eq_zero.mp zero
  refine ⟨⟨annihilator,
    mem_nonZeroDivisors_of_ne_zero annihilator_ne⟩, ?_⟩
  change ((left : ℤ) - (right : ℤ)) • point = 0
  rw [sub_smul]
  simpa using sub_eq_zero.mpr same_point

/-- Conversely, integral torsion is annihilated by the generated canonical
quadratic value. -/
theorem canonicalValue_mem_torsion_zero
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V)
    (torsion : point ∈ Submodule.torsion ℤ V) :
    canonicalValue evaluation point = 0 := by
  rw [Submodule.mem_torsion_iff] at torsion
  obtain ⟨annihilator, annihilates⟩ := torsion
  have annihilates' : (annihilator : ℤ) • point = 0 := annihilates
  have scaled := canonicalValue_zsmul evaluation bound approximate
    (annihilator : ℤ) point
  rw [annihilates', canonicalValue_zero evaluation bound approximate] at scaled
  have coefficient_ne : ((annihilator : ℤ) : ℝ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 <| by
      exact_mod_cast nonZeroDivisors.coe_ne_zero annihilator
  exact (mul_eq_zero.mp scaled.symm).resolve_left coefficient_ne

theorem canonicalValue_eq_zero_iff_mem_torsion_of_northcott
    (evaluation : V → ℝ) [Northcott evaluation]
    (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    canonicalValue evaluation point = 0 ↔
      point ∈ Submodule.torsion ℤ V :=
  ⟨canonicalValue_zero_mem_torsion_of_northcott evaluation bound approximate
      point,
    canonicalValue_mem_torsion_zero evaluation bound approximate point⟩

def differencePolar (quadratic : V → ℝ) (left right : V) : ℝ :=
  (quadratic (left + right) - quadratic (left - right)) / 2

theorem differencePolar_add_left
    (quadratic : V → ℝ)
    (parallelogram : ∀ left right : V,
      quadratic (left + right) + quadratic (left - right) =
        2 * (quadratic left + quadratic right))
    (left right point : V) :
    differencePolar quadratic (left + right) point =
      differencePolar quadratic left point +
        differencePolar quadratic right point := by
  have first := parallelogram (left + right + point) (left - point)
  have second := parallelogram (left + right - point) (left + point)
  have third := parallelogram (right + point) point
  have fourth := parallelogram (right - point) point
  unfold differencePolar
  abel_nf at first second third fourth ⊢
  linear_combination (-first + second + third - fourth) / 4

theorem canonicalValue_polar_eq_differencePolar
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (left right : V) :
    QuadraticMap.polar (canonicalValue evaluation) left right =
      differencePolar (canonicalValue evaluation) left right := by
  have identity :=
    canonicalValue_parallelogram evaluation bound approximate left right
  unfold QuadraticMap.polar differencePolar
  linarith

theorem canonicalValue_polar_add_left
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (left right point : V) :
    QuadraticMap.polar (canonicalValue evaluation) (left + right) point =
      QuadraticMap.polar (canonicalValue evaluation) left point +
        QuadraticMap.polar (canonicalValue evaluation) right point := by
  rw [canonicalValue_polar_eq_differencePolar evaluation bound approximate,
    canonicalValue_polar_eq_differencePolar evaluation bound approximate,
    canonicalValue_polar_eq_differencePolar evaluation bound approximate]
  exact differencePolar_add_left (canonicalValue evaluation)
    (canonicalValue_parallelogram evaluation bound approximate)
    left right point

theorem canonicalValue_polar_zero_left
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (right : V) :
    QuadraticMap.polar (canonicalValue evaluation) 0 right = 0 := by
  rw [canonicalValue_polar_eq_differencePolar evaluation bound approximate]
  unfold differencePolar
  rw [zero_add, zero_sub,
    canonicalValue_neg evaluation bound approximate]
  ring

def canonicalPolarAddHom
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (right : V) : V →+ ℝ where
  toFun := fun left =>
    QuadraticMap.polar (canonicalValue evaluation) left right
  map_zero' :=
    canonicalValue_polar_zero_left evaluation bound approximate right
  map_add' := fun left left' =>
    canonicalValue_polar_add_left evaluation bound approximate
      left left' right

theorem canonicalValue_polar_zsmul_left
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (integer : ℤ) (left right : V) :
    QuadraticMap.polar (canonicalValue evaluation) (integer • left) right =
      integer • QuadraticMap.polar (canonicalValue evaluation) left right := by
  exact map_zsmul
    (canonicalPolarAddHom evaluation bound approximate right) integer left

theorem canonicalValue_zsmul_quadratic
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (integer : ℤ) (point : V) :
    canonicalValue evaluation (integer • point) =
      (integer * integer) • canonicalValue evaluation point := by
  rw [canonicalValue_zsmul evaluation bound approximate]
  simp only [zsmul_eq_mul, Int.cast_mul]
  ring

/-- The root-generated quadratic state.  Quadraticity and bilinear
polarization are conclusions of the cofinal calculation, not premises. -/
noncomputable def quadraticState
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound) :
    QuadraticMap ℤ V ℝ :=
  QuadraticMap.ofPolar (canonicalValue evaluation)
    (canonicalValue_zsmul_quadratic evaluation bound approximate)
    (canonicalValue_polar_add_left evaluation bound approximate)
    (canonicalValue_polar_zsmul_left evaluation bound approximate)

/-- The generated quadratic map is independent of every uniformly bounded
finite presentation change. -/
theorem quadraticState_eq_of_boundedDifference
    (leftEvaluation rightEvaluation : V → ℝ)
    (leftBound rightBound differenceBound : ℝ)
    (leftApproximate : ∀ left right : V,
      |parallelogramDefect leftEvaluation left right| ≤ leftBound)
    (rightApproximate : ∀ left right : V,
      |parallelogramDefect rightEvaluation left right| ≤ rightBound)
    (boundedDifference : ∀ point,
      |leftEvaluation point - rightEvaluation point| ≤ differenceBound) :
    quadraticState leftEvaluation leftBound leftApproximate =
      quadraticState rightEvaluation rightBound rightApproximate := by
  apply QuadraticMap.ext
  intro point
  exact canonicalValue_eq_of_boundedDifference
    leftEvaluation rightEvaluation leftBound rightBound differenceBound
    leftApproximate rightApproximate boundedDifference point

theorem quadraticState_add
    (leftEvaluation rightEvaluation : V → ℝ)
    (leftBound rightBound : ℝ)
    (leftApproximate : ∀ left right : V,
      |parallelogramDefect leftEvaluation left right| ≤ leftBound)
    (rightApproximate : ∀ left right : V,
      |parallelogramDefect rightEvaluation left right| ≤ rightBound) :
    quadraticState
        (fun point => leftEvaluation point + rightEvaluation point)
        (leftBound + rightBound)
        (approximateParallelogram_add leftEvaluation rightEvaluation
          leftBound rightBound leftApproximate rightApproximate) =
      quadraticState leftEvaluation leftBound leftApproximate +
        quadraticState rightEvaluation rightBound rightApproximate := by
  apply QuadraticMap.ext
  intro point
  exact canonicalValue_add leftEvaluation rightEvaluation
    leftBound rightBound leftApproximate rightApproximate point

theorem quadraticState_const_mul
    (scalar : ℝ) (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound) :
    quadraticState (fun point => scalar * evaluation point)
        (|scalar| * bound)
        (approximateParallelogram_const_mul scalar evaluation bound approximate) =
      scalar • quadraticState evaluation bound approximate := by
  apply QuadraticMap.ext
  intro point
  exact canonicalValue_const_mul scalar evaluation bound approximate point

/-- An actual incidence fold converges to the same generated canonical value
when every finite stage is identified with the normalized doubling readout.
The identification is about finite source data; it does not supply a limit or
quadratic law. -/
theorem accountedStageValue_tendsto
    {State : Type v} {Incidence : Type w}
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (seed : State) (advance : State → State)
    (incidenceExposure : State → V → RootedAccountedUnfolding Incidence)
    (localEvaluation : Incidence → V → ℝ)
    (stageFold_eq : ∀ stage point,
      accountedIncidenceEvaluation localEvaluation
          (incidenceExposure ((advance^[stage]) seed) point) point =
        doublingNormalizedValue evaluation stage point)
    (point : V) :
    Tendsto
      (fun stage => accountedIncidenceEvaluation localEvaluation
        (incidenceExposure ((advance^[stage]) seed) point) point)
      atTop (𝓝 (canonicalValue evaluation point)) := by
  exact
    (doublingNormalizedValue_tendsto evaluation bound approximate point).congr'
      (Filter.Eventually.of_forall fun stage =>
        (stageFold_eq stage point).symm)

/-- Compiler from finite source incidences plus the already proved bounded
approximate parallelogram law to the existing root-owned cofinal recurrence.
All three asymptotic quadratic/polar defects are discharged here; callers do
not provide them. -/
noncomputable def cofinalRecurrence
    {State : Type v} {Incidence : Type w}
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (seed : State) (advance : State → State)
    (incidenceExposure : State → V → RootedAccountedUnfolding Incidence)
    (localEvaluation : Incidence → V → ℝ)
    (stageFold_eq : ∀ stage point,
      accountedIncidenceEvaluation localEvaluation
          (incidenceExposure ((advance^[stage]) seed) point) point =
        doublingNormalizedValue evaluation stage point) :
    CofinalQuadraticRecurrence ℝ State V Incidence where
  seed := seed
  advance := advance
  incidenceExposure := incidenceExposure
  localEvaluation := localEvaluation
  pointwiseCauchy := fun point =>
    (accountedStageValue_tendsto evaluation bound approximate seed advance
      incidenceExposure localEvaluation stageFold_eq point).cauchySeq
  smulDefect_tendsto_zero := fun integer point => by
    have left := accountedStageValue_tendsto evaluation bound approximate
      seed advance incidenceExposure localEvaluation stageFold_eq
      (integer • point)
    have right :=
      (accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq point).const_mul
          (algebraMap ℤ ℝ (integer * integer))
    have difference := left.sub right
    convert difference using 1
    congr 1
    rw [canonicalValue_zsmul evaluation bound approximate]
    norm_num
    ring
  polarAddDefect_tendsto_zero := fun left right point => by
    have leftRightPoint :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq
        ((left + right) + point)
    have leftRight :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq (left + right)
    have pointLimit :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq point
    have leftPoint :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq (left + point)
    have leftLimit :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq left
    have rightPoint :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq (right + point)
    have rightLimit :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq right
    have difference :=
      ((leftRightPoint.sub leftRight).sub pointLimit).sub
        (((leftPoint.sub leftLimit).sub pointLimit).add
          ((rightPoint.sub rightLimit).sub pointLimit))
    convert difference using 1
    congr 1
    change 0 =
      QuadraticMap.polar (canonicalValue evaluation) (left + right) point -
        (QuadraticMap.polar (canonicalValue evaluation) left point +
          QuadraticMap.polar (canonicalValue evaluation) right point)
    rw [canonicalValue_polar_add_left evaluation bound approximate]
    simp
  polarSmulDefect_tendsto_zero := fun integer left right => by
    have integerLeftRight :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq
        (integer • left + right)
    have integerLeft :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq (integer • left)
    have rightLimit :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq right
    have leftRight :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq (left + right)
    have leftLimit :=
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq left
    have scalar :=
      ((leftRight.sub leftLimit).sub rightLimit).const_mul
        (algebraMap ℤ ℝ integer)
    have difference :=
      ((integerLeftRight.sub integerLeft).sub rightLimit).sub scalar
    convert difference using 1
    congr 1
    change 0 =
      QuadraticMap.polar (canonicalValue evaluation) (integer • left) right -
        algebraMap ℤ ℝ integer *
          QuadraticMap.polar (canonicalValue evaluation) left right
    rw [canonicalValue_polar_zsmul_left evaluation bound approximate]
    simp [zsmul_eq_mul]

/-- The compiled incidence recurrence has exactly the canonical value of the
finite seed.  This identifies the root-owned fold with the analytic
normalization without adding a second value field to either interface. -/
theorem cofinalRecurrence_cofinalValue_eq
    {State : Type v} {Incidence : Type w}
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (seed : State) (advance : State → State)
    (incidenceExposure : State → V → RootedAccountedUnfolding Incidence)
    (localEvaluation : Incidence → V → ℝ)
    (stageFold_eq : ∀ stage point,
      accountedIncidenceEvaluation localEvaluation
          (incidenceExposure ((advance^[stage]) seed) point) point =
        doublingNormalizedValue evaluation stage point)
    (point : V) :
    (cofinalRecurrence evaluation bound approximate seed advance
      incidenceExposure localEvaluation stageFold_eq).cofinalValue point =
        canonicalValue evaluation point := by
  have recurrenceLimit :=
    (cofinalRecurrence evaluation bound approximate seed advance
      incidenceExposure localEvaluation stageFold_eq).stageValue_tendsto point
  have canonicalLimit :
      Tendsto
        (fun stage =>
          (cofinalRecurrence evaluation bound approximate seed advance
            incidenceExposure localEvaluation stageFold_eq).stageValue stage point)
        atTop (𝓝 (canonicalValue evaluation point)) := by
    simpa only [CofinalQuadraticRecurrence.stageValue,
      CofinalQuadraticRecurrence.stateAt, cofinalRecurrence] using
      accountedStageValue_tendsto evaluation bound approximate seed advance
        incidenceExposure localEvaluation stageFold_eq point
  exact tendsto_nhds_unique recurrenceLimit canonicalLimit

@[simp] theorem quadraticState_apply
    (evaluation : V → ℝ) (bound : ℝ)
    (approximate : ∀ left right : V,
      |parallelogramDefect evaluation left right| ≤ bound)
    (point : V) :
    quadraticState evaluation bound approximate point =
      canonicalValue evaluation point :=
  rfl

end

end ApproximateParallelogramQuadratic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
