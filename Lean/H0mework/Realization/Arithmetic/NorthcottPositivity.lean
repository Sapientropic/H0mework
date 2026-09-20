import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Order.Floor
import H0mework.Realization.Arithmetic.ApproximateParallelogram

/-!
# Northcott generation of real lattice positivity

A nonnegative quadratic state on a full integral lattice cannot have a
nonzero real null direction while retaining Northcott finiteness.  Scaling a
putative null direction and rounding through the lattice's fundamental
parallelepiped would produce infinitely many lattice points in one bounded
quadratic sublevel.

The basis in this proof is an internal calculation device.  The public
conclusion is positive definiteness of the basis-free real bilinear form.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NorthcottLatticePositivity

open Filter
open scoped Topology

noncomputable section

variable {E ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι]

/-- Integral lattice point obtained by flooring the coordinates of a scaled
real point in the chosen calculation basis. -/
def scaledFloorPoint (basis : Module.Basis ι ℝ E)
    (point : E) (stage : ℕ) :
    Submodule.span ℤ (Set.range basis) :=
  ZSpan.floor basis (((stage + 1 : ℕ) : ℝ) • point)

/-- Normalized rounded lattice points converge back to the real direction.
The rounding error stays in one bounded fundamental parallelepiped. -/
theorem scaledFloorPoint_normalized_tendsto
    (basis : Module.Basis ι ℝ E) (point : E) :
    Tendsto
      (fun stage => ((stage + 1 : ℕ) : ℝ)⁻¹ •
        (scaledFloorPoint basis point stage : E))
      atTop (𝓝 point) := by
  let _ : FiniteDimensional ℝ E := basis.finiteDimensional_of_finite
  have inverse_tendsto :
      Tendsto (fun stage : ℕ => ((stage + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 0) := by
    rw [show (fun stage : ℕ => ((stage + 1 : ℕ) : ℝ)⁻¹) =
        ((fun value : ℝ => value⁻¹) ∘
          fun stage : ℕ => (stage : ℝ) + 1) by
      funext stage
      simp]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop)
  have error_tendsto :
      Tendsto
        (fun stage => ((stage + 1 : ℕ) : ℝ)⁻¹ •
          ZSpan.fract basis (((stage + 1 : ℕ) : ℝ) • point))
        atTop (𝓝 0) := by
    refine squeeze_zero_norm
      (a := fun stage => ((stage + 1 : ℕ) : ℝ)⁻¹ *
        (∑ index, ‖basis index‖)) ?_ ?_
    · intro stage
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (ZSpan.norm_fract_le basis _)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    · simpa using inverse_tendsto.mul_const (∑ index, ‖basis index‖)
  have identity : ∀ stage,
      ((stage + 1 : ℕ) : ℝ)⁻¹ •
          (scaledFloorPoint basis point stage : E) =
        point - ((stage + 1 : ℕ) : ℝ)⁻¹ •
          ZSpan.fract basis (((stage + 1 : ℕ) : ℝ) • point) := by
    intro stage
    have scale_ne : ((stage + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have floor_eq :
        (scaledFloorPoint basis point stage : E) =
          ((stage + 1 : ℕ) : ℝ) • point -
            ZSpan.fract basis (((stage + 1 : ℕ) : ℝ) • point) := by
      rw [ZSpan.fract_apply]
      simp [scaledFloorPoint]
    rw [floor_eq, smul_sub, smul_smul, inv_mul_cancel₀ scale_ne,
      one_smul]
  simpa using
    (((tendsto_const_nhds : Tendsto (fun _ : ℕ => point) atTop (𝓝 point)
        ).sub error_tendsto).congr'
      (Filter.Eventually.of_forall fun stage => (identity stage).symm))

/-- Nonnegativity on the full integer lattice extends to the whole real
space by normalized lattice approximation. -/
theorem bilinForm_diagonal_nonneg_of_zspan
    (basis : Module.Basis ι ℝ E)
    (pairing : LinearMap.BilinForm ℝ E)
    (lattice_nonneg : ∀ point : Submodule.span ℤ (Set.range basis),
      0 ≤ pairing point point)
    (point : E) :
    0 ≤ pairing point point := by
  let _ : FiniteDimensional ℝ E := basis.finiteDimensional_of_finite
  have normalized_nonneg : ∀ stage : ℕ,
      0 ≤ pairing
        (((stage + 1 : ℕ) : ℝ)⁻¹ •
          (scaledFloorPoint basis point stage : E))
        (((stage + 1 : ℕ) : ℝ)⁻¹ •
          (scaledFloorPoint basis point stage : E)) := by
    intro stage
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (lattice_nonneg (scaledFloorPoint basis point stage)))
  have diagonal_continuous :
      Continuous (fun current => pairing current current) := by
    let innerContinuous : E →ₗ[ℝ] E →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap.comp pairing
    let continuousPairing : E →L[ℝ] E →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap innerContinuous
    exact Continuous.clm_apply continuousPairing.continuous continuous_id
  have diagonal_tendsto :
      Tendsto
        (fun stage => pairing
          (((stage + 1 : ℕ) : ℝ)⁻¹ •
            (scaledFloorPoint basis point stage : E))
          (((stage + 1 : ℕ) : ℝ)⁻¹ •
            (scaledFloorPoint basis point stage : E)))
        atTop (𝓝 (pairing point point)) :=
    (diagonal_continuous.tendsto point).comp
      (scaledFloorPoint_normalized_tendsto basis point)
  exact ge_of_tendsto' diagonal_tendsto normalized_nonneg

/-- For a symmetric nonnegative bilinear form, a zero diagonal vector lies in
the radical. -/
theorem bilinForm_annihilates_of_diagonal_zero
    (pairing : LinearMap.BilinForm ℝ E)
    (symmetric : ∀ left right, pairing left right = pairing right left)
    (nonnegative : ∀ point, 0 ≤ pairing point point)
    (point : E) (diagonal_zero : pairing point point = 0)
    (other : E) :
    pairing point other = 0 := by
  by_contra pairing_ne
  let mixed := pairing point other
  let otherDiagonal := pairing other other
  let scalar := -mixed / (otherDiagonal + 1)
  have other_nonneg : 0 ≤ otherDiagonal := nonnegative other
  have denominator_pos : 0 < otherDiagonal + 1 := by linarith
  have expanded :
      pairing (point + scalar • other) (point + scalar • other) =
        2 * scalar * mixed + scalar ^ 2 * otherDiagonal := by
    simp only [map_add, LinearMap.add_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [diagonal_zero, symmetric other point]
    dsimp only [mixed, otherDiagonal]
    ring
  have formula :
      2 * scalar * mixed + scalar ^ 2 * otherDiagonal =
        -(mixed ^ 2 * (otherDiagonal + 2)) /
          (otherDiagonal + 1) ^ 2 := by
    dsimp only [scalar]
    field_simp
    ring
  have mixed_sq_pos : 0 < mixed ^ 2 := sq_pos_of_ne_zero pairing_ne
  have numerator_pos : 0 < mixed ^ 2 * (otherDiagonal + 2) :=
    mul_pos mixed_sq_pos (by linarith)
  have negative :
      pairing (point + scalar • other) (point + scalar • other) < 0 := by
    rw [expanded, formula]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos numerator_pos)
      (sq_pos_of_pos denominator_pos)
  exact (not_lt_of_ge (nonnegative (point + scalar • other))) negative

/-- Northcott finiteness converts integral nonnegativity into positive
definiteness of the whole real pairing. A nonzero real null direction would
generate infinitely many rounded lattice points in one height sublevel. -/
theorem bilinForm_posDef_of_zspan_northcott
    (basis : Module.Basis ι ℝ E)
    (pairing : LinearMap.BilinForm ℝ E)
    (symmetric : ∀ left right, pairing left right = pairing right left)
    (height : Submodule.span ℤ (Set.range basis) → ℝ)
    [Northcott height]
    (diagonal_eq_height :
      ∀ point : Submodule.span ℤ (Set.range basis),
        pairing point point = 2 * height point)
    (height_nonneg : ∀ point, 0 ≤ height point) :
    pairing.toQuadraticMap.PosDef := by
  let _ : FiniteDimensional ℝ E := basis.finiteDimensional_of_finite
  have lattice_nonneg :
      ∀ point : Submodule.span ℤ (Set.range basis),
        0 ≤ pairing point point := by
    intro point
    rw [diagonal_eq_height]
    exact mul_nonneg (by norm_num) (height_nonneg point)
  have nonnegative : ∀ point : E, 0 ≤ pairing point point :=
    bilinForm_diagonal_nonneg_of_zspan basis pairing lattice_nonneg
  intro point point_ne_zero
  change 0 < pairing point point
  apply lt_of_le_of_ne (nonnegative point)
  intro diagonal_zero_symm
  have diagonal_zero : pairing point point = 0 := diagonal_zero_symm.symm
  have diagonal_continuous :
      Continuous (fun current => pairing current current) := by
    let innerContinuous : E →ₗ[ℝ] E →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap.comp pairing
    let continuousPairing : E →L[ℝ] E →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap innerContinuous
    exact Continuous.clm_apply continuousPairing.continuous continuous_id
  have compact_diagonal : IsCompact
      ((fun current => pairing current current) '' basis.parallelepiped) :=
    basis.parallelepiped.isCompact.image diagonal_continuous
  obtain ⟨bound, bound_spec⟩ := compact_diagonal.bddAbove
  obtain ⟨coordinate, coordinate_ne_zero⟩ :
      ∃ coordinate, basis.repr point coordinate ≠ 0 := by
    by_contra all_zero
    simp only [not_exists, not_not] at all_zero
    apply point_ne_zero
    apply basis.repr.injective
    ext index
    simpa using all_zero index
  let direction : E :=
    if 0 < basis.repr point coordinate then point else -point
  have direction_coordinate_pos :
      0 < basis.repr direction coordinate := by
    dsimp only [direction]
    split_ifs with positive
    · exact positive
    · rw [map_neg, Finsupp.neg_apply]
      exact neg_pos.mpr <| lt_of_le_of_ne (le_of_not_gt positive)
        coordinate_ne_zero
  have direction_diagonal_zero : pairing direction direction = 0 := by
    dsimp only [direction]
    split_ifs
    · exact diagonal_zero
    · simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact diagonal_zero
  have direction_annihilates : ∀ other, pairing direction other = 0 :=
    bilinForm_annihilates_of_diagonal_zero pairing symmetric nonnegative
      direction direction_diagonal_zero
  let latticePoint : ℕ → Submodule.span ℤ (Set.range basis) :=
    fun stage => scaledFloorPoint basis direction stage
  have latticePoint_height_le :
      ∀ stage, height (latticePoint stage) ≤ bound / 2 := by
    intro stage
    let scale : ℝ := ((stage + 1 : ℕ) : ℝ)
    let error : E := ZSpan.fract basis (scale • direction)
    have error_mem : error ∈ basis.parallelepiped :=
      ZSpan.fundamentalDomain_subset_parallelepiped basis
        (ZSpan.fract_mem_fundamentalDomain basis (scale • direction))
    have error_bound : pairing error error ≤ bound :=
      bound_spec ⟨error, error_mem, rfl⟩
    have floor_eq : (latticePoint stage : E) = scale • direction - error := by
      dsimp only [latticePoint, scaledFloorPoint, error]
      rw [ZSpan.fract_apply]
      simp [scale]
    have floor_diagonal_eq :
        pairing (latticePoint stage) (latticePoint stage) =
          pairing error error := by
      rw [floor_eq]
      simp only [map_sub, LinearMap.sub_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
      rw [direction_annihilates direction,
        direction_annihilates error, symmetric error direction,
        direction_annihilates error]
      ring
    have height_identity := diagonal_eq_height (latticePoint stage)
    rw [floor_diagonal_eq] at height_identity
    linarith
  have coordinate_tendsto :
      Tendsto
        (fun stage => basis.repr (latticePoint stage : E) coordinate)
        atTop atTop := by
    have scaled_coordinate_tendsto :
        Tendsto
          (fun stage : ℕ =>
            (((stage + 1 : ℕ) : ℝ) *
              basis.repr direction coordinate))
          atTop atTop := by
      have scale_tendsto :
          Tendsto (fun stage : ℕ => ((stage + 1 : ℕ) : ℝ))
            atTop atTop := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          tendsto_atTop_add_const_right atTop 1
            tendsto_natCast_atTop_atTop
      exact scale_tendsto.atTop_mul_const direction_coordinate_pos
    have floored_tendsto :=
      tendsto_floor_atTop.comp scaled_coordinate_tendsto
    have cast_floored_tendsto :
        Tendsto
          (fun stage =>
            ((⌊(((stage + 1 : ℕ) : ℝ) *
              basis.repr direction coordinate)⌋ : ℤ) : ℝ))
          atTop atTop :=
      tendsto_intCast_atTop_atTop.comp floored_tendsto
    rw [show
        (fun stage => basis.repr (latticePoint stage : E) coordinate) =
          (fun stage =>
            ((⌊(((stage + 1 : ℕ) : ℝ) *
              basis.repr direction coordinate)⌋ : ℤ) : ℝ)) by
      funext stage
      simp [latticePoint, scaledFloorPoint, map_smul]]
    exact cast_floored_tendsto
  have latticePoint_range_infinite : (Set.range latticePoint).Infinite := by
    intro range_finite
    have coordinate_range_finite :
        (Set.range fun stage =>
          basis.repr (latticePoint stage : E) coordinate).Finite := by
      change (Set.range
        ((fun current : Submodule.span ℤ (Set.range basis) =>
          basis.repr (current : E) coordinate) ∘ latticePoint)).Finite
      rw [Set.range_comp]
      exact range_finite.image
        (fun current : Submodule.span ℤ (Set.range basis) =>
          basis.repr (current : E) coordinate)
    exact (not_bddAbove_of_tendsto_atTop coordinate_tendsto)
      coordinate_range_finite.bddAbove
  have sublevel_finite :
      {current | height current ≤ bound / 2}.Finite :=
    Northcott.finite_le (h := height) (bound / 2)
  exact (latticePoint_range_infinite <|
    sublevel_finite.subset <| by
      rintro _ ⟨stage, rfl⟩
      exact latticePoint_height_le stage).elim

end

end NorthcottLatticePositivity
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
