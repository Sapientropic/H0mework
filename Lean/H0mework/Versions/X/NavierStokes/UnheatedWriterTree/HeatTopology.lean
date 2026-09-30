import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatSpace
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatLocal

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatTopology
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedTreeRieszKernel (Wave E)
noncomputable section

inductive Tree where
  | leaf
  | fork (left right : Tree)

def leaves : Tree → ℕ
  | .leaf => 1
  | .fork left right => leaves left+leaves right

def nodes : Tree → ℕ
  | .leaf => 0
  | .fork left right => nodes left+nodes right+1

theorem leaves_positive (tree : Tree) : 0 < leaves tree := by
  induction tree with
  | leaf => exact Nat.zero_lt_one
  | fork left right first last => exact Nat.add_pos_left first _

theorem leaves_nodes (tree : Tree) : leaves tree = nodes tree+1 := by
  induction tree with
  | leaf => rfl
  | fork left right first last => simp only [leaves, nodes, first, last]; omega

def grade (tree : Tree) : ℝ := 1/2-3*(leaves tree : ℝ)/14

theorem grade_le (tree : Tree) : grade tree ≤ 1/2 := by
  unfold grade
  linarith [Nat.cast_nonneg (α := ℝ) (leaves tree)]

theorem grade_fork (left right : Tree) :
    grade (.fork left right) = grade left+grade right-1/2 := by
  simp only [grade, leaves, Nat.cast_add]
  ring

theorem grade_total (left right : Tree) (small : leaves (.fork left right) ≤ 7) :
    -1 ≤ grade left+grade right := by
  have paid : (leaves left : ℝ)+leaves right ≤ 7 := by exact_mod_cast small
  unfold grade
  linarith

theorem left_small (left right : Tree) (small : leaves (.fork left right) ≤ 7) : leaves left ≤ 7 := by
  unfold leaves at small
  omega

theorem right_small (left right : Tree) (small : leaves (.fork left right) ≤ 7) : leaves right ≤ 7 := by
  unfold leaves at small
  omega

def factor (nu : Viscosity) : ℝ := NativeUnheatedTreeLocalHeat.cap nu*(2*Real.pi)

theorem factor_positive (nu : Viscosity) : 0 < factor nu := by
  unfold factor
  positivity [NativeUnheatedTreeLocalHeat.cap_positive nu]

def cost (nu : Viscosity) : ℝ := factor nu*NativeUnheatedTreeHeatConvolution.cap

theorem cost_nonnegative (nu : Viscosity) : 0 ≤ cost nu :=
  mul_nonneg (factor_positive nu).le NativeUnheatedTreeHeatConvolution.cap_nonnegative

def value (nu : Viscosity) : (tree : Tree) → leaves tree ≤ 7 → E → E
  | .leaf, _, input => lp.toNorm input
  | .fork left right, small, input => factor nu •
      NativeUnheatedTreeHeatSpace.value (grade left) (grade right) (grade_le left) (grade_le right)
        (grade_total left right small) (value nu left (left_small left right small) input)
          (value nu right (right_small left right small) input)

theorem value_nonnegative (nu : Viscosity) (tree : Tree) (small : leaves tree ≤ 7) (input : E) (k : Wave) :
    0 ≤ value nu tree small input k := by
  cases tree with
  | leaf => exact norm_nonneg _
  | fork left right =>
    change 0 ≤ factor nu*NativeUnheatedTreeHeatConvolution.row _ _ _ _ k
    exact mul_nonneg (factor_positive nu).le (NativeUnheatedTreeHeatConvolution.row_nonnegative _ _ _ _ _)

theorem value_bound (nu : Viscosity) (tree : Tree) (small : leaves tree ≤ 7) (input : E) :
    ‖value nu tree small input‖ ≤ cost nu^(nodes tree)*‖input‖^(leaves tree) := by
  induction tree with
  | leaf => simp only [value, lp.norm_toNorm, nodes, leaves, pow_zero, pow_one, one_mul, le_refl]
  | fork left right first last =>
    rw [value, norm_smul, Real.norm_of_nonneg (factor_positive nu).le]
    have paid := mul_le_mul_of_nonneg_left (NativeUnheatedTreeHeatSpace.value_norm
      (grade left) (grade right) (grade_le left) (grade_le right) (grade_total left right small)
      (value nu left (left_small left right small) input) (value nu right (right_small left right small) input))
      (factor_positive nu).le
    have both := mul_le_mul (first (left_small left right small)) (last (right_small left right small))
      (norm_nonneg _) (by positivity [cost_nonnegative nu])
    calc
      _ ≤ _ := paid
      _ = cost nu*(‖value nu left (left_small left right small) input‖*
          ‖value nu right (right_small left right small) input‖) := by unfold cost; ring
      _ ≤ cost nu*((cost nu^nodes left*‖input‖^leaves left)*(cost nu^nodes right*‖input‖^leaves right)) :=
        mul_le_mul_of_nonneg_left both (cost_nonnegative nu)
      _ = _ := by simp only [nodes, leaves, pow_add, pow_one]; ring

def envelope (nu : Viscosity) (tree : Tree) (small : leaves tree ≤ 7) (input : E) (k : Wave) : ℝ :=
  NativeUnheatedSexticLatticePower.mass k^(-grade tree/2)*value nu tree small input k

theorem envelope_nonnegative (nu : Viscosity) (tree : Tree) (small : leaves tree ≤ 7) (input : E) (k : Wave) :
    0 ≤ envelope nu tree small input k :=
  mul_nonneg (Real.rpow_pos_of_pos (NativeUnheatedSexticLatticePower.mass_positive k) _).le
    (value_nonnegative nu tree small input k)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatTopology
