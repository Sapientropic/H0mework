import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatKernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatConvolution
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedTreeRieszPermutations (outputEquiv)
noncomputable section

def term (a b : ℝ) (L M : E) (k p : Wave) : ℝ :=
  NativeUnheatedTreeHeatKernel.kernel a b p (k-p)*|L p| * |M (k-p)|

theorem term_nonnegative (a b : ℝ) (L M : E) (k p : Wave) : 0 ≤ term a b L M k p := by
  unfold term
  positivity [NativeUnheatedTreeHeatKernel.kernel_nonnegative a b p (k-p)]

def row (a b : ℝ) (L M : E) (k : Wave) : ℝ := ∑' p, term a b L M k p

theorem row_nonnegative (a b : ℝ) (L M : E) (k : Wave) : 0 ≤ row a b L M k :=
  tsum_nonneg (term_nonnegative a b L M k)

theorem pair_recognition (a b : ℝ) (L M T : E) (index : Wave × Wave) :
    term a b L M index.1 index.2*|T index.1| =
      NativeUnheatedTreeHeatKernel.term a b L M T (outputEquiv.symm index) := by
  simp only [term, NativeUnheatedTreeHeatKernel.term, outputEquiv, Equiv.coe_fn_symm_mk,
    show index.2+(index.1-index.2) = index.1 by abel]

theorem pair_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M T : E) : Summable (fun index : Wave × Wave => term a b L M index.1 index.2*|T index.1|) := by
  simp_rw [pair_recognition]
  exact outputEquiv.symm.summable_iff.mpr (NativeUnheatedTreeHeatKernel.summable a b first last total L M T)

theorem row_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) (k : Wave) : Summable (term a b L M k) := by
  have paid := (pair_summable a b first last total L M (lp.single 2 k 1)).prod_factor k
  simpa only [lp.single_apply_self, abs_one, mul_one] using paid

theorem row_absolute_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) (k : Wave) : Summable (fun p => ‖term a b L M k p‖) := by
  simpa only [Real.norm_of_nonneg (term_nonnegative a b L M k _)] using row_summable a b first last total L M k

theorem testing_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M T : E) : Summable (fun k => row a b L M k*|T k|) := by
  have paid := (pair_summable a b first last total L M T).prod
  simpa only [tsum_mul_right, row] using paid

theorem testing_identity (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M T : E) : (∑' k, row a b L M k*|T k|) =
      ∑' index, NativeUnheatedTreeHeatKernel.term a b L M T index := by
  have same := (pair_summable a b first last total L M T).tsum_prod
  calc
    _ = ∑' index : Wave × Wave, term a b L M index.1 index.2*|T index.1| := by
      simpa only [row, tsum_mul_right] using same.symm
    _ = _ := by
      simp_rw [pair_recognition]
      exact outputEquiv.symm.tsum_eq _

def cap : ℝ := 6*Real.sqrt NativeUnheatedRieszKernel.constant

theorem cap_nonnegative : 0 ≤ cap := by unfold cap; positivity

theorem testing_bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M T : E) : (∑' k, row a b L M k*|T k|) ≤ cap*‖L‖*‖M‖*‖T‖ := by
  rw [testing_identity a b first last total]
  exact NativeUnheatedTreeHeatKernel.bound a b first last total L M T

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatConvolution
