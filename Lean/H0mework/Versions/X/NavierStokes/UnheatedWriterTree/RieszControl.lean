import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RieszPermutations

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeRiesz
open NativeUnheatedTreeRieszKernel NativeUnheatedTreeRieszPermutations
open NativeUnheatedSexticLatticePower
noncomputable section

theorem kernel_bound (p q : Wave) :
    density 1 p*density 1 q*density 1 (p+q) ≤
      radical (p+q)*density 2 p*density 2 q +
      radical p*density 2 q*density 2 (p+q) +
      radical q*density 2 p*density 2 (p+q) := by
  have positive := radical_positive p
  have positive' := radical_positive q
  have positive'' := radical_positive (p+q)
  have product0 := mul_nonneg (mul_nonneg positive.le positive'.le) positive''.le
  have square0 : 0 ≤ (radical p-radical q)^2 + (radical q-radical (p+q))^2 +
      (radical (p+q)-radical p)^2 := by positivity
  have paid := mul_nonneg (add_nonneg (add_nonneg positive.le positive'.le) positive''.le) square0
  have cubes : radical p*radical q*radical (p+q) ≤
      radical (p+q)^3+radical p^3+radical q^3 := by
    nlinarith only [paid, product0]
  apply (mul_le_mul_iff_right₀ (show 0 < radical p^2*radical q^2*radical (p+q)^2 by positivity)).mp
  convert! cubes using 1 <;> unfold density <;>
    field_simp [positive.ne', positive'.ne', positive''.ne']

def term (L M T : E) (index : Wave × Wave) : ℝ :=
  density 1 index.1*density 1 index.2*density 1 (index.1+index.2) *
    |L index.1| * |M index.2| * |T (index.1+index.2)|

theorem term_nonnegative (L M T : E) (index : Wave × Wave) : 0 ≤ term L M T index := by
  unfold term
  positivity [density_positive 1 index.1, density_positive 1 index.2,
    density_positive 1 (index.1+index.2)]

theorem term_bound (L M T : E) (index : Wave × Wave) :
    term L M T index ≤ outputTerm L M T index + firstTerm L M T index + secondTerm L M T index := by
  have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_bound index.1 index.2) (abs_nonneg (L index.1)))
    (abs_nonneg (M index.2))) (abs_nonneg (T (index.1+index.2)))
  exact paid.trans_eq (by unfold outputTerm firstTerm secondTerm; ring)

theorem summable (L M T : E) : Summable (term L M T) :=
  (((output_summable L M T).add (first_summable L M T)).add (second_summable L M T)).of_nonneg_of_le
    (term_nonnegative L M T) (term_bound L M T)

theorem bound (L M T : E) : (∑' index, term L M T index) ≤
    3*Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  have compared := (summable L M T).tsum_le_tsum (term_bound L M T)
    (((output_summable L M T).add (first_summable L M T)).add (second_summable L M T))
  rw [((output_summable L M T).add (first_summable L M T)).tsum_add (second_summable L M T),
    (output_summable L M T).tsum_add (first_summable L M T)] at compared
  exact compared.trans ((add_le_add (add_le_add (output_bound L M T) (first_bound L M T))
    (second_bound L M T)).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeRiesz
