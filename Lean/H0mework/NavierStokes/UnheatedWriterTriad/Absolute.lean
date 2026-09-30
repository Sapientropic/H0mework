import H0mework.NavierStokes.UnheatedWriterTriad.Sum

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeCompleteStressCarrier NativeHigherTimeJets NativeUnheatedPairInverseFlux
noncomputable section
variable (kernel : IntegerWavevector → IntegerWavevector → IntegerWavevector → ℂ)
  (cap : ℝ) (bounded : ∀ a b c, ‖kernel a b c‖ ≤ cap * weight c)
  (wave : IntegerWavevector) (i j l : Coordinate)

def term (left middle right : E) (indices : IntegerWavevector × IntegerWavevector) : ℂ :=
  innerTerm kernel wave i j left middle indices.1 indices.2 * right indices.1 l

include bounded

theorem inner_absolute_bound (left middle : E) (c : IntegerWavevector) :
    (∑' a, ‖innerTerm kernel wave i j left middle c a‖) ≤
      (3 * cap * ‖left‖ * ‖middle‖) * weight c := by
  have sums := (inner_summable kernel cap bounded wave i j left middle c).norm
  have upper := ((mixed_pair_summable left middle (wave-c) j i).norm.mul_left (cap * weight c))
  have compare := sums.tsum_le_tsum (fun a => by
    rw [innerTerm, norm_mul]
    exact mul_le_mul_of_nonneg_right (bounded _ _ _) (norm_nonneg _)) upper
  rw [tsum_mul_left] at compare
  exact compare.trans ((mul_le_mul_of_nonneg_left (absolute_pair_bound left middle (wave-c) j i)
    (mul_nonneg (cap_nonnegative kernel cap bounded) (weight_pos c).le)).trans_eq (by ring))

theorem double_absolute_bound (left middle right : E) (c : IntegerWavevector) :
    (∑' a, ‖term kernel wave i j l left middle right (c,a)‖) ≤
      (3 * cap * ‖left‖ * ‖middle‖) * (weight c * ‖right c‖) := by
  simp only [term, norm_mul, tsum_mul_right]
  exact (mul_le_mul (inner_absolute_bound kernel cap bounded wave i j left middle c)
    (norm_le_pi_norm (right c) l) (norm_nonneg _)
    (by positivity [cap_nonnegative kernel cap bounded, weight_pos c])).trans_eq (by ring)

theorem absolute_summable (left middle right : E) :
    Summable (fun indices => ‖term kernel wave i j l left middle right indices‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun c => ?_, ?_⟩
  · simpa only [term, norm_mul] using
      (inner_summable kernel cap bounded wave i j left middle c).norm.mul_right ‖right c l‖
  · exact ((weighted_summable right).mul_left (3 * cap * ‖left‖ * ‖middle‖)).of_nonneg_of_le
      (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (double_absolute_bound kernel cap bounded wave i j l left middle right)

theorem absolute_bound (left middle right : E) :
    (∑' indices, ‖term kernel wave i j l left middle right indices‖) ≤
      (3 * cap * ‖weights‖) * ‖left‖ * ‖middle‖ * ‖right‖ := by
  rw [(absolute_summable kernel cap bounded wave i j l left middle right).tsum_prod]
  have sums := (absolute_summable kernel cap bounded wave i j l left middle right).prod
  have compare := sums.tsum_le_tsum (double_absolute_bound kernel cap bounded wave i j l left middle right)
    ((weighted_summable right).mul_left (3 * cap * ‖left‖ * ‖middle‖))
  rw [tsum_mul_left] at compare
  exact compare.trans ((mul_le_mul_of_nonneg_left (weighted_bound right)
    (by positivity [cap_nonnegative kernel cap bounded])).trans_eq (by ring))

theorem value_eq_tsum (left middle right : E) :
    value kernel wave i j l left middle right = ∑' indices, term kernel wave i j l left middle right indices := by
  have sums := (absolute_summable kernel cap bounded wave i j l left middle right).of_norm
  rw [sums.tsum_prod]
  simp only [value, term, tsum_mul_right, innerValue]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadSum
