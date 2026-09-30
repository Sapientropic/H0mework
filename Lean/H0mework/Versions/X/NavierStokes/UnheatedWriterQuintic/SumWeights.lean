import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Weights
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Sum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticSum
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedQuinticWeights NativeUnheatedTriadSum
noncomputable section
abbrev Pair := IntegerWavevector × IntegerWavevector
abbrev Index := Pair × IntegerWavevector

def etaL2 : NativeFullOrderAction.ScalarL2 :=
  ⟨eta, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using eta_square_summable)⟩

theorem weighted_summable (value : E) : Summable (fun k => eta k*‖value k‖) := by
  have paid := lp.summable_mul (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
    rw [Real.holderConjugate_iff]; norm_num) etaL2 (rowNorms value)
  simpa only [etaL2, rowNorms, Real.norm_of_nonneg (eta_nonnegative _), Real.norm_of_nonneg (norm_nonneg _)] using paid

theorem weighted_bound (value : E) : (∑' k, eta k*‖value k‖) ≤ ‖etaL2‖*‖value‖ := by
  have paid := lp.tsum_mul_le_mul_norm' (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
    rw [Real.holderConjugate_iff]; norm_num) etaL2 (rowNorms value)
  rw [rowNorms_norm] at paid
  simpa only [etaL2, rowNorms, Real.norm_of_nonneg (eta_nonnegative _), Real.norm_of_nonneg (norm_nonneg _)] using paid

def plane (wave : IntegerWavevector) (U V : E) (outer : Pair) : ℝ :=
  (eta outer.1*‖V outer.1‖)*(eta (wave-outer.1-outer.2)*‖U (wave-outer.1-outer.2)‖)

theorem plane_nonnegative (wave : IntegerWavevector) (U V : E) (outer : Pair) : 0 ≤ plane wave U V outer :=
  mul_nonneg (mul_nonneg (eta_nonnegative _) (norm_nonneg _)) (mul_nonneg (eta_nonnegative _) (norm_nonneg _))

theorem plane_summable (wave : IntegerWavevector) (U V : E) : Summable (plane wave U V) := by
  let reindex : Pair ≃ Pair := Equiv.prodCongrRight fun c => Equiv.subLeft (wave-c)
  have product := (weighted_summable V).mul_of_nonneg (weighted_summable U)
    (fun k => mul_nonneg (eta_nonnegative k) (norm_nonneg _)) (fun k => mul_nonneg (eta_nonnegative k) (norm_nonneg _))
  exact reindex.summable_iff.mpr product

theorem plane_sum (wave : IntegerWavevector) (U V : E) :
    (∑' outer, plane wave U V outer) = (∑' k, eta k*‖V k‖)*(∑' k, eta k*‖U k‖) := by
  rw [(plane_summable wave U V).tsum_prod]
  have inner (c : IntegerWavevector) : (∑' a, plane wave U V (c,a)) =
      (eta c*‖V c‖)*(∑' k, eta k*‖U k‖) := by
    change (∑' a, (eta c*‖V c‖)*(eta (wave-c-a)*‖U (wave-c-a)‖)) = _
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.subLeft (wave-c)).tsum_eq (fun k => eta k*‖U k‖)
  simp_rw [inner]
  rw [tsum_mul_right]

theorem plane_bound (wave : IntegerWavevector) (U V : E) :
    (∑' outer, plane wave U V outer) ≤ ‖etaL2‖^2*‖U‖*‖V‖ := by
  rw [plane_sum]
  exact (mul_le_mul (weighted_bound V) (weighted_bound U)
    (tsum_nonneg fun k => mul_nonneg (eta_nonnegative k) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticSum
