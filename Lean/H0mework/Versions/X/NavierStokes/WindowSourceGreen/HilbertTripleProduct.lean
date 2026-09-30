import H0mework.Versions.X.NavierStokes.WindowSourceGreen.HilbertHalfProduct

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHilbertTripleProduct
open Set Filter MeasureTheory UnitAddTorus
open NativeWindowHilbertHalfProduct
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativePhysicalFourier (Torus)
open NativeUnheatedSexticLatticePower (radical radical_positive density)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem weighted_coefficient (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) (k : Wave) :
    radical k^2*‖coefficients F G u f k‖^2≤NativeUnheatedRieszKernel.constant*
      ∑p∈F,|amplitude F 2 u p|^2*|amplitude G 2 f (k-p)|^2 := by
  classical
  let K:=NativeUnheatedTreeRieszKernel.kernel k
  let a:=amplitude F 2 u
  let b:=amplitude G 2 f
  have point (p : Wave) (inside : p∈F) :
      radical k*‖if k-p∈G then f (k-p) • u p else 0‖=K p*(|a p| * |b (k-p)|) := by
    dsimp only [K,a,b]
    by_cases kept : k-p∈G
    · rw [if_pos kept,amplitude_apply,if_pos inside,amplitude_apply,if_pos kept,norm_smul]
      rw [abs_of_nonneg (by positivity [radical_positive p]),abs_of_nonneg (by positivity [radical_positive (k-p)])]
      simp only [NativeUnheatedTreeRieszKernel.kernel,density]
      field_simp [(radical_positive p).ne',(radical_positive (k-p)).ne']
    · simp only [amplitude_apply,if_neg kept,norm_zero,abs_zero,mul_zero]
  have triangle:=mul_le_mul_of_nonneg_left (norm_sum_le F (fun p => if k-p∈G then f (k-p) • u p else 0))
    (radical_positive k).le
  rw [← coefficients_single,Finset.mul_sum] at triangle
  have same: (∑p∈F,radical k*‖if k-p∈G then f (k-p) • u p else 0‖)=∑p∈F,K p*(|a p| * |b (k-p)|) :=
    Finset.sum_congr rfl point
  rw [same] at triangle
  have squared:=pow_le_pow_left₀ (mul_nonneg (radical_positive k).le (norm_nonneg _)) triangle 2
  rw [mul_pow] at squared
  have cauchy:=Finset.sum_mul_sq_le_sq_mul_sq F K (fun p => |a p| * |b (k-p)|)
  have cap:=NativeUnheatedTreeRieszKernel.kernel_square_sum k F
  have paid:=mul_le_mul_of_nonneg_right cap (Finset.sum_nonneg (s := F) fun p _ => sq_nonneg (|a p| * |b (k-p)|))
  exact squared.trans (cauchy.trans (by simpa only [mul_pow,a,b] using paid))

theorem weighted_product_bound (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) :
    (∑k∈F+G,radical k^2*‖coefficients F G u f k‖^2)≤NativeUnheatedRieszKernel.constant*
      (∑p∈F,radical p^4*‖u p‖^2)*(∑q∈G,radical q^4*‖f q‖^2) := by
  classical
  have compare:=Finset.sum_le_sum (s := F+G) fun k _ => weighted_coefficient F G u f k
  apply compare.trans
  rw [← Finset.mul_sum,Finset.sum_comm]
  have rows (p : Wave) (inside : p∈F) :
      (∑k∈F+G,|amplitude F 2 u p|^2*|amplitude G 2 f (k-p)|^2)≤
        (radical p^4*‖u p‖^2)*‖amplitude G 2 f‖^2 := by
    rw [← Finset.mul_sum]
    have paid:=mul_le_mul_of_nonneg_left
      (NativeUnheatedTreeRieszKernel.translated_square_sum (amplitude G 2 f) p (F+G))
      (sq_nonneg |amplitude F 2 u p|)
    simpa only [amplitude_apply,if_pos inside,sq_abs,mul_pow,← pow_mul] using paid
  have paid:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum rows) NativeUnheatedRieszKernel.constant_nonnegative
  rw [← Finset.sum_mul,amplitude_square] at paid
  exact paid.trans_eq (by ring)

theorem triple_product_bound (F G S : Finset Wave) (u : Wave → E) (f g : Wave → ℂ) :
    (∫x : Torus,‖(polynomial G f x*polynomial S g x) • polynomial F u x‖^2)≤
      (NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
        (∑k∈F,radical k^4*‖u k‖^2)*(∑p∈G,radical p^4*‖f p‖^2)*(∑q∈S,radical q^4*‖g q‖^2) := by
  have product (x : Torus) : polynomial G f x*polynomial S g x=polynomial (G+S) (coefficients G S f g) x := by
    rw [polynomial_product,smul_eq_mul,mul_comm]
  simp_rw [product]
  have paid:=finite_product_bound F (G+S) u (coefficients G S f g)
  apply paid.trans
  have source:=mul_le_mul_of_nonneg_left (weighted_product_bound G S f g)
    (show 0≤NativeWindowHistoryAdjointSpatialHalf.cap^2*(∑k∈F,radical k^4*‖u k‖^2) by positivity)
  exact source.trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeWindowHilbertTripleProduct
