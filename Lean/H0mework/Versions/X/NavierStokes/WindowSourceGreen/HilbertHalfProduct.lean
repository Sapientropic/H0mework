import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Fourier
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.FeedbackHalf

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHilbertHalfProduct
open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (polynomial polynomial_square)
open NativeUnheatedSexticLatticePower (radical radical_positive density mass)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
abbrev Wave := IntegerWavevector
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def amplitude {G : Type*} [NormedAddCommGroup G] (F : Finset Wave) (n : ℕ) (u : Wave → G) :
    NativeUnheatedTreeRieszKernel.E := ∑ k∈F,lp.single 2 k (radical k^n*‖u k‖)

theorem amplitude_apply {G : Type*} [NormedAddCommGroup G] (F : Finset Wave) (n : ℕ)
    (u : Wave → G) (k : Wave) : amplitude F n u k=if k∈F then radical k^n*‖u k‖ else 0 := by
  classical
  simp only [amplitude,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem amplitude_square {G : Type*} [NormedAddCommGroup G] (F : Finset Wave) (n : ℕ) (u : Wave → G) :
    ‖amplitude F n u‖^2=∑ k∈F,radical k^(2*n)*‖u k‖^2 := by
  have source:=lp.norm_sum_single (by norm_num : 0<(2:ℝ≥0∞).toReal) (fun k => radical k^n*‖u k‖) F
  simpa only [amplitude,ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,mul_pow,← pow_mul,Nat.mul_comm n 2] using source

def coefficients (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) (k : Wave) : E :=
  ∑ pair∈F×ˢG with pair.1+pair.2=k,f pair.2 • u pair.1

theorem coefficients_single (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) (k : Wave) :
    coefficients F G u f k=∑ p∈F,if k-p∈G then f (k-p) • u p else 0 := by
  classical
  simp only [coefficients,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _
  have criterion (q : Wave) : p+q=k ↔ q=k-p := by
    constructor
    · intro h; rw [← h]; abel
    · intro h; rw [h]; abel
  simp_rw [criterion]
  simp

theorem polynomial_product (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) (x : Torus) :
    polynomial (F+G) (coefficients F G u f) x=polynomial G f x • polynomial F u x := by
  classical
  have grouping:=Finset.sum_fiberwise_of_maps_to (s := F×ˢG) (t := F+G)
    (g := fun pair : Wave×Wave => pair.1+pair.2)
    (fun pair member => Finset.mem_add.mpr ⟨pair.1,(Finset.mem_product.mp member).1,
      pair.2,(Finset.mem_product.mp member).2,rfl⟩)
    (fun pair => mFourier (pair.1+pair.2) x • (f pair.2 • u pair.1))
  have grouped : polynomial (F+G) (coefficients F G u f) x=
      ∑ k∈F+G,∑ pair∈F×ˢG with pair.1+pair.2=k,mFourier (pair.1+pair.2) x • (f pair.2 • u pair.1) := by
    simp only [polynomial,ContinuousMap.coe_mk,coefficients,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro pair inside
    rw [(Finset.mem_filter.mp inside).2]
  rw [grouped,grouping]
  simp only [Finset.sum_product,mFourier_add,smul_smul,polynomial,ContinuousMap.coe_mk,smul_eq_mul,
    Finset.smul_sum,Finset.sum_mul,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  ring

theorem coefficient_bound (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) (k : Wave) :
    ‖coefficients F G u f k‖≤NativeWindowHistoryAdjointSpatialHalf.row true (amplitude F 2 u) (amplitude G 1 f) k := by
  classical
  rw [coefficients_single]
  apply (norm_sum_le _ _).trans
  have term (p : Wave) (inside : p∈F) :
      ‖if k-p∈G then f (k-p) • u p else 0‖≤
        NativeWindowHistoryAdjointSpatialHalf.kernel true p (k-p)*|amplitude F 2 u p| * |amplitude G 1 f (k-p)| := by
    by_cases kept : k-p∈G
    · rw [if_pos kept,amplitude_apply,if_pos inside,amplitude_apply,if_pos kept,norm_smul]
      rw [abs_of_nonneg (by positivity [radical_positive p]),abs_of_nonneg (by positivity [radical_positive (k-p)])]
      simp only [NativeWindowHistoryAdjointSpatialHalf.kernel,if_true,density,pow_one]
      have p0:radical p≠0:=(radical_positive p).ne'
      have q0:radical (k-p)≠0:=(radical_positive (k-p)).ne'
      apply le_of_eq
      field_simp [p0,q0]
    · simp only [norm_zero,amplitude_apply,if_neg kept,abs_zero,mul_zero,le_refl]
  apply (Finset.sum_le_sum term).trans
  exact (NativeWindowHistoryAdjointSpatialHalf.row_summable true (amplitude F 2 u) (amplitude G 1 f) k).sum_le_tsum F
    (fun p _ => by positivity [NativeWindowHistoryAdjointSpatialHalf.kernel_nonnegative true p (k-p)])

theorem finite_product_bound (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) :
    (∫ x : Torus,‖polynomial G f x • polynomial F u x‖^2)≤
      NativeWindowHistoryAdjointSpatialHalf.cap^2*(∑ p∈F,radical p^4*‖u p‖^2)*(∑ q∈G,radical q^2*‖f q‖^2) := by
  simp_rw [← polynomial_product F G u f]
  rw [polynomial_square]
  have compare:=Finset.sum_le_sum (s := F+G) fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (coefficient_bound F G u f k) 2
  have paid:=NativeWindowHistoryAdjointSpatialHalf.row_square_bound true (amplitude F 2 u) (amplitude G 1 f) (F+G)
  apply compare.trans (paid.trans_eq ?_)
  rw [mul_pow,mul_pow,amplitude_square,amplitude_square]


abbrev Scalar := Lp ℂ 2 (volume : Measure Torus)
abbrev Physical (E : Type*) [NormedAddCommGroup E] := Lp E 2 (volume : Measure Torus)

def multiply (u : C(Torus,E)) : Scalar →L[ℂ] Physical E :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip.holderL (volume : Measure Torus) ∞ 2 2
    ((ContinuousMap.toLp ∞ volume ℂ) u)

theorem multiply_ae (u : C(Torus,E)) (f : Scalar) :
    multiply u f=ᵐ[volume] fun x => f x • u x := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℂ) (E := E) (F := ℂ) (G := E) (r := 2)
    (ContinuousLinearMap.lsmul ℂ ℂ).flip ((ContinuousMap.toLp ∞ volume ℂ) u) f,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (volume : Measure Torus) u] with x applied original
  change multiply u f x=f x • (((ContinuousMap.toLp ∞ volume ℂ) u) x) at applied
  exact applied.trans (congrArg (fun v : E => f x • v) original)


theorem product_memLp (u : C(Torus,E)) (f : Scalar) :
    MemLp (fun x => f x • u x) 2 (volume : Measure Torus) :=
  (memLp_congr_ae (multiply_ae u f)).mp (Lp.memLp (multiply u f))

theorem lp_square (v : Physical E) : ‖v‖^2=∫x : Torus,‖v x‖^2 := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem multiply_square (u : C(Torus,E)) (f : Scalar) :
    ‖multiply u f‖^2=∫x : Torus,‖f x • u x‖^2 := by
  rw [lp_square]
  exact integral_congr_ae ((multiply_ae u f).fun_comp (fun v => ‖v‖^2))

theorem polynomial_toLp (G : Finset Wave) (f : Wave → ℂ) :
    (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (polynomial G f)=∑k∈G,f k • mFourierLp 2 k := by
  have original : polynomial G f=∑k∈G,f k • mFourier k := by
    apply ContinuousMap.ext
    intro x
    simp only [polynomial,ContinuousMap.coe_mk,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [original,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]

theorem scalar_product_bound (f : Scalar) (B : ℝ)
    (paid : ∀ G : Finset Wave,(∑q∈G,radical q^2*‖mFourierCoeff f q‖^2)≤B)
    (F : Finset Wave) (u : Wave → E) :
    (∫x : Torus,‖f x • polynomial F u x‖^2)≤
      NativeWindowHistoryAdjointSpatialHalf.cap^2*(∑p∈F,radical p^4*‖u p‖^2)*B := by
  have convergence : Tendsto (fun G : Finset Wave =>
      (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (polynomial G (mFourierCoeff f))) atTop (𝓝 f) := by
    simp only [polynomial_toLp]
    exact (hasSum_mFourier_series_L2 f)
  have multiplied:=((multiply (polynomial F u)).continuous.tendsto f).comp convergence
  have normed:=((continuous_norm.pow 2).tendsto (multiply (polynomial F u) f)).comp multiplied
  rw [← multiply_square]
  apply le_of_tendsto normed
  filter_upwards with G
  dsimp only [Function.comp_def,Pi.pow_apply]
  have scalar:=ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus)
    (polynomial G (mFourierCoeff f))
  rw [multiply_square]
  have read : (∫x : Torus,‖((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ)
      (polynomial G (mFourierCoeff f))) x • polynomial F u x‖^2)=
      ∫x : Torus,‖polynomial G (mFourierCoeff f) x • polynomial F u x‖^2 := by
    apply integral_congr_ae
    filter_upwards [scalar] with x actual
    rw [actual]
  rw [read]
  exact (finite_product_bound F G u (mFourierCoeff f)).trans
    (mul_le_mul_of_nonneg_left (paid G) (by positivity [radical_positive]))


theorem scalar_product_of_spectrum (f : Scalar) (c : NativePhysicalFourier.ScalarSequence)
    (read : ∀ k,c k=(radical k:ℂ)*mFourierCoeff f k) (F : Finset Wave) (u : Wave → E) :
    (∫x : Torus,‖f x • polynomial F u x‖^2)≤
      NativeWindowHistoryAdjointSpatialHalf.cap^2*(∑p∈F,radical p^4*‖u p‖^2)*‖c‖^2 := by
  apply scalar_product_bound f (‖c‖^2) _ F u
  intro G
  have sum : Summable (fun k => ‖c k‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mp (lp.memℓp c)
  have whole : ‖c‖^2=∑'k,‖c k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) c
  have original (k : Wave) : ‖c k‖^2=radical k^2*‖mFourierCoeff f k‖^2 := by
    rw [read,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [whole]
  simpa only [original] using sum.sum_le_tsum G (fun k _ => sq_nonneg ‖c k‖)

end
end SaturationMonoid.NavierStokes.NativeWindowHilbertHalfProduct
