import H0mework.Versions.X.NavierStokes.WindowSourceGreen.HilbertTripleProduct
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHilbertSquareProduct
open Set Filter MeasureTheory UnitAddTorus
open NativeWindowHilbertHalfProduct NativeWindowHilbertTripleProduct
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativePhysicalFourier (Torus)
open NativeUnheatedSexticLatticePower (radical radical_positive)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem square_toLp (f : Torus → E) (regular : MemLp f 2 (volume : Measure Torus)) :
    ‖regular.toLp f‖^2=∫x : Torus,‖f x‖^2 := by
  rw [lp_square]
  exact integral_congr_ae (regular.coeFn_toLp.fun_comp (fun v => ‖v‖^2))

private theorem physical_fatou (v : ℕ → Torus → E) (f : Torus → E)
    (regular : ∀ n,MemLp (v n) 2 (volume : Measure Torus))
    (limit : ∀ᵐ x ∂(volume : Measure Torus),Tendsto (fun n => v n x) atTop (𝓝 (f x)))
    (B : ℝ) (nonnegative : 0≤B) (paid : ∀ n,(∫x : Torus,‖v n x‖^2)≤B) :
    MemLp f 2 (volume : Measure Torus) ∧ (∫x : Torus,‖f x‖^2)≤B := by
  have bound (n : ℕ) : eLpNorm (v n) 2 (volume : Measure Torus)≤ENNReal.ofReal (Real.sqrt B) := by
    have normed : ‖(regular n).toLp (v n)‖≤Real.sqrt B := by
      have square : ‖(regular n).toLp (v n)‖^2≤B := (square_toLp _ _).trans_le (paid n)
      nlinarith only [square,Real.sq_sqrt nonnegative,norm_nonneg ((regular n).toLp (v n)),Real.sqrt_nonneg B]
    rw [← Lp.enorm_toLp (regular n),← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal normed
  have lowered:=Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall bound)
    (fun n => (regular n).aestronglyMeasurable) limit
  have measured:=aestronglyMeasurable_of_tendsto_ae atTop (fun n => (regular n).aestronglyMeasurable) limit
  have member : MemLp f 2 (volume : Measure Torus) := ⟨measured,lowered.trans_lt ENNReal.ofReal_lt_top⟩
  have normed : ‖member.toLp f‖≤Real.sqrt B := by
    have realBound:=ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (Real.sqrt B)≠⊤) lowered
    simpa only [Lp.norm_toLp,ENNReal.toReal_ofReal (Real.sqrt_nonneg B)] using realBound
  refine ⟨member,?_⟩
  rw [← square_toLp f member]
  exact (pow_le_pow_left₀ (norm_nonneg _) normed 2).trans_eq (Real.sq_sqrt nonnegative)

def squarePolynomial (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) : C(Torus,E) where
  toFun x := polynomial G f x • (polynomial G f x • polynomial F u x)
  continuous_toFun := (polynomial G f).continuous.smul
    ((polynomial G f).continuous.smul (polynomial F u).continuous)

theorem finite_square_bound (F G : Finset Wave) (u : Wave → E) (f : Wave → ℂ) :
    (∫x : Torus,‖squarePolynomial F G u f x‖^2)≤
      (NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
        (∑k∈F,radical k^4*‖u k‖^2)*(∑k∈G,radical k^4*‖f k‖^2)^2 := by
  have paid:=triple_product_bound F G G u f f
  simp only [squarePolynomial,ContinuousMap.coe_mk,smul_smul]
  exact paid.trans_eq (by ring)

theorem scalar_square_bound (f : Scalar) (B : ℝ)
    (paid : ∀ G : Finset Wave,(∑k∈G,radical k^4*‖mFourierCoeff f k‖^2)≤B)
    (F : Finset Wave) (u : Wave → E) :
    MemLp (fun x => f x • (f x • polynomial F u x)) 2 (volume : Measure Torus) ∧
      (∫x : Torus,‖f x • (f x • polynomial F u x)‖^2)≤
        (NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
          (∑k∈F,radical k^4*‖u k‖^2)*B^2 := by
  have convergence : Tendsto (fun G : Finset Wave =>
      (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (polynomial G (mFourierCoeff f))) atTop (𝓝 f) := by
    simp only [polynomial_toLp]
    exact hasSum_mFourier_series_L2 f
  obtain ⟨sets,_,pointwise⟩:=(tendstoInMeasure_of_tendsto_Lp convergence).exists_seq_tendsto_ae'
  have representatives : ∀ᵐ x ∂(volume : Measure Torus),∀ n : ℕ,
      ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (polynomial (sets n) (mFourierCoeff f))) x=
        polynomial (sets n) (mFourierCoeff f) x := by
    apply ae_all_iff.mpr
    intro n
    exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) _
  have limit : ∀ᵐ x ∂(volume : Measure Torus),Tendsto
      (fun n => squarePolynomial F (sets n) u (mFourierCoeff f) x) atTop
        (𝓝 (f x • (f x • polynomial F u x))) := by
    filter_upwards [pointwise,representatives] with x convergence original
    have scalar : Tendsto (fun n => polynomial (sets n) (mFourierCoeff f) x) atTop (𝓝 (f x)) := by
      exact convergence.congr' (Eventually.of_forall (fun n => original n))
    exact scalar.smul (scalar.smul tendsto_const_nhds)
  have coefficient0 : 0≤NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant*
      (∑k∈F,radical k^4*‖u k‖^2) := by positivity [NativeUnheatedRieszKernel.constant_nonnegative]
  apply physical_fatou (fun n => squarePolynomial F (sets n) u (mFourierCoeff f)) _
    (fun n => ContinuousMap.memLp volume ℂ _) limit _ (mul_nonneg coefficient0 (sq_nonneg B))
  intro n
  have first:=finite_square_bound F (sets n) u (mFourierCoeff f)
  have square:=pow_le_pow_left₀ (Finset.sum_nonneg (s := sets n) fun k _ =>
    mul_nonneg (pow_nonneg (radical_positive k).le 4) (sq_nonneg ‖mFourierCoeff f k‖)) (paid (sets n)) 2
  exact first.trans (mul_le_mul_of_nonneg_left square coefficient0)

theorem scalar_square_of_spectrum (f : Scalar) (c : NativePhysicalFourier.ScalarSequence)
    (read : ∀ k,c k=(radical k:ℂ)^2*mFourierCoeff f k) (F : Finset Wave) (u : Wave → E) :
    MemLp (fun x => f x • (f x • polynomial F u x)) 2 (volume : Measure Torus) ∧
      (∫x : Torus,‖f x • (f x • polynomial F u x)‖^2)≤
        (NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
          (∑k∈F,radical k^4*‖u k‖^2)*‖c‖^4 := by
  have paid (G : Finset Wave) : (∑k∈G,radical k^4*‖mFourierCoeff f k‖^2)≤‖c‖^2 := by
    have sum : Summable (fun k => ‖c k‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mp (lp.memℓp c)
    have whole : ‖c‖^2=∑'k,‖c k‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) c
    have original (k : Wave) : ‖c k‖^2=radical k^4*‖mFourierCoeff f k‖^2 := by
      rw [read,norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (radical_positive k),← pow_mul]
    rw [whole]
    simpa only [original] using sum.sum_le_tsum G (fun k _ => sq_nonneg ‖c k‖)
  simpa only [← pow_mul] using scalar_square_bound f (‖c‖^2) paid F u


theorem norm_square_of_spectrum (f : Scalar) (c : NativePhysicalFourier.ScalarSequence)
    (read : ∀ k,c k=(radical k:ℂ)^2*mFourierCoeff f k) (F : Finset Wave) (u : Wave → E) :
    MemLp (fun x => (‖f x‖^2:ℂ) • polynomial F u x) 2 (volume : Measure Torus) ∧
      (∫x : Torus,‖(‖f x‖^2:ℂ) • polynomial F u x‖^2)≤
        (NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
          (∑k∈F,radical k^4*‖u k‖^2)*‖c‖^4 := by
  have paid:=scalar_square_of_spectrum f c read F u
  have measured : AEStronglyMeasurable (fun x => (‖f x‖^2:ℂ) • polynomial F u x) (volume : Measure Torus) :=
    ((show Continuous (fun z : ℂ => (‖z‖^2:ℂ)) by fun_prop).comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable).smul (polynomial F u).continuous.aestronglyMeasurable
  have equal (x : Torus) : ‖f x • (f x • polynomial F u x)‖=‖(‖f x‖^2:ℂ) • polynomial F u x‖ := by
    simp only [norm_smul]
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (f x))]
    ring
  refine ⟨paid.1.congr_norm measured (Eventually.of_forall equal),?_⟩
  simp_rw [← equal]
  exact paid.2

end
end SaturationMonoid.NavierStokes.NativeWindowHilbertSquareProduct
