import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false
open scoped ComplexConjugate ENNReal
open MeasureTheory UnitAddTorus

namespace SaturationMonoid.NavierStokes.NativeFourierProduct

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Torus := UnitAddTorus (Fin 3)
abbrev Wave := Fin 3 → ℤ
abbrev ScalarL2 := Lp ℂ 2 (volume : Measure Torus)

theorem product_memLp (f g : ScalarL2) :
    MemLp (fun x => f x * g x) 1 (volume : Measure Torus) :=
  (Lp.memLp g).mul' (Lp.memLp f)

theorem product_integrable (f g : ScalarL2) :
    Integrable (fun x => f x * g x) (volume : Measure Torus) :=
  memLp_one_iff_integrable.mp (product_memLp f g)

private theorem monomial_norm (k : Wave) (x : Torus) : ‖mFourier k x‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

private theorem modulatedConjugate_memLp (g : ScalarL2) (k : Wave) :
    MemLp (fun x => mFourier k x * conj (g x)) 2 (volume : Measure Torus) := by
  apply (Lp.memLp g).mono
  · exact (mFourier k).continuous.aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.memLp g).1)
  · exact Filter.Eventually.of_forall fun x => by simp [monomial_norm]

private def modulatedConjugate (g : ScalarL2) (k : Wave) : ScalarL2 :=
  (modulatedConjugate_memLp g k).toLp _

private theorem modulatedConjugate_coeff (g : ScalarL2) (k p : Wave) :
    mFourierCoeff (modulatedConjugate g k) p = conj (mFourierCoeff g (k - p)) := by
  rw [mFourierCoeff, mFourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [(modulatedConjugate_memLp g k).coeFn_toLp] with x same
  change mFourier (-p) x * modulatedConjugate g k x = _
  rw [show modulatedConjugate g k x = mFourier k x * conj (g x) from same]
  simp only [smul_eq_mul, map_mul, ← mFourier_neg, neg_neg]
  rw [← mul_assoc, ← mFourier_add]
  congr 2
  abel

theorem product_hasSum (f g : ScalarL2) (k : Wave) :
    HasSum (fun p => mFourierCoeff f p * mFourierCoeff g (k - p))
      (mFourierCoeff (fun x => f x * g x) k) := by
  have parseval := hasSum_prod_mFourierCoeff f (modulatedConjugate g k)
  have value : (∫ x, conj (f x) * modulatedConjugate g k x) =
      conj (mFourierCoeff (fun x => f x * g x) k) := by
    rw [mFourierCoeff, ← integral_conj]
    apply integral_congr_ae
    filter_upwards [(modulatedConjugate_memLp g k).coeFn_toLp] with x same
    rw [show modulatedConjugate g k x = mFourier k x * conj (g x) from same]
    simp only [smul_eq_mul, map_mul, ← mFourier_neg, neg_neg]
    ring
  rw [value] at parseval
  simp_rw [modulatedConjugate_coeff, ← map_mul] at parseval
  exact Complex.hasSum_conj'.mp parseval

theorem product_coeff (f g : ScalarL2) (k : Wave) :
    mFourierCoeff (fun x => f x * g x) k =
      ∑' p, mFourierCoeff f p * mFourierCoeff g (k - p) :=
  (product_hasSum f g k).tsum_eq.symm

theorem product_coeff_absolute (f g : ScalarL2) (k : Wave) :
    Summable (fun p => ‖mFourierCoeff f p * mFourierCoeff g (k - p)‖) :=
  (product_hasSum f g k).summable.norm

end
end SaturationMonoid.NavierStokes.NativeFourierProduct
