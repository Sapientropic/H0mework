import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert

/-! The actual coframe half density on the native common Hilbert space. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceQuantumHalfDensityHilbert
open MeasureTheory Filter
open scoped ENNReal Topology
open SourceQuantumConfigurationHilbert

abbrev BaseHilbert := Lp ℂ 2 chartMeasure

def halfDensity (N : ℕ) (z : chart) : ℝ := Real.sqrt (numberWeight N z)

theorem halfDensity_pos (N : ℕ) (z : chart) : 0 < halfDensity N z :=
  Real.sqrt_pos.2 (numberWeight_pos N z)

theorem halfDensity_sq (N : ℕ) (z : chart) : halfDensity N z ^ 2 = numberWeight N z :=
  Real.sq_sqrt (numberWeight_pos N z).le

theorem halfDensity_continuous (N : ℕ) : Continuous (halfDensity N) :=
  Real.continuous_sqrt.comp (numberWeight_continuous N)

def multiplyHalf (N : ℕ) (f : chart → ℂ) : chart → ℂ :=
  fun z => (halfDensity N z : ℂ) * f z

theorem weight_measurable (N : ℕ) :
    Measurable (fun z => ENNReal.ofReal (numberWeight N z)) :=
  (numberWeight_continuous N).measurable.ennreal_ofReal

theorem weighted_null_sets (N : ℕ) : chartMeasure ≪ numberMeasure N :=
  withDensity_absolutelyContinuous' (weight_measurable N).aemeasurable
    (Eventually.of_forall fun z => (ENNReal.ofReal_pos.2 (numberWeight_pos N z)).ne')

theorem halfDensity_enorm_sq (N : ℕ) (z : chart) :
    ‖(halfDensity N z : ℂ)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (numberWeight N z) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (halfDensity_pos N z), ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (halfDensity_pos N z).le, halfDensity_sq]

theorem eLpNorm_multiplyHalf (N : ℕ) (f : chart → ℂ) :
    eLpNorm (multiplyHalf N f) 2 chartMeasure = eLpNorm f 2 (numberMeasure N) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [numberMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (weight_measurable N) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  apply lintegral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [multiplyHalf, enorm_mul, Pi.mul_apply,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), halfDensity_enorm_sq]

theorem multiplyHalf_memLp (N : ℕ) (f : SectorHilbert N) :
    MemLp (multiplyHalf N f) 2 chartMeasure := by
  constructor
  · exact ((Complex.continuous_ofReal.comp (halfDensity_continuous N)).aestronglyMeasurable).mul
      ((Lp.memLp f).aestronglyMeasurable.mono_ac (weighted_null_sets N))
  · rw [eLpNorm_multiplyHalf]
    exact (Lp.memLp f).2

def halfDensityMap (N : ℕ) : SectorHilbert N →ₗᵢ[ℂ] BaseHilbert where
  toFun f := (multiplyHalf_memLp N f).toLp (multiplyHalf N f)
  map_add' := by
    intro f g
    ext1
    filter_upwards [(multiplyHalf_memLp N (f + g)).coeFn_toLp,
      (multiplyHalf_memLp N f).coeFn_toLp, (multiplyHalf_memLp N g).coeFn_toLp,
      Lp.coeFn_add ((multiplyHalf_memLp N f).toLp _) ((multiplyHalf_memLp N g).toLp _),
      (Lp.coeFn_add f g).filter_mono (weighted_null_sets N).ae_le] with z hadd hf hg hout hin
    rw [hadd, hout]
    simp only [Pi.add_apply] at *
    rw [hf, hg]
    change (halfDensity N z : ℂ) * ((f + g : SectorHilbert N) z) =
      (halfDensity N z : ℂ) * f z + (halfDensity N z : ℂ) * g z
    rw [hin, mul_add]
  map_smul' := by
    intro c f
    ext1
    filter_upwards [(multiplyHalf_memLp N (c • f)).coeFn_toLp,
      (multiplyHalf_memLp N f).coeFn_toLp,
      Lp.coeFn_smul c ((multiplyHalf_memLp N f).toLp _),
      (Lp.coeFn_smul c f).filter_mono (weighted_null_sets N).ae_le] with z hc hf hout hin
    simp only [RingHom.id_apply]
    rw [hc, hout]
    simp only [Pi.smul_apply] at *
    rw [hf]
    simp [multiplyHalf, hin, mul_left_comm]
  norm_map' := by
    intro f
    change ‖(multiplyHalf_memLp N f).toLp (multiplyHalf N f)‖ = ‖f‖
    simp only [Lp.norm_def]
    rw [eLpNorm_congr_ae (multiplyHalf_memLp N f).coeFn_toLp, eLpNorm_multiplyHalf]

theorem halfDensityMap_apply (N : ℕ) (f : SectorHilbert N) :
    halfDensityMap N f =ᵐ[chartMeasure] multiplyHalf N f :=
  (multiplyHalf_memLp N f).coeFn_toLp

def divideHalf (N : ℕ) (f : chart → ℂ) : chart → ℂ :=
  fun z => (halfDensity N z : ℂ)⁻¹ * f z

theorem multiply_divideHalf (N : ℕ) (f : chart → ℂ) :
    multiplyHalf N (divideHalf N f) = f := by
  funext z
  have hn : (halfDensity N z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfDensity_pos N z).ne'
  simp [multiplyHalf, divideHalf, hn]

theorem divideHalf_memLp (N : ℕ) (f : BaseHilbert) :
    MemLp (divideHalf N f) 2 (numberMeasure N) := by
  constructor
  · exact (Complex.continuous_ofReal.comp (halfDensity_continuous N)).measurable.inv.aestronglyMeasurable.mul
      ((Lp.memLp f).aestronglyMeasurable.mono_ac
        (withDensity_absolutelyContinuous chartMeasure _))
  · rw [← eLpNorm_multiplyHalf, multiply_divideHalf]
    exact (Lp.memLp f).2

theorem halfDensityMap_surjective (N : ℕ) : Function.Surjective (halfDensityMap N) := by
  intro f
  refine ⟨(divideHalf_memLp N f).toLp (divideHalf N f), ?_⟩
  ext1
  filter_upwards [halfDensityMap_apply N ((divideHalf_memLp N f).toLp _),
    (divideHalf_memLp N f).coeFn_toLp.filter_mono (weighted_null_sets N).ae_le] with z hout hin
  rw [hout]
  change (halfDensity N z : ℂ) * ((divideHalf_memLp N f).toLp (divideHalf N f)) z = f z
  rw [hin]
  exact congrFun (multiply_divideHalf N f) z

/-- The positive source half density gives an actual complex Hilbert equivalence. -/
def halfDensityEquiv (N : ℕ) : SectorHilbert N ≃ₗᵢ[ℂ] BaseHilbert :=
  LinearIsometryEquiv.ofSurjective (halfDensityMap N) (halfDensityMap_surjective N)

abbrev FlatFockHilbert := PiLp 2 (fun _ : Occupation => BaseHilbert)

/-- Every original occupation word is retained, with its generated number weight. -/
def fockHalfDensityEquiv : FockHilbert ≃ₗᵢ[ℂ] FlatFockHilbert :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun word => halfDensityEquiv word.card)

theorem fockHalfDensityEquiv_apply (f : FockHilbert) (word : Occupation) :
    (fockHalfDensityEquiv f) word =ᵐ[chartMeasure] multiplyHalf word.card (f word) :=
  halfDensityMap_apply word.card (f word)

theorem source_halfDensity_one (N : ℕ) : halfDensity N sourcePoint = 1 := by
  simp [halfDensity, source_weight_one]

end LowEnergy.SourceQuantumHalfDensityHilbert
