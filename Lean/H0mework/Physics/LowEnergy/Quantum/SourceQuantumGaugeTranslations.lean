import H0mework.Physics.LowEnergy.Quantum.SourceQuantumFockGaugeHilbert
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Prod
/-! Native electric translations on the original common source Hilbert space.
Gauge is the already generated native36-dimensional carrier. Its original
inner-product volume and number-weighted chart measure are preserved by
A -> A+h. The actual full504 gauge action intertwines the translations with
its original native adjoint action; the CAR inverse factor is unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceQuantumGaugeTranslations
open MeasureTheory Set Filter
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumResidualFlow SourceQuantumResidualFlowMeasure SourceQuantumResidualChartFlow
open SourceQuantumFockGauge SourceQuantumFockGaugeHilbert SourceQuantumHalfDensityHilbert
open scoped ENNReal Topology ContDiff BigOperators

def translate (h : Gauge) (z : Configuration) : Configuration := (z.1, z.2.1, z.2.2 + h)

theorem translate_chart_iff (h : Gauge) (z : Configuration) : translate h z ∈ chart ↔ z ∈ chart := Iff.rfl

def translateHomeomorph (h : Gauge) : Configuration ≃ₜ Configuration where
  toFun := translate h
  invFun := translate (-h)
  left_inv z := by simp [translate]
  right_inv z := by simp [translate]
  continuous_toFun := by unfold translate; fun_prop
  continuous_invFun := by unfold translate; fun_prop

theorem translate_measurePreserving (h : Gauge) :
    MeasurePreserving (translate h) configurationMeasure configurationMeasure := by
  have hg : MeasurePreserving (fun A : Gauge => A + h) gaugeMeasure gaugeMeasure := by
    unfold gaugeMeasure
    exact measurePreserving_add_right _ h
  let : IsLocallyFiniteMeasure SourceQuantumScalarHilbert.sliceMeasure := by
    unfold SourceQuantumScalarHilbert.sliceMeasure
    infer_instance
  exact (MeasurePreserving.id coframeMeasure).prod
    ((MeasurePreserving.id SourceQuantumScalarHilbert.sliceMeasure).prod hg)

def chartTranslation (h : Gauge) (z : chart) : chart := ⟨translate h z, z.property⟩

theorem chartTranslation_add (h k : Gauge) (z : chart) :
    chartTranslation h (chartTranslation k z) = chartTranslation (h+k) z := by
  apply Subtype.ext
  exact congrArg (fun A : Gauge => (z.val.1, z.val.2.1, A))
    (show (z.val.2.2 + k) + h = z.val.2.2 + (h+k) by abel)

theorem chartTranslation_zero (z : chart) : chartTranslation 0 z = z := by
  apply Subtype.ext
  simp [chartTranslation, translate]

def chartTranslationHomeomorph (h : Gauge) : chart ≃ₜ chart where
  toFun := chartTranslation h
  invFun := chartTranslation (-h)
  left_inv z := by rw [chartTranslation_add, neg_add_cancel, chartTranslation_zero]
  right_inv z := by rw [chartTranslation_add, add_neg_cancel, chartTranslation_zero]
  continuous_toFun := ((translateHomeomorph h).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((translateHomeomorph (-h)).continuous.comp continuous_subtype_val).subtype_mk _

theorem chartTranslation_measurePreserving (h : Gauge) :
    MeasurePreserving (chartTranslation h) chartMeasure chartMeasure := by
  have hm : Measurable (chartTranslation h) := (chartTranslationHomeomorph h).continuous.measurable
  have hs : MeasurePreserving (Subtype.val : chart → Configuration) chartMeasure
      (configurationMeasure.restrict chart) := measurePreserving_subtype_coe chart.isOpen.measurableSet
  have hr := (translate_measurePreserving h).restrict_preimage chart.isOpen.measurableSet
  have hp : (translate h) ⁻¹' (chart : Set Configuration) = chart := Set.ext (translate_chart_iff h)
  rw [hp] at hr
  refine ⟨hm, ?_⟩
  apply (MeasurableEmbedding.subtype_coe chart.isOpen.measurableSet).map_injective
  calc
    Measure.map (Subtype.val : chart → Configuration) (Measure.map (chartTranslation h) chartMeasure) =
        Measure.map ((Subtype.val : chart → Configuration) ∘ chartTranslation h) chartMeasure :=
      Measure.map_map measurable_subtype_coe hm
    _ = Measure.map ((translate h) ∘ (Subtype.val : chart → Configuration)) chartMeasure := rfl
    _ = configurationMeasure.restrict chart := (hr.comp hs).map_eq
    _ = Measure.map (Subtype.val : chart → Configuration) chartMeasure := hs.map_eq.symm

theorem chartTranslation_numberWeight (N : ℕ) (h : Gauge) (z : chart) :
    numberWeight N (chartTranslation h z) = numberWeight N z := rfl

theorem chartTranslation_numberMeasurePreserving (N : ℕ) (h : Gauge) :
    MeasurePreserving (chartTranslation h) (numberMeasure N) (numberMeasure N) := by
  have hm : Measurable (chartTranslation h) := (chartTranslationHomeomorph h).continuous.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, numberMeasure, withDensity_apply _ (hm hs), withDensity_apply _ hs]
  have he := (chartTranslation_measurePreserving h).setLIntegral_comp_preimage hs
    (numberWeight_continuous N).measurable.ennreal_ofReal
  simpa only [chartTranslation_numberWeight] using he

def sectorTranslation (N : ℕ) (h : Gauge) : SectorHilbert N →ₗᵢ[ℂ] SectorHilbert N :=
  Lp.compMeasurePreservingₗᵢ ℂ (chartTranslation h) (chartTranslation_numberMeasurePreserving N h)

theorem sectorTranslation_add (N : ℕ) (h k : Gauge) (f : SectorHilbert N) :
    sectorTranslation N h (sectorTranslation N k f) = sectorTranslation N (h+k) f := by
  change Lp.compMeasurePreserving (chartTranslation h) (chartTranslation_numberMeasurePreserving N h)
    (Lp.compMeasurePreserving (chartTranslation k) (chartTranslation_numberMeasurePreserving N k) f) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : chartTranslation k ∘ chartTranslation h = chartTranslation (h+k) := by
    funext z
    rw [Function.comp_apply, chartTranslation_add, add_comm]
  simp only [he]
  rfl

theorem sectorTranslation_zero (N : ℕ) (f : SectorHilbert N) : sectorTranslation N 0 f = f := by
  change Lp.compMeasurePreserving (chartTranslation 0) (chartTranslation_numberMeasurePreserving N 0) f = f
  have he : chartTranslation 0 = id := funext chartTranslation_zero
  simp only [he, Lp.compMeasurePreserving_id_apply]

def sectorTranslationUnitary (N : ℕ) (h : Gauge) : SectorHilbert N ≃ₗᵢ[ℂ] SectorHilbert N where
  toFun := sectorTranslation N h
  invFun := sectorTranslation N (-h)
  left_inv f := by rw [sectorTranslation_add, neg_add_cancel, sectorTranslation_zero]
  right_inv f := by rw [sectorTranslation_add, add_neg_cancel, sectorTranslation_zero]
  map_add' := (sectorTranslation N h).map_add
  map_smul' := (sectorTranslation N h).map_smul
  norm_map' := (sectorTranslation N h).norm_map

theorem sectorTranslation_apply_ae (N : ℕ) (h : Gauge) (f : SectorHilbert N) :
    sectorTranslationUnitary N h f =ᵐ[numberMeasure N] fun z => f (chartTranslation h z) :=
  Lp.coeFn_compMeasurePreserving f (chartTranslation_numberMeasurePreserving N h)

theorem sectorTranslation_testDomain (N : ℕ) (h : Gauge) (f : SectorHilbert N)
    (hf : f ∈ testDomain N) : sectorTranslationUnitary N h f ∈ testDomain N := by
  rcases hf with ⟨g, hfg, hgk, hgc, hgs⟩
  refine ⟨g ∘ translate h, ?_, ?_, ?_, ?_⟩
  · exact (sectorTranslation_apply_ae N h f).trans
      ((chartTranslation_numberMeasurePreserving N h).quasiMeasurePreserving.ae_eq hfg)
  · exact hgk.comp_homeomorph (translateHomeomorph h)
  · apply hgc.comp
    unfold translate
    fun_prop
  · intro z hz
    have he : translate h z ∈ tsupport g := tsupport_comp_subset_preimage g (translateHomeomorph h).continuous hz
    exact (translate_chart_iff h z).mp (hgs he)

theorem sectorTranslation_testDomain_iff (N : ℕ) (h : Gauge) (f : SectorHilbert N) :
    sectorTranslationUnitary N h f ∈ testDomain N ↔ f ∈ testDomain N := by
  constructor
  · intro hf
    have hi := sectorTranslation_testDomain N (-h) (sectorTranslationUnitary N h f) hf
    change sectorTranslation N (-h) (sectorTranslation N h f) ∈ testDomain N at hi
    simpa only [sectorTranslation_add, neg_add_cancel, sectorTranslation_zero] using hi
  · exact sectorTranslation_testDomain N h f

def fockTranslation (h : Gauge) : FockHilbert ≃ₗᵢ[ℂ] FockHilbert :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun word => sectorTranslationUnitary word.card h)

theorem fockTranslation_add (h k : Gauge) (f : FockHilbert) :
    fockTranslation h (fockTranslation k f) = fockTranslation (h+k) f := by
  apply PiLp.ext
  intro word
  exact sectorTranslation_add word.card h k (f word)

theorem fockTranslation_zero (f : FockHilbert) : fockTranslation 0 f = f := by
  apply PiLp.ext
  intro word
  exact sectorTranslation_zero word.card (f word)

theorem fockTranslation_testDomain_iff (h : Gauge) (f : FockHilbert) :
    fockTranslation h f ∈ fockTestDomain ↔ f ∈ fockTestDomain := by
  change (∀ word : Occupation, sectorTranslationUnitary word.card h (f word) ∈ testDomain word.card) ↔
    ∀ word : Occupation, f word ∈ testDomain word.card
  simp only [sectorTranslation_testDomain_iff]


def chartTranslationMap (h : Gauge) : C(chart, chart) :=
  ⟨chartTranslation h, (chartTranslationHomeomorph h).continuous⟩

theorem chartTranslationMap_continuous : Continuous chartTranslationMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : Continuous (fun z : Gauge × chart => translate z.1 z.2) := by
    unfold translate
    fun_prop
  exact h.subtype_mk _

theorem sectorTranslation_stronglyContinuous (N : ℕ) (f : SectorHilbert N) :
    Continuous (fun h : Gauge => sectorTranslationUnitary N h f) := by
  change Continuous (fun h : Gauge => Lp.compMeasurePreserving
    (chartTranslationMap h) (chartTranslation_numberMeasurePreserving N h) f)
  exact continuous_const.compMeasurePreservingLp chartTranslationMap_continuous
    (chartTranslation_numberMeasurePreserving N) (by norm_num)


theorem fockTranslation_stronglyContinuous (f : FockHilbert) :
    Continuous (fun h : Gauge => fockTranslation h f) := by
  exact (PiLp.continuous_toLp 2 (fun word : Occupation => SectorHilbert word.card)).comp
    (continuous_pi (fun word => sectorTranslation_stronglyContinuous word.card (f word)))

theorem chartTranslation_covariant (a : stabilizer) (h : Gauge) (z : chart) :
    chartFlow a (chartTranslation h z) =
      chartTranslation (gaugePartEquiv a h) (chartFlow a z) := by
  apply Subtype.ext
  change flow a (translate h z) = translate (gaugePartEquiv a h) (flow a z)
  rw [flow_product]
  simp [translate, map_add]

theorem fockTranslation_apply_ae (h : Gauge) (f : FockHilbert) (word : Occupation) :
    fockTranslation h f word =ᵐ[chartMeasure] fun z => f word (chartTranslation h z) :=
  (sectorTranslation_apply_ae word.card h (f word)).filter_mono (weighted_null_sets word.card).ae_le

theorem fullGauge_covariant (a : stabilizer) (h : Gauge) (f : FockHilbert) :
    fockTranslation h (fullGaugeUnitary a f) =
      fullGaugeUnitary a (fockTranslation (gaugePartEquiv a h) f) := by
  apply PiLp.ext
  intro word
  apply Lp.ext
  have hl := fockTranslation_apply_ae h (fullGaugeUnitary a f) word
  have hll := (chartTranslation_measurePreserving h).quasiMeasurePreserving.ae_eq
    (fullGaugeUnitary_apply_ae a f word)
  have hr := fullGaugeUnitary_apply_ae a (fockTranslation (gaugePartEquiv a h) f) word
  have hall : ∀ᵐ z ∂chartMeasure, ∀ input : Occupation,
      fockTranslation (gaugePartEquiv a h) f input (chartFlow a z) =
        f input (chartTranslation (gaugePartEquiv a h) (chartFlow a z)) :=
    ae_all_iff.mpr (fun input => (chartFlow_measurePreserving a).quasiMeasurePreserving.ae_eq
      (fockTranslation_apply_ae (gaugePartEquiv a h) f input))
  have both : (fun z => fockTranslation h (fullGaugeUnitary a f) word z) =ᵐ[chartMeasure]
      fun z => fullGaugeUnitary a (fockTranslation (gaugePartEquiv a h) f) word z := by
    filter_upwards [hl, hll, hr, hall] with z hl hll hr hi
    simp only [Function.comp_apply] at hll
    rw [hl, hll, hr]
    apply Finset.sum_congr rfl
    intro input _
    rw [hi input, chartTranslation_covariant]
  have hm : numberMeasure word.card ≪ chartMeasure := withDensity_absolutelyContinuous _ _
  exact both.filter_mono hm.ae_le

theorem fullGauge_conjugates_translation (a : stabilizer) (h : Gauge) (f : FockHilbert) :
    (fullGaugeUnitary a).symm (fockTranslation h (fullGaugeUnitary a f)) =
      fockTranslation (gaugePartEquiv a h) f := by
  rw [fullGauge_covariant, LinearIsometryEquiv.symm_apply_apply]


def gaugeDirection (h : Gauge) : Configuration := (0, 0, h)

/-- The canonical electric differential acts on the original ambient smooth representative. -/
def electricDerivative (h : Gauge) (g : Configuration → ℂ) (z : Configuration) : ℂ :=
  -Complex.I * (fderiv ℝ g z) (gaugeDirection h)

theorem smooth_translation_derivative (h : Gauge) (g : Configuration → ℂ)
    (hg : ContDiff ℝ ∞ g) (z : Configuration) (t : ℝ) :
    HasDerivAt (fun r : ℝ => g (translate (r • h) z))
      ((fderiv ℝ g (translate (t • h) z)) (gaugeDirection h)) t := by
  have line : HasDerivAt (fun r : ℝ => translate (r • h) z) (gaugeDirection h) t := by
    have ha := ((hasDerivAt_id t).smul_const h).const_add z.2.2
    have hp := (hasDerivAt_const t z.1).prodMk ((hasDerivAt_const t z.2.1).prodMk ha)
    simpa only [translate, gaugeDirection, id_eq, one_smul] using hp
  exact (((hg.differentiable (by simp)) (translate (t • h) z)).hasFDerivAt).comp_hasDerivAt t line

theorem electricDerivative_translation (h : Gauge) (g : Configuration → ℂ)
    (hg : ContDiff ℝ ∞ g) (z : Configuration) :
    -Complex.I * deriv (fun t : ℝ => g (translate (t • h) z)) 0 = electricDerivative h g z := by
  rw [(smooth_translation_derivative h g hg z 0).deriv]
  simp [electricDerivative, translate]

end LowEnergy.SourceQuantumGaugeTranslations
