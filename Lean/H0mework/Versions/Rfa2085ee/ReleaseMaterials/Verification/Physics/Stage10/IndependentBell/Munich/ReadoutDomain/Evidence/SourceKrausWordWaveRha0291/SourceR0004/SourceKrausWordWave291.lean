import H0mework.Versions.R01f114f0.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceWordMassSimplexRha02890290.SourceR0010.SourceKrausWordSimplex290
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The complete source word expansion generates a joint L² vector.

No wave function, measure, mass or normalization witness enters the source.
All finite marked words and all their real time coordinates are retained in a
disjoint carrier. The original atomic vector is acted on by the same exact
word amplitudes. The full-word norm theorem then creates the L² element and
its isometric source map. Born measure is a readout of this generated vector.

The record carrier still contains every Kraus channel. The physical emission
consumer preserves natural channels coherently, translates their two flights,
applies the source passive optical isometry, and only then restricts arrived
and pending fields or traces the capture/ion environment.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology ENNReal

namespace SourceKrausWordWave291

open SourceKrausSurvival285 SourceHiddenWordFlow286
open SourceKrausWordMass289 SourceKrausWordSimplex290

universe u v

abbrev WordChart (ι : Type v) := Σ n : ℕ, Fin n → ι
abbrev WordHistory (ι : Type v) := Σ chart : WordChart ι, Fin chart.1 → ℝ

private theorem chart_inclusion_measurable {ι : Type v} (chart : WordChart ι) :
    Measurable (fun times : Fin chart.1 → ℝ => (⟨chart,times⟩ : WordHistory ι)) :=
  Measurable.of_le_map (iInf_le _ chart)

private theorem measurable_from_charts {ι : Type v} {Y : Type*} [MeasurableSpace Y]
    (f : WordHistory ι → Y) (charts : ∀ chart, Measurable (fun times => f ⟨chart,times⟩)) :
    Measurable f :=
  Measurable.of_comap_le <| le_iInf fun chart =>
    MeasurableSpace.comap_le_iff_le_map.2 <| by
      simpa only [MeasurableSpace.map_comp, Function.comp_def] using
        (charts chart).le_map

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
variable {ι : Type v} [Fintype ι]
variable (source : RawKrausWindow E ι)

def baseMeasure (start : ℝ) : Measure (WordHistory ι) :=
  Measure.sum fun chart : WordChart ι =>
    (volume.restrict (simplex start source.right chart.1)).map (fun times : Fin chart.1 → ℝ => (⟨chart,times⟩ : WordHistory ι))

def wordFunction (start : ℝ) (x : E) (history : WordHistory ι) : E :=
  SourceKrausWordSimplex290.amplitude source history.1.1 start history.1.2 history.2 x

def bornDensity (start : ℝ) (x : E) (history : WordHistory ι) : ℝ≥0∞ :=
  ENNReal.ofReal (‖wordFunction source start x history‖^2)

theorem bornDensity_measurable (start : ℝ) (x : E) :
    Measurable (bornDensity source start x) := by
  apply measurable_from_charts
  intro chart
  exact (ENNReal.continuous_ofReal.comp
    (((SourceKrausWordSimplex290.amplitude_continuous source chart.1 start chart.2).clm_apply (g := fun _ => x)
      continuous_const).norm.pow 2)).measurable

/-- The base measure comes from words and volume; its generated Born density has exact mass. -/
theorem lintegral_bornDensity (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (x : E) :
    (∫⁻ history, bornDensity source start x history ∂baseMeasure source start) =
      ENNReal.ofReal (‖x‖^2) := by
  classical
  rw [baseMeasure, lintegral_sum_measure]
  simp_rw [lintegral_map (bornDensity_measurable source start x)
    (chart_inclusion_measurable _)]
  rw [ENNReal.tsum_sigma' (β := fun n : ℕ => Fin n → ι)
    (fun chart => ∫⁻ times in simplex start source.right chart.1,
      bornDensity source start x ⟨chart,times⟩)]
  have each (n : ℕ) :
      (∑' word : Fin n → ι, ∫⁻ times in simplex start source.right n,
        bornDensity source start x ⟨⟨n,word⟩,times⟩) =
        ENNReal.ofReal (wordMass source n start x) := by
    rw [tsum_fintype, wordMass_eq_simplex source n start inside x,
      ENNReal.ofReal_sum_of_nonneg (fun word _ => integral_nonneg fun _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro word _
    have integrable := simplex_integrable n start source.right _
      (((SourceKrausWordSimplex290.amplitude_continuous source n start word).clm_apply (g := fun _ => x)
        continuous_const).norm.pow 2)
    exact (ofReal_integral_eq_lintegral_ofReal integrable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  simp_rw [each]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => wordMass_nonnegative source n start inside x)
    (wordMass_hasSum_norm source start inside x).summable,
    (wordMass_hasSum_norm source start inside x).tsum_eq]

def bornMeasure (start : ℝ) (x : E) : Measure (WordHistory ι) :=
  (baseMeasure source start).withDensity (bornDensity source start x)

theorem bornMeasure_univ (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    bornMeasure source start x univ = ENNReal.ofReal (‖x‖^2) := by
  rw [bornMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_bornDensity source start inside x

theorem bornMeasure_finite (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    IsFiniteMeasure (bornMeasure source start x) :=
  ⟨by rw [bornMeasure_univ source start inside x]; exact ENNReal.ofReal_lt_top⟩

theorem bornMeasure_probability (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (x : E) (unit : ‖x‖ = 1) : IsProbabilityMeasure (bornMeasure source start x) :=
  ⟨by rw [bornMeasure_univ source start inside x,unit]; norm_num⟩

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
theorem wordFunction_measurable (start : ℝ) (x : E) :
    Measurable (wordFunction source start x) := by
  apply measurable_from_charts
  intro chart
  exact ((SourceKrausWordSimplex290.amplitude_continuous source chart.1 start chart.2).clm_apply (g := fun _ => x)
    continuous_const).measurable

omit [SecondCountableTopology E] in
theorem wordFunction_squared_integrable (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (x : E) :
    Integrable (fun history => ‖wordFunction source start x history‖^2) (baseMeasure source start) := by
  refine ⟨((wordFunction_measurable source start x).norm.pow_const 2).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact (lintegral_bornDensity source start inside x).trans_lt ENNReal.ofReal_lt_top

theorem wordFunction_memLp (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    MemLp (wordFunction source start x) 2 (baseMeasure source start) :=
  (memLp_two_iff_integrable_sq_norm
    (wordFunction_measurable source start x).aestronglyMeasurable).mpr
      (wordFunction_squared_integrable source start inside x)

def wave (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    Lp E 2 (baseMeasure source start) :=
  (wordFunction_memLp source start inside x).toLp (wordFunction source start x)

theorem wave_ae (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    wave source start inside x =ᵐ[baseMeasure source start] wordFunction source start x :=
  (wordFunction_memLp source start inside x).coeFn_toLp

omit [CompleteSpace E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
private theorem l2_squared_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : Lp E 2 μ) : (∫ x, ‖v x‖^2 ∂μ) = ‖v‖^2 := by
  calc
    _ = ∫ x, (inner ℂ (v x) (v x)).re ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall fun x => (inner_self_eq_norm_sq (𝕜 := ℂ) (v x)).symm)
    _ = (∫ x, inner ℂ (v x) (v x) ∂μ).re :=
      Complex.reCLM.integral_comp_comm (L2.integrable_inner v v)
    _ = ‖v‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) v

theorem wave_norm (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    ‖wave source start inside x‖ = ‖x‖ := by
  have original := ofReal_integral_eq_lintegral_ofReal
    (wordFunction_squared_integrable source start inside x)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have mass : (∫ history, ‖wordFunction source start x history‖^2
      ∂baseMeasure source start) = ‖x‖^2 :=
    (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).mp
      (original.trans (lintegral_bornDensity source start inside x))
  have same : (∫ history, ‖wave source start inside x history‖^2 ∂baseMeasure source start) =
      ∫ history, ‖wordFunction source start x history‖^2 ∂baseMeasure source start :=
    integral_congr_ae ((wave_ae source start inside x).mono fun _ h =>
      congrArg (fun z : E => ‖z‖^2) h)
  rw [l2_squared_integral] at same
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (same.trans mass)

theorem wave_add (start : ℝ) (inside : start ∈ Icc source.left source.right) (x y : E) :
    wave source start inside (x+y) = wave source start inside x + wave source start inside y := by
  apply Lp.ext
  filter_upwards [wave_ae source start inside (x+y), wave_ae source start inside x,
    wave_ae source start inside y, Lp.coeFn_add (wave source start inside x)
      (wave source start inside y)] with history hxy hx hy hadd
  simp only [hxy,hadd,hx,hy,wordFunction,map_add,Pi.add_apply]

theorem wave_smul (start : ℝ) (inside : start ∈ Icc source.left source.right) (c : ℂ) (x : E) :
    wave source start inside (c • x) = c • wave source start inside x := by
  apply Lp.ext
  filter_upwards [wave_ae source start inside (c • x), wave_ae source start inside x,
    Lp.coeFn_smul c (wave source start inside x)] with history hcx hx hsmul
  simp only [hcx,hsmul,hx,wordFunction,map_smul,Pi.smul_apply]

/-- One source-generated joint wave retains the entire atomic/field norm. -/
def sourceIsometry (start : ℝ) (inside : start ∈ Icc source.left source.right) :
    E →ₗᵢ[ℂ] Lp E 2 (baseMeasure source start) where
  toFun := wave source start inside
  map_add' := wave_add source start inside
  map_smul' := wave_smul source start inside
  norm_map' := wave_norm source start inside

end SourceKrausWordWave291
