import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeMeasure

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationMeasure
open MeasureTheory MeasureTheory.Measure Filter
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert (physicalChart SectorHilbert)
open PreparationScalarCoordinates CanonicalPreparationCutoff
open scoped ENNReal RealInnerProductSpace Distributions

-- The literal dz100 measure is restricted through the original actual chart.
def rawChartMeasure : Measure physicalChart :=
  flatMeasure.comap (fun z : physicalChart => fullCoordinates z.val)

theorem original_chart_measure : GaussHistoryHilbert.chartMeasure=
    ENNReal.ofReal nativeVolumeFactor • rawChartMeasure := by
  rw [GaussHistoryHilbert.chartMeasure,← native_measure_return,nativeFlatMeasure_eq,
    Measure.comap_smul,Measure.comap_smul]
  change ENNReal.ofReal nativeVolumeFactor •
    ((flatMeasure.comap fullCoordinates).comap Subtype.val)=_
  congr 1
  exact Measure.comap_comap
    (fun s hs => physicalChart.isOpenEmbedding'.measurableEmbedding.measurableSet_image.mpr hs)
    fullCoordinates.injective
    (fun s hs => fullCoordinates.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs) flatMeasure

def rawNumberWeight (N : ℕ) (z : physicalChart) : ℝ :=
  nativeVolumeFactor*GaussHistoryHilbert.numberWeight N z

theorem rawNumberWeight_pos (N : ℕ) (z : physicalChart) : 0<rawNumberWeight N z :=
  mul_pos nativeVolumeFactor_pos (GaussHistoryHilbert.numberWeight_pos N z)

theorem rawNumberWeight_continuous (N : ℕ) : Continuous (rawNumberWeight N) :=
  continuous_const.mul (GaussHistoryHilbert.numberWeight_continuous N)

theorem original_number_measure (N : ℕ) : GaussHistoryHilbert.numberMeasure N=
    rawChartMeasure.withDensity (fun z => ENNReal.ofReal (rawNumberWeight N z)) := by
  rw [GaussHistoryHilbert.numberMeasure,original_chart_measure,withDensity_smul_measure]
  have weight : (fun z : physicalChart => ENNReal.ofReal (rawNumberWeight N z))=
      ENNReal.ofReal nativeVolumeFactor • (fun z => ENNReal.ofReal (GaussHistoryHilbert.numberWeight N z)) := by
    ext z
    rw [rawNumberWeight,ENNReal.ofReal_mul nativeVolumeFactor_pos.le]
    rfl
  rw [weight,withDensity_smul' _ _ ENNReal.ofReal_ne_top]

theorem raw_density_readback (N : ℕ) (z : physicalChart) :
    rawNumberWeight N z=(1024*Real.sqrt 3)*GaussDensityCore.density N z.val := rfl

def rawHalfFactor (N : ℕ) (z : physicalChart) : ℝ :=
  Real.sqrt nativeVolumeFactor*GaussHalfDensity.halfDensity N z

theorem rawHalfFactor_pos (N : ℕ) (z : physicalChart) : 0<rawHalfFactor N z :=
  mul_pos (Real.sqrt_pos.mpr nativeVolumeFactor_pos) (GaussHalfDensity.halfDensity_pos N z)

theorem rawHalfFactor_continuous (N : ℕ) : Continuous (rawHalfFactor N) :=
  continuous_const.mul (GaussHalfDensity.halfDensity_continuous N)

theorem rawHalfFactor_sq (N : ℕ) (z : physicalChart) :
    rawHalfFactor N z^2=rawNumberWeight N z := by
  rw [rawHalfFactor,mul_pow,Real.sq_sqrt nativeVolumeFactor_pos.le,
    GaussHalfDensity.halfDensity_sq]
  rfl

theorem rawHalfFactor_enorm_sq (N : ℕ) (z : physicalChart) :
    ‖(rawHalfFactor N z : ℂ)‖ₑ ^ (2 : ℝ)=ENNReal.ofReal (rawNumberWeight N z) := by
  rw [← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (rawHalfFactor_pos N z),
    ENNReal.rpow_two,← ENNReal.ofReal_pow (rawHalfFactor_pos N z).le,rawHalfFactor_sq]

def rawMultiplyHalf (N : ℕ) (f : physicalChart → ℂ) : physicalChart → ℂ :=
  fun z => (rawHalfFactor N z : ℂ)*f z

theorem raw_weight_measurable (N : ℕ) : Measurable
    (fun z : physicalChart => ENNReal.ofReal (rawNumberWeight N z)) :=
  (rawNumberWeight_continuous N).measurable.ennreal_ofReal

theorem raw_weighted_null_sets (N : ℕ) : rawChartMeasure ≪ GaussHistoryHilbert.numberMeasure N := by
  rw [original_number_measure]
  exact withDensity_absolutelyContinuous' (raw_weight_measurable N).aemeasurable
    (Eventually.of_forall fun z => (ENNReal.ofReal_pos.mpr (rawNumberWeight_pos N z)).ne')

theorem raw_native_null_sets : rawChartMeasure ≪ GaussHistoryHilbert.chartMeasure := by
  rw [original_chart_measure]
  exact Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.mpr nativeVolumeFactor_pos).ne'

theorem eLpNorm_rawMultiplyHalf (N : ℕ) (f : physicalChart → ℂ) :
    eLpNorm (rawMultiplyHalf N f) 2 rawChartMeasure=
      eLpNorm f 2 (GaussHistoryHilbert.numberMeasure N) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [original_number_measure,lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (raw_weight_measurable N) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  apply lintegral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [rawMultiplyHalf,enorm_mul,Pi.mul_apply,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ)≤2),rawHalfFactor_enorm_sq]

abbrev RawBaseHilbert := Lp ℂ 2 rawChartMeasure

theorem rawMultiplyHalf_memLp (N : ℕ) (f : SectorHilbert N) :
    MemLp (rawMultiplyHalf N f) 2 rawChartMeasure := by
  constructor
  · exact (Complex.continuous_ofReal.comp (rawHalfFactor_continuous N)).aestronglyMeasurable.mul
      ((Lp.memLp f).aestronglyMeasurable.mono_ac (raw_weighted_null_sets N))
  · rw [eLpNorm_rawMultiplyHalf]
    exact (Lp.memLp f).2

def rawHalfDensityMap (N : ℕ) : SectorHilbert N →ₗᵢ[ℂ] RawBaseHilbert where
  toFun f := (rawMultiplyHalf_memLp N f).toLp (rawMultiplyHalf N f)
  map_add' f g := by
    ext1
    filter_upwards [(rawMultiplyHalf_memLp N (f+g)).coeFn_toLp,
      (rawMultiplyHalf_memLp N f).coeFn_toLp,(rawMultiplyHalf_memLp N g).coeFn_toLp,
      Lp.coeFn_add ((rawMultiplyHalf_memLp N f).toLp _) ((rawMultiplyHalf_memLp N g).toLp _),
      (Lp.coeFn_add f g).filter_mono (raw_weighted_null_sets N).ae_le] with z hadd hf hg hout hin
    rw [hadd,hout]
    simp only [Pi.add_apply] at *
    rw [hf,hg]
    change (rawHalfFactor N z : ℂ)*(f+g) z=(rawHalfFactor N z : ℂ)*f z+(rawHalfFactor N z : ℂ)*g z
    rw [hin,mul_add]
  map_smul' c f := by
    ext1
    filter_upwards [(rawMultiplyHalf_memLp N (c • f)).coeFn_toLp,
      (rawMultiplyHalf_memLp N f).coeFn_toLp,
      Lp.coeFn_smul c ((rawMultiplyHalf_memLp N f).toLp _),
      (Lp.coeFn_smul c f).filter_mono (raw_weighted_null_sets N).ae_le] with z hc hf hout hin
    simp only [RingHom.id_apply]
    rw [hc,hout]
    simp only [Pi.smul_apply] at *
    rw [hf]
    simp [rawMultiplyHalf,hin,mul_left_comm]
  norm_map' f := by
    change ‖(rawMultiplyHalf_memLp N f).toLp (rawMultiplyHalf N f)‖=‖f‖
    simp only [Lp.norm_def]
    rw [eLpNorm_congr_ae (rawMultiplyHalf_memLp N f).coeFn_toLp,eLpNorm_rawMultiplyHalf]

theorem rawHalfDensityMap_apply (N : ℕ) (f : SectorHilbert N) :
    rawHalfDensityMap N f=ᵐ[rawChartMeasure] rawMultiplyHalf N f :=
  (rawMultiplyHalf_memLp N f).coeFn_toLp

def rawDivideHalf (N : ℕ) (f : physicalChart → ℂ) : physicalChart → ℂ :=
  fun z => (rawHalfFactor N z : ℂ)⁻¹*f z

theorem raw_multiply_divideHalf (N : ℕ) (f : physicalChart → ℂ) :
    rawMultiplyHalf N (rawDivideHalf N f)=f := by
  ext z
  have hn : (rawHalfFactor N z : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (rawHalfFactor_pos N z).ne'
  simp [rawMultiplyHalf,rawDivideHalf,hn]

theorem rawDivideHalf_memLp (N : ℕ) (f : RawBaseHilbert) :
    MemLp (rawDivideHalf N f) 2 (GaussHistoryHilbert.numberMeasure N) := by
  constructor
  · apply (Complex.continuous_ofReal.comp (rawHalfFactor_continuous N)).measurable.inv.aestronglyMeasurable.mul
    apply (Lp.memLp f).aestronglyMeasurable.mono_ac
    rw [original_number_measure]
    exact withDensity_absolutelyContinuous rawChartMeasure _
  · rw [← eLpNorm_rawMultiplyHalf,raw_multiply_divideHalf]
    exact (Lp.memLp f).2

theorem rawHalfDensityMap_surjective (N : ℕ) : Function.Surjective (rawHalfDensityMap N) := by
  intro f
  refine ⟨(rawDivideHalf_memLp N f).toLp (rawDivideHalf N f),?_⟩
  ext1
  filter_upwards [rawHalfDensityMap_apply N ((rawDivideHalf_memLp N f).toLp _),
    (rawDivideHalf_memLp N f).coeFn_toLp.filter_mono (raw_weighted_null_sets N).ae_le] with z hout hin
  rw [hout]
  change (rawHalfFactor N z : ℂ)*((rawDivideHalf_memLp N f).toLp (rawDivideHalf N f)) z=f z
  rw [hin]
  exact congrFun (raw_multiply_divideHalf N f) z

def rawHalfDensityEquiv (N : ℕ) : SectorHilbert N ≃ₗᵢ[ℂ] RawBaseHilbert :=
  LinearIsometryEquiv.ofSurjective (rawHalfDensityMap N) (rawHalfDensityMap_surjective N)

theorem original_halfDensity_readback (N : ℕ) (f : SectorHilbert N) :
    rawHalfDensityEquiv N f=ᵐ[rawChartMeasure]
      (fun z => (Real.sqrt (1024*Real.sqrt 3) : ℂ)*GaussHalfDensity.halfDensityEquiv N f z) := by
  filter_upwards [rawHalfDensityMap_apply N f,
    (GaussHalfDensity.halfDensityMap_apply N f).filter_mono raw_native_null_sets.ae_le] with z hr hn
  change rawHalfDensityMap N f z=(Real.sqrt nativeVolumeFactor : ℂ)*GaussHalfDensity.halfDensityMap N f z
  rw [hr,hn]
  simp [rawMultiplyHalf,rawHalfFactor,GaussHalfDensity.multiplyHalf,mul_assoc]

theorem original_core_raw_readback (N : ℕ) (f : 𝓓(physicalChart,ℂ)) :
    rawHalfDensityEquiv N (GaussCoreHilbert.scalarLp N f)=ᵐ[rawChartMeasure]
      (fun z => (rawHalfFactor N z : ℂ)*f z) := by
  filter_upwards [rawHalfDensityMap_apply N (GaussCoreHilbert.scalarLp N f),
    (GaussCoreHilbert.scalarLp_ae N f).filter_mono (raw_weighted_null_sets N).ae_le] with z hr hc
  change rawHalfDensityMap N (GaussCoreHilbert.scalarLp N f) z = _
  rw [hr]
  simp [rawMultiplyHalf,hc]

def flatChart : TopologicalSpace.Opens FlatConfiguration :=
  ⟨fullCoordinates.symm ⁻¹' (physicalChart : Set SourceCoordinateSlice),
    physicalChart.isOpen.preimage fullCoordinates.symm.continuous⟩

def chartCoordinates : physicalChart ≃ₜ flatChart :=
  fullCoordinates.toHomeomorph.subtype (fun z => by
    change z ∈ (physicalChart : Set SourceCoordinateSlice) ↔
      fullCoordinates.symm (fullCoordinates z) ∈ (physicalChart : Set SourceCoordinateSlice)
    rw [fullCoordinates.symm_apply_apply])

def flatChartMeasure : Measure flatChart := flatMeasure.comap Subtype.val

theorem raw_chart_coordinate_measure : rawChartMeasure=flatChartMeasure.comap chartCoordinates := by
  unfold flatChartMeasure
  rw [Measure.comap_comap
    (fun s hs => chartCoordinates.measurableEmbedding.measurableSet_image.mpr hs)
    (Subtype.val_injective : Function.Injective (Subtype.val : flatChart → FlatConfiguration))
    (fun s hs => flatChart.isOpenEmbedding'.measurableEmbedding.measurableSet_image.mpr hs)]
  rfl

theorem chartCoordinates_preserving : MeasurePreserving chartCoordinates rawChartMeasure flatChartMeasure where
  measurable := chartCoordinates.continuous.measurable
  map_eq := by
    rw [raw_chart_coordinate_measure,chartCoordinates.measurableEmbedding.map_comap]
    simp [chartCoordinates.surjective.range_eq]

theorem chartCoordinates_inverse_preserving :
    MeasurePreserving chartCoordinates.symm flatChartMeasure rawChartMeasure :=
  MeasurePreserving.symm chartCoordinates.toMeasurableEquiv chartCoordinates_preserving

abbrev FlatChartHilbert := Lp ℂ 2 flatChartMeasure

def rawCoordinateHilbertEquiv : RawBaseHilbert ≃ₗᵢ[ℂ] FlatChartHilbert :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ chartCoordinates.symm chartCoordinates_inverse_preserving) (by
      intro f
      refine ⟨Lp.compMeasurePreserving chartCoordinates chartCoordinates_preserving f,?_⟩
      change Lp.compMeasurePreserving chartCoordinates.symm chartCoordinates_inverse_preserving
        (Lp.compMeasurePreserving chartCoordinates chartCoordinates_preserving f)=f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have comp : (chartCoordinates ∘ chartCoordinates.symm)=id :=
        funext chartCoordinates.apply_symm_apply
      simp only [comp,Lp.compMeasurePreserving_id_apply])

def flatHalfDensityEquiv (N : ℕ) : SectorHilbert N ≃ₗᵢ[ℂ] FlatChartHilbert :=
  (rawHalfDensityEquiv N).trans rawCoordinateHilbertEquiv

theorem flat_core_readback (N : ℕ) (f : 𝓓(physicalChart,ℂ)) :
    flatHalfDensityEquiv N (GaussCoreHilbert.scalarLp N f)=ᵐ[flatChartMeasure]
      (fun z => (rawHalfFactor N (chartCoordinates.symm z) : ℂ)*f (fullCoordinates.symm z.val)) := by
  have original : rawHalfDensityEquiv N (GaussCoreHilbert.scalarLp N f)=ᵐ[
      flatChartMeasure.map chartCoordinates.symm]
      (fun z => (rawHalfFactor N z : ℂ)*f z) := by
    rw [chartCoordinates_inverse_preserving.map_eq]
    exact original_core_raw_readback N f
  have pulled : ∀ᵐ z ∂flatChartMeasure,
      rawHalfDensityEquiv N (GaussCoreHilbert.scalarLp N f) (chartCoordinates.symm z)=
        (rawHalfFactor N (chartCoordinates.symm z) : ℂ)*f (chartCoordinates.symm z) :=
    ae_of_ae_map chartCoordinates_inverse_preserving.measurable.aemeasurable
      original
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (rawHalfDensityEquiv N (GaussCoreHilbert.scalarLp N f)) chartCoordinates_inverse_preserving,pulled]
    with z hc hp
  change Lp.compMeasurePreserving chartCoordinates.symm chartCoordinates_inverse_preserving
    (rawHalfDensityEquiv N (GaussCoreHilbert.scalarLp N f)) z = _
  rw [hc]
  exact hp

end LowEnergy.PreparationMeasure
