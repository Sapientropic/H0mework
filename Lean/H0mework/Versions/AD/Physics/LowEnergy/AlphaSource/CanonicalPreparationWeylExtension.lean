import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationHalfDensityReadback
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylDomain
open PreparationMeasure CanonicalPreparationCutoff PreparationScalarCoordinates
open GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates
open MeasureTheory Filter Set
open scoped ENNReal Distributions
attribute [local instance] Classical.propDecidable

def flatZeroExtend (f : flatChart → ℂ) (z : FlatConfiguration) : ℂ :=
  if inside : z∈flatChart then f ⟨z,inside⟩ else 0

theorem flatZeroExtend_on_chart (f : flatChart → ℂ) (z : flatChart) :
    flatZeroExtend f z.val=f z := by simp [flatZeroExtend,z.property]

theorem flatZeroExtend_outside (f : flatChart → ℂ) (z : FlatConfiguration)
    (outside : z∉flatChart) : flatZeroExtend f z=0 := by simp [flatZeroExtend,outside]

theorem flatZeroExtend_indicator (f : flatChart → ℂ) :
    (flatChart : Set FlatConfiguration).indicator (flatZeroExtend f)=flatZeroExtend f := by
  ext z
  by_cases inside : z∈flatChart <;> simp [flatZeroExtend,inside]

theorem flatZeroExtend_memLp (f : FlatChartHilbert) : MemLp (flatZeroExtend f) 2 flatMeasure := by
  rw [←flatZeroExtend_indicator,memLp_indicator_iff_restrict flatChart.isOpen.measurableSet,
    ←map_comap_subtype_coe flatChart.isOpen.measurableSet,
    (MeasurableEmbedding.subtype_coe flatChart.isOpen.measurableSet).memLp_map_measure_iff]
  simpa only [Function.comp_def,flatZeroExtend_on_chart] using! Lp.memLp f

theorem flatZeroExtend_eLpNorm (f : flatChart → ℂ) :
    eLpNorm (flatZeroExtend f) 2 flatMeasure=eLpNorm f 2 flatChartMeasure := by
  rw [←flatZeroExtend_indicator,eLpNorm_indicator_eq_eLpNorm_restrict flatChart.isOpen.measurableSet,
    ←map_comap_subtype_coe flatChart.isOpen.measurableSet,
    (MeasurableEmbedding.subtype_coe flatChart.isOpen.measurableSet).eLpNorm_map_measure]
  congr 1
  ext z
  exact flatZeroExtend_on_chart f z

theorem flatZeroExtend_congr_ae {f g : flatChart → ℂ} (same : f=ᵐ[flatChartMeasure] g) :
    flatZeroExtend f=ᵐ[flatMeasure] flatZeroExtend g := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (flatChart : Set FlatConfiguration)
  · rw [ae_restrict_iff_subtype flatChart.isOpen.measurableSet]
    simpa only [flatZeroExtend_on_chart] using! same
  · filter_upwards [ae_restrict_mem flatChart.isOpen.measurableSet.compl] with z outside
    rw [flatZeroExtend_outside _ _ outside,flatZeroExtend_outside _ _ outside]

theorem flatZeroExtend_add (f g : flatChart → ℂ) :
    flatZeroExtend (f+g)=flatZeroExtend f+flatZeroExtend g := by
  ext z
  by_cases inside : z∈flatChart <;> simp [flatZeroExtend,inside]

theorem flatZeroExtend_smul (c : ℂ) (f : flatChart → ℂ) :
    flatZeroExtend (c • f)=c • flatZeroExtend f := by
  ext z
  by_cases inside : z∈flatChart <;> simp [flatZeroExtend,inside]

abbrev FlatRawHilbert := Lp ℂ 2 flatMeasure

def flatZeroExtension : FlatChartHilbert →ₗᵢ[ℂ] FlatRawHilbert where
  toFun f := (flatZeroExtend_memLp f).toLp (flatZeroExtend f)
  map_add' f g := by
    ext1
    filter_upwards [(flatZeroExtend_memLp (f+g)).coeFn_toLp,
      (flatZeroExtend_memLp f).coeFn_toLp,(flatZeroExtend_memLp g).coeFn_toLp,
      Lp.coeFn_add ((flatZeroExtend_memLp f).toLp _) ((flatZeroExtend_memLp g).toLp _),
      flatZeroExtend_congr_ae (Lp.coeFn_add f g)] with z hadd hf hg hout hin
    simp only [Pi.add_apply] at *
    rw [hadd,hout,hf,hg,hin]
    exact congrFun (flatZeroExtend_add (f : flatChart→ℂ) (g : flatChart→ℂ)) z
  map_smul' c f := by
    ext1
    filter_upwards [(flatZeroExtend_memLp (c • f)).coeFn_toLp,
      (flatZeroExtend_memLp f).coeFn_toLp,Lp.coeFn_smul c ((flatZeroExtend_memLp f).toLp _),
      flatZeroExtend_congr_ae (Lp.coeFn_smul c f)] with z hc hf hout hin
    simp only [Pi.smul_apply,RingHom.id_apply] at *
    rw [hc,hout,hf,hin]
    exact congrFun (flatZeroExtend_smul c (f : flatChart→ℂ)) z
  norm_map' f := by
    change ‖(flatZeroExtend_memLp f).toLp (flatZeroExtend f)‖=‖f‖
    simp only [Lp.norm_def]
    rw [eLpNorm_congr_ae (flatZeroExtend_memLp f).coeFn_toLp,flatZeroExtend_eLpNorm]

theorem flatZeroExtension_readback (f : FlatChartHilbert) :
    flatZeroExtension f=ᵐ[flatMeasure] flatZeroExtend f := (flatZeroExtend_memLp f).coeFn_toLp

def sourceRawHalfDensity (N : ℕ) : SectorHilbert N →ₗᵢ[ℂ] FlatRawHilbert :=
  flatZeroExtension.comp (flatHalfDensityEquiv N).toLinearIsometry

theorem sourceRawHalfDensity_norm (N : ℕ) (f : SectorHilbert N) :
    ‖sourceRawHalfDensity N f‖=‖f‖ := (sourceRawHalfDensity N).norm_map f

theorem source_raw_core_readback (N : ℕ) (f : 𝓓(physicalChart,ℂ)) :
    sourceRawHalfDensity N (GaussCoreHilbert.scalarLp N f)=ᵐ[flatMeasure]
      flatZeroExtend (fun z => (rawHalfFactor N (chartCoordinates.symm z) : ℂ)*
        f (fullCoordinates.symm z.val)) :=
  (flatZeroExtension_readback _).trans (flatZeroExtend_congr_ae (flat_core_readback N f))

end LowEnergy.PreparationVacuumWeylDomain
