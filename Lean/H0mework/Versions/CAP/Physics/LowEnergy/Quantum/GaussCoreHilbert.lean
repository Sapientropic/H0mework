import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussCoreDifferential
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.LinearAlgebra.LinearPMap

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.GaussCoreHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussCoreDifferential SourceQuantumFockGauge
open MeasureTheory Set Function
open scoped ContDiff Distributions Topology ENNReal

abbrev H := GaussHistoryHilbert.FockHilbert
abbrev Core := GaussHistoryHilbert.fockTestDomain
open GaussHistoryHilbert (physicalChart)

instance configuration_openPos : GaussHistoryHilbert.configurationMeasure.IsOpenPosMeasure := by
  have : coframeMeasure.IsOpenPosMeasure := by unfold coframeMeasure; infer_instance
  have : SourceQuantumScalarHilbert.sliceMeasure.IsOpenPosMeasure := by
    unfold SourceQuantumScalarHilbert.sliceMeasure
    infer_instance
  have : GaussHistoryHilbert.coordinateGaugeMeasure.IsOpenPosMeasure := by
    unfold GaussHistoryHilbert.coordinateGaugeMeasure
    infer_instance
  unfold GaussHistoryHilbert.configurationMeasure
  infer_instance

instance chart_openPos : GaussHistoryHilbert.chartMeasure.IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap _ physicalChart.isOpenEmbedding'

instance number_openPos (N : ℕ) : (GaussHistoryHilbert.numberMeasure N).IsOpenPosMeasure := by
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := GaussHistoryHilbert.chartMeasure)
  apply withDensity_absolutelyContinuous'
  · exact (ENNReal.continuous_ofReal.comp (GaussHistoryHilbert.numberWeight_continuous N)).measurable.aemeasurable
  · exact Filter.Eventually.of_forall (fun z => (ENNReal.ofReal_pos.mpr (GaussHistoryHilbert.numberWeight_pos N z)).ne')

theorem restricted_compact {F : Type*} [Zero F] {g : SourceCoordinateSlice → F}
    (compact : HasCompactSupport g) (inside : tsupport g ⊆ (physicalChart : Set SourceCoordinateSlice)) :
    HasCompactSupport (fun z : physicalChart => g z) := by
  have hk : IsCompact ((Subtype.val : physicalChart → SourceCoordinateSlice) ⁻¹' tsupport g) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [image_preimage_eq_of_subset]
    · exact compact
    · intro x hx
      exact ⟨⟨x, inside hx⟩, rfl⟩
  apply hk.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact subset_tsupport g hz
  · exact isClosed_closure.preimage continuous_subtype_val

def component (word : Occupation) : QuantumTest →L[ℂ] 𝓓(physicalChart, ℂ) :=
  TestFunction.postcompCLM (PiLp.proj 2 (fun _ : Occupation => ℂ) word)

theorem component_apply (word : Occupation) (f : QuantumTest) (z : SourceCoordinateSlice) :
    component word f z = f z word := rfl

theorem scalarMemLp (N : ℕ) (f : 𝓓(physicalChart, ℂ)) :
    MemLp (fun z : physicalChart => f z) 2 (GaussHistoryHilbert.numberMeasure N) :=
  (f.continuous.comp continuous_subtype_val).memLp_of_hasCompactSupport
    (restricted_compact f.hasCompactSupport f.tsupport_subset)

def scalarLp (N : ℕ) (f : 𝓓(physicalChart, ℂ)) : GaussHistoryHilbert.SectorHilbert N :=
  (scalarMemLp N f).toLp _

theorem scalarLp_ae (N : ℕ) (f : 𝓓(physicalChart, ℂ)) :
    scalarLp N f =ᵐ[GaussHistoryHilbert.numberMeasure N] (fun z : physicalChart => f z) :=
  (scalarMemLp N f).coeFn_toLp

def embed : QuantumTest →ₗ[ℂ] H where
  toFun f := WithLp.toLp 2 (fun word => scalarLp word.card (component word f))
  map_add' f g := by
    apply PiLp.ext
    intro word
    apply Lp.ext
    filter_upwards [scalarLp_ae word.card (component word (f+g)),
      scalarLp_ae word.card (component word f), scalarLp_ae word.card (component word g),
      Lp.coeFn_add (scalarLp word.card (component word f)) (scalarLp word.card (component word g))]
      with z hsum hf hg hadd
    change scalarLp word.card (component word (f+g)) z =
      (scalarLp word.card (component word f) + scalarLp word.card (component word g)) z
    rw [hsum, hadd, Pi.add_apply, hf, hg]
    rfl
  map_smul' c f := by
    apply PiLp.ext
    intro word
    apply Lp.ext
    filter_upwards [scalarLp_ae word.card (component word (c • f)),
      scalarLp_ae word.card (component word f),
      Lp.coeFn_smul c (scalarLp word.card (component word f))] with z hsum hf hsmul
    change scalarLp word.card (component word (c • f)) z =
      (c • scalarLp word.card (component word f)) z
    rw [hsum, hsmul, Pi.smul_apply, hf]
    rfl

theorem embed_ae (f : QuantumTest) (word : Occupation) :
    embed f word =ᵐ[GaussHistoryHilbert.numberMeasure word.card] (fun z : physicalChart => f z word) :=
  scalarLp_ae word.card (component word f)

theorem embed_mem_core (f : QuantumTest) : embed f ∈ Core := by
  intro word
  exact ⟨component word f, embed_ae f word, (component word f).hasCompactSupport,
    (component word f).contDiff, (component word f).tsupport_subset⟩

theorem embed_injective : Function.Injective embed := by
  intro f g h
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · apply PiLp.ext
    intro word
    have he : (fun x : physicalChart => f x word) =ᵐ[GaussHistoryHilbert.numberMeasure word.card]
        (fun x : physicalChart => g x word) :=
      (embed_ae f word).symm.trans ((congrArg (fun v : H => v word) h) ▸ embed_ae g word)
    have hc := Measure.eq_of_ae_eq he
      ((component word f).continuous.comp continuous_subtype_val)
      ((component word g).continuous.comp continuous_subtype_val)
    exact congrFun hc ⟨z, hz⟩
  · rw [image_eq_zero_of_notMem_tsupport (fun hf => hz (f.tsupport_subset hf)),
      image_eq_zero_of_notMem_tsupport (fun hg => hz (g.tsupport_subset hg))]

theorem embed_surjective_core (f : Core) : ∃ g : QuantumTest, embed g = (f : H) := by
  have h (word : Occupation) := f.property word
  choose g hfg hgk hgc hgs using h
  let combined : SourceCoordinateSlice → FockFiber := fun z => WithLp.toLp 2 (fun word => g word z)
  have hk : IsCompact (⋃ word, tsupport (g word)) := isCompact_iUnion hgk
  have hs : tsupport combined ⊆ ⋃ word, tsupport (g word) := by
    apply closure_minimal _ hk.isClosed
    intro z hz
    by_contra hn
    apply hz
    apply PiLp.ext
    intro word
    change g word z = 0
    exact image_eq_zero_of_notMem_tsupport (fun hw => hn (mem_iUnion.mpr ⟨word, hw⟩))
  have hc : ContDiff ℝ ∞ combined := (contDiff_piLp 2).mpr hgc
  let test : QuantumTest :=
    ⟨combined, hc, hk.of_isClosed_subset isClosed_closure hs,
      hs.trans (iUnion_subset hgs)⟩
  refine ⟨test, ?_⟩
  apply PiLp.ext
  intro word
  exact Lp.ext ((embed_ae test word).trans (hfg word).symm)

def coreEquiv : QuantumTest ≃ₗ[ℂ] Core :=
  LinearEquiv.ofBijective (embed.codRestrict Core embed_mem_core)
    ⟨fun f g h => embed_injective (congrArg Subtype.val h), by
      intro f
      obtain ⟨g, hg⟩ := embed_surjective_core f
      exact ⟨g, Subtype.ext hg⟩⟩

def realize (A : QuantumTest →ₗ[ℂ] QuantumTest) : H →ₗ.[ℂ] H where
  domain := Core
  toFun := embed.comp (A.comp coreEquiv.symm.toLinearMap)

theorem realize_preserves_core (A : QuantumTest →ₗ[ℂ] QuantumTest) (f : (realize A).domain) :
    realize A f ∈ (realize A).domain := embed_mem_core _

theorem realize_dense (A : QuantumTest →ₗ[ℂ] QuantumTest) : Dense ((realize A).domain : Set H) :=
  GaussHistoryHilbert.fockTestDomain_dense

def momentum (v : GaussLiveMomentum.Ambient) : H →ₗ.[ℂ] H := realize (covariantMomentum v)

theorem momentum_on_test (v : GaussLiveMomentum.Ambient) (f : QuantumTest) :
    momentum v (coreEquiv f) = embed (covariantMomentum v f) := by
  change embed (covariantMomentum v (coreEquiv.symm (coreEquiv f))) = _
  rw [coreEquiv.symm_apply_apply]

#print axioms embed_injective
#print axioms coreEquiv
#print axioms realize_preserves_core
#print axioms momentum_on_test
end LowEnergy.GaussCoreHilbert
