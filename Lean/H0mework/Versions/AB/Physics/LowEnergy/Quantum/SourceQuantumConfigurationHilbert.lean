import H0mework.Physics.LowEnergy.Quantum.SourceQuantumScalarHilbert
import H0mework.Versions.AB.Physics.LowEnergyQuantum.Carrier
import H0mework.Versions.R2.Physics.SpinPair.Actual
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Native common configuration and the original coframe number weight.

This is the source scalar slice times all three native spatial connections,
before the residual gauge quotient. The scalar dimension and the later
coordinate gauge minor are not supplied as assumptions or numerical aliases.
-/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceQuantumConfigurationHilbert

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology ContDiff
open SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore

abbrev Coframe := EuclideanSpace ℝ (Fin 6)

def Gauge := PiLp 2 (fun _ : Fin 3 => NativeLie)
instance : NormedAddCommGroup Gauge :=
  inferInstanceAs (NormedAddCommGroup (PiLp 2 (fun _ : Fin 3 => NativeLie)))
instance : NormedSpace ℝ Gauge :=
  inferInstanceAs (NormedSpace ℝ (PiLp 2 (fun _ : Fin 3 => NativeLie)))
instance : InnerProductSpace ℝ Gauge :=
  inferInstanceAs (InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 3 => NativeLie)))
instance : FiniteDimensional ℝ Gauge :=
  inferInstanceAs (FiniteDimensional ℝ (PiLp 2 (fun _ : Fin 3 => NativeLie)))
instance : MeasurableSpace Gauge := borel Gauge
instance : BorelSpace Gauge := ⟨rfl⟩

abbrev Configuration := Coframe × scalarSlice × Gauge

def coframeMeasure : Measure Coframe :=
  (measureSpaceOfInnerProductSpace (E := Coframe)).volume

def gaugeMeasure : Measure Gauge :=
  (measureSpaceOfInnerProductSpace (E := Gauge)).volume

def configurationMeasure : Measure Configuration :=
  coframeMeasure.prod (SourceQuantumScalarHilbert.sliceMeasure.prod gaugeMeasure)

instance coframeMeasure_locallyFinite : IsLocallyFiniteMeasure coframeMeasure := by
  unfold coframeMeasure
  infer_instance
instance gaugeMeasure_locallyFinite : IsLocallyFiniteMeasure gaugeMeasure := by
  unfold gaugeMeasure
  infer_instance
instance configurationMeasure_locallyFinite : IsLocallyFiniteMeasure configurationMeasure := by
  unfold configurationMeasure SourceQuantumScalarHilbert.sliceMeasure
  infer_instance
instance configurationMeasure_regular : configurationMeasure.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure configurationMeasure

def chart : Opens Configuration :=
  ⟨{z | 0 < z.1 0 ∧ 0 < z.1 2 ∧ 0 < z.1 5 ∧ z.2.1 ∈ scalarChart}, by
    have h0 : Continuous (fun z : Configuration => z.1 0) := by fun_prop
    have h2 : Continuous (fun z : Configuration => z.1 2) := by fun_prop
    have h5 : Continuous (fun z : Configuration => z.1 5) := by fun_prop
    exact (isOpen_lt continuous_const h0).inter
      ((isOpen_lt continuous_const h2).inter
        ((isOpen_lt continuous_const h5).inter
          (scalarChart.isOpen.preimage (continuous_fst.comp continuous_snd))))⟩

instance chart_locallyCompact : LocallyCompactSpace chart := chart.isOpen.locallyCompactSpace

def chartMeasure : Measure chart :=
  configurationMeasure.comap (Subtype.val : chart → Configuration)
instance chartMeasure_regular : chartMeasure.Regular :=
  Measure.Regular.comap' configurationMeasure chart.isOpenEmbedding'

def coframeVolume (z : chart) : ℝ := z.val.1 0 * z.val.1 2 * z.val.1 5

theorem coframeVolume_pos (z : chart) : 0 < coframeVolume z :=
  mul_pos (mul_pos z.property.1 z.property.2.1) z.property.2.2.1

theorem coframeVolume_continuous : Continuous coframeVolume := by
  unfold coframeVolume
  fun_prop

def numberWeight (N : ℕ) (z : chart) : ℝ := coframeVolume z ^ (N + 2)

theorem numberWeight_pos (N : ℕ) (z : chart) : 0 < numberWeight N z :=
  pow_pos (coframeVolume_pos z) _

theorem numberWeight_continuous (N : ℕ) : Continuous (numberWeight N) :=
  coframeVolume_continuous.pow _

def numberMeasure (N : ℕ) : Measure chart :=
  chartMeasure.withDensity (fun z => ENNReal.ofReal (numberWeight N z))

instance numberMeasure_locallyFinite (N : ℕ) : IsLocallyFiniteMeasure (numberMeasure N) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (numberWeight_continuous N)
instance numberMeasure_regular (N : ℕ) : (numberMeasure N).Regular := inferInstance

abbrev SectorHilbert (N : ℕ) := Lp ℂ 2 (numberMeasure N)

instance sector_complete (N : ℕ) : CompleteSpace (SectorHilbert N) := inferInstance
instance sector_inner (N : ℕ) : InnerProductSpace ℂ (SectorHilbert N) := inferInstance

/-- Both original full exterior-matter branches, without a mode cutoff. -/
abbrev Mode := LowEnergy.Quantum.Index ⊕ LowEnergy.Quantum.Index
noncomputable instance mode_decidableEq : DecidableEq Mode := Classical.decEq _
abbrev Occupation := Finset Mode

theorem full_mode_card : Fintype.card Mode = 504 := by
  change Fintype.card (LowEnergy.Quantum.Index ⊕ LowEnergy.Quantum.Index) = 504
  rw [Fintype.card_sum, LowEnergy.Quantum.index_card]

/-- The source number weight is attached to the actual CAR occupation basis. -/
abbrev FockHilbert := PiLp 2 (fun word : Occupation => SectorHilbert word.card)
instance fock_complete : CompleteSpace FockHilbert := inferInstance
instance fock_inner : InnerProductSpace ℂ FockHilbert := inferInstance

def testDomain (N : ℕ) : Submodule ℂ (SectorHilbert N) where
  carrier := {f | ∃ g : Configuration → ℂ,
    f =ᵐ[numberMeasure N] (fun z : chart => g z) ∧ HasCompactSupport g ∧
    ContDiff ℝ ∞ g ∧ tsupport g ⊆ (chart : Set Configuration)}
  zero_mem' := by
    refine ⟨0, Lp.coeFn_zero _ _ _, HasCompactSupport.zero, contDiff_const, ?_⟩
    simp
  add_mem' := by
    rintro f h ⟨g, hfg, hgk, hgc, hgs⟩ ⟨k, hhk, hkk, hkc, hks⟩
    refine ⟨g + k, ?_, hgk.add hkk, hgc.add hkc, ?_⟩
    · filter_upwards [Lp.coeFn_add f h, hfg, hhk] with z hsum hg hk
      simpa [hg, hk] using hsum
    · exact (tsupport_add g k).trans (union_subset hgs hks)
  smul_mem' := by
    rintro c f ⟨g, hfg, hgk, hgc, hgs⟩
    refine ⟨c • g, ?_, ?_, hgc.const_smul c, ?_⟩
    · filter_upwards [Lp.coeFn_smul c f, hfg] with z hsmul hg
      simpa [hg] using hsmul
    · exact hgk.smul_left (f := fun _ => c)
    · exact (tsupport_smul_subset_right (fun _ => c) g).trans hgs

theorem testDomain_dense (N : ℕ) : Dense (testDomain N : Set (SectorHilbert N)) :=
  OpenChartTestDomain.dense_compact_contDiff_inside chart (numberMeasure N) (by norm_num)

theorem gauge_finrank : Module.finrank ℝ Gauge = 3 * Module.finrank ℝ NativeLie := by
  calc
    Module.finrank ℝ Gauge = Module.finrank ℝ (Fin 3 → NativeLie) :=
      (WithLp.linearEquiv 2 ℝ (Fin 3 → NativeLie)).finrank_eq
    _ = _ := by simp [Module.finrank_pi_fintype]

theorem configuration_finrank : Module.finrank ℝ Configuration =
    6 + Module.finrank ℝ scalarSlice + 3 * Module.finrank ℝ NativeLie := by
  rw [Module.finrank_prod, Module.finrank_prod, gauge_finrank]
  simp [Coframe, Nat.add_assoc]

/-- The complete source Fock test domain, with no selected occupation sector. -/
def fockTestDomain : Submodule ℂ FockHilbert where
  carrier := {f | ∀ word, f word ∈ testDomain word.card}
  zero_mem' := by
    intro word
    exact (testDomain word.card).zero_mem
  add_mem' := by
    intro f g hf hg word
    exact (testDomain word.card).add_mem (hf word) (hg word)
  smul_mem' := by
    intro c f hf word
    exact (testDomain word.card).smul_mem c (hf word)

theorem fockTestDomain_dense : Dense (fockTestDomain : Set FockHilbert) := by
  let e := PiLp.homeomorph 2 (fun word : Occupation => SectorHilbert word.card)
  have hd := dense_pi (Set.univ : Set Occupation) (fun word _ => testDomain_dense word.card)
  have ht := e.isOpenQuotientMap.dense_preimage_iff.mpr hd
  convert ht using 1
  ext f
  change (∀ word, f word ∈ testDomain word.card) ↔
    ∀ word, word ∈ (Set.univ : Set Occupation) → e f word ∈ testDomain word.card
  simp only [Set.mem_univ, true_implies]
  rfl

def sourceCoframe : Coframe :=
  WithLp.toLp 2 ![Stage9C.Material.SpinPair.actual.coframe 0 1 1,
    Stage9C.Material.SpinPair.actual.coframe 0 2 1,
    Stage9C.Material.SpinPair.actual.coframe 0 2 2,
    Stage9C.Material.SpinPair.actual.coframe 0 3 1,
    Stage9C.Material.SpinPair.actual.coframe 0 3 2,
    Stage9C.Material.SpinPair.actual.coframe 0 3 3]

@[simp] theorem sourceCoframe_eq : sourceCoframe = WithLp.toLp 2 ![1, 0, 1, 0, 0, 1] := rfl

def sourceGauge : Gauge := WithLp.toLp 2 (fun i : Fin 3 =>
  StageNineHolonomicField.p286CoordinateEquiv
    (Stage9C.Material.SpinPair.actual.gaugeConnection 0 i.succ))

def sourcePoint : chart :=
  ⟨(sourceCoframe, (0, sourceGauge)), by
    refine ⟨?_, ?_, ?_, zero_mem_scalarChart⟩
    all_goals change 0 < (1 : ℝ); norm_num⟩

theorem source_weight_one (N : ℕ) : numberWeight N sourcePoint = 1 := by
  simp [numberWeight, coframeVolume, sourcePoint]

end LowEnergy.SourceQuantumConfigurationHilbert
