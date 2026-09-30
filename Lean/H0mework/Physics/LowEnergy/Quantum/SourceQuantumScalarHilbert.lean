import H0mework.Physics.LowEnergy.Quantum.SourceQuantumScalarChart
import H0mework.Physics.LowEnergy.Quantum.OpenChartTestDomain
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space

/-! The canonical scalar L² space and its dense smooth operator domain.

The fixed source vacuum, original native action and scalar inner product
already determine the slice and its open regular chart. Their canonical
Lebesgue measure is restricted through the original open embedding. No
measure, chart, rank witness or dense-domain hypothesis is caller supplied.
-/

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceQuantumScalarHilbert

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology ContDiff
open SourceQuantumScalarChart

/-- The actual scalar slice's inner product fixes its Lebesgue normalization. -/
def sliceMeasure : Measure scalarSlice :=
  (measureSpaceOfInnerProductSpace (E := scalarSlice)).volume

instance sliceMeasure_regular : sliceMeasure.Regular := by
  unfold sliceMeasure
  infer_instance

/-- The original noncharacteristic open chart inherits this exact measure. -/
def chartMeasure : Measure scalarChart :=
  sliceMeasure.comap (Subtype.val : scalarChart → scalarSlice)

instance chartMeasure_regular : chartMeasure.Regular :=
  Measure.Regular.comap' sliceMeasure scalarChart.isOpenEmbedding'

/-- The completed complex scalar state space, with its actual source measure. -/
abbrev Hilbert := Lp ℂ 2 chartMeasure

instance hilbert_complete : CompleteSpace Hilbert := inferInstance
instance hilbert_innerProduct : InnerProductSpace ℂ Hilbert := inferInstance

/-- Original-source smooth tests, with compact support strictly inside the chart. -/
def testDomain : Submodule ℂ Hilbert where
  carrier := {f | ∃ g : scalarSlice → ℂ,
    f =ᵐ[chartMeasure] (fun x : scalarChart => g x) ∧ HasCompactSupport g ∧
    ContDiff ℝ ∞ g ∧ tsupport g ⊆ (scalarChart : Set scalarSlice)}
  zero_mem' := by
    refine ⟨0, Lp.coeFn_zero _ _ _, HasCompactSupport.zero, contDiff_const, ?_⟩
    simp
  add_mem' := by
    rintro f h ⟨g, hfg, hgk, hgc, hgs⟩ ⟨k, hhk, hkk, hkc, hks⟩
    refine ⟨g + k, ?_, hgk.add hkk, hgc.add hkc, ?_⟩
    · filter_upwards [Lp.coeFn_add f h, hfg, hhk] with x hsum hg hk
      simpa [hg, hk] using hsum
    · exact (tsupport_add g k).trans (union_subset hgs hks)
  smul_mem' := by
    rintro c f ⟨g, hfg, hgk, hgc, hgs⟩
    refine ⟨c • g, ?_, ?_, hgc.const_smul c, ?_⟩
    · filter_upwards [Lp.coeFn_smul c f, hfg] with x hsmul hg
      simpa [hg] using hsmul
    · exact hgk.smul_left (f := fun _ => c)
    · exact (tsupport_smul_subset_right (fun _ => c) g).trans hgs

theorem testDomain_dense : Dense (testDomain : Set Hilbert) :=
  OpenChartTestDomain.dense_compact_contDiff_inside scalarChart chartMeasure (by norm_num)

theorem testDomain_topologicalClosure : testDomain.topologicalClosure = ⊤ := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.mp testDomain_dense

/-- The source vacuum actually belongs to this chart before Hilbert completion. -/
def sourcePoint : scalarChart := ⟨0, zero_mem_scalarChart⟩

end LowEnergy.SourceQuantumScalarHilbert
