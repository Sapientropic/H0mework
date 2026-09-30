import H0mework.Physics.LowEnergy.Quantum.SourceQuantumResidualFlowMeasure
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-! The actual orbit/slice Jacobian for the source Gauss100 history space. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.GaussHistoryHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumResidualFlow
open SourceQuantumNativeDimensions
open scoped InnerProductSpace ContDiff
open MeasureTheory Set

abbrev OrbitSlice := WithLp 2 (stabilizer × coordinateSlice)

def sourceSplit : OrbitSlice ≃ₗ[ℝ] Gauge :=
  (WithLp.linearEquiv 2 ℝ (stabilizer × coordinateSlice)).trans sourceSplitEquiv

def sourceBasis : OrthonormalBasis (Fin (Module.finrank ℝ OrbitSlice)) ℝ OrbitSlice :=
  stdOrthonormalBasis ℝ OrbitSlice

def sourceJacobian : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i => sourceSplit (sourceBasis i))).det

theorem source_jacobian_pos : 0 < sourceJacobian := by
  apply Real.sqrt_pos.mpr
  have hi : LinearIndependent ℝ (fun i => sourceSplit (sourceBasis i)) :=
    (sourceBasis.toBasis.map sourceSplit).linearIndependent
  exact (Matrix.posDef_gram_of_linearIndependent hi).det_pos

def combined (A : Gauge) : (stabilizer × coordinateSlice) →ₗ[ℝ] Gauge :=
  ((gaugeAction.flip A).comp (LinearMap.fst ℝ stabilizer coordinateSlice)) +
    (coordinateSlice.subtype.comp (LinearMap.snd ℝ stabilizer coordinateSlice))

def relative (A : Gauge) : Module.End ℝ (stabilizer × coordinateSlice) :=
  sourceSplitEquiv.symm.toLinearMap.comp (combined A)

theorem combined_source : combined SourceQuantumConfigurationHilbert.sourceGauge =
    sourceSplitEquiv.toLinearMap := by
  apply LinearMap.ext
  intro av
  change gaugeAction av.1 SourceQuantumConfigurationHilbert.sourceGauge + (av.2 : Gauge) =
    residualOrbit av.1 + (av.2 : Gauge)
  rfl

theorem relative_source : relative SourceQuantumConfigurationHilbert.sourceGauge = 1 := by
  unfold relative
  rw [combined_source]
  apply LinearMap.ext
  intro av
  exact sourceSplitEquiv.symm_apply_apply av

def coordinateBasis := sourceBasis.toBasis.map
  (WithLp.linearEquiv 2 ℝ (stabilizer × coordinateSlice))

def relativeMatrix (A : Gauge) : Matrix (Fin (Module.finrank ℝ OrbitSlice))
    (Fin (Module.finrank ℝ OrbitSlice)) ℝ :=
  LinearMap.toMatrix coordinateBasis coordinateBasis (relative A)

def jacobian (A : Gauge) : ℝ := sourceJacobian * |(relativeMatrix A).det|

theorem jacobian_source : jacobian SourceQuantumConfigurationHilbert.sourceGauge = sourceJacobian := by
  simp [jacobian, relativeMatrix, relative_source]

theorem relativeMatrix_smooth (i j : Fin (Module.finrank ℝ OrbitSlice)) :
    ContDiff ℝ ∞ (fun A => relativeMatrix A i j) := by
  simp only [relativeMatrix, LinearMap.toMatrix_apply]
  let read : Gauge →ₗ[ℝ] ℝ :=
    (coordinateBasis.coord i).comp sourceSplitEquiv.symm.toLinearMap
  have hread : ContDiff ℝ ∞ read := read.toContinuousLinearMap.contDiff
  have hvalue : ContDiff ℝ ∞ (fun A : Gauge => gaugeAction (coordinateBasis j).1 A +
      ((coordinateBasis j).2 : Gauge)) :=
    (gaugeAction (coordinateBasis j).1).toContinuousLinearMap.contDiff.add contDiff_const
  exact hread.comp hvalue

theorem jacobian_continuous : Continuous jacobian :=
  continuous_const.mul
    (continuous_pi (fun i => continuous_pi (fun j => (relativeMatrix_smooth i j).continuous))).matrix_det.abs

theorem coordinate_finrank : Module.finrank ℝ SourceCoordinateSlice = 100 := by
  rw [commonSliceEquiv.finrank_eq]
  exact sourceLinearSlice_finrank

def firstGauge : Gauge →ₗ[ℝ] ℝ where
  toFun A := (nativeCoordinates (gaugeCoordinates A 0)).1 1
  map_add' := by intros; simp
  map_smul' := by intros; simp

def secondGauge : Gauge →ₗ[ℝ] ℝ where
  toFun A := (nativeCoordinates (gaugeCoordinates A 1)).1 0
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem source_firstGauge_pos : 0 < firstGauge SourceQuantumConfigurationHilbert.sourceGauge := by
  change 0 < (nativeCoordinates (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge 0)).1 1
  rw [sourceGauge_apply, map_smul, colorGenerator_coordinates]
  simpa using div_pos SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.gaugeScale_pos
    (show (0 : ℝ) < 2 by norm_num)

theorem source_secondGauge_pos : 0 < secondGauge SourceQuantumConfigurationHilbert.sourceGauge := by
  change 0 < (nativeCoordinates (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge 1)).1 0
  rw [sourceGauge_apply, map_smul, colorGenerator_coordinates]
  simpa using div_pos SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.gaugeScale_pos
    (show (0 : ℝ) < 2 by norm_num)

def physicalChart : TopologicalSpace.Opens SourceCoordinateSlice :=
  ⟨{z | 0 < z.1 0 ∧ 0 < z.1 2 ∧ 0 < z.1 5 ∧ z.2.1 ∈ scalarChart ∧
    0 < firstGauge z.2.2 ∧ 0 < secondGauge z.2.2 ∧ 0 < jacobian z.2.2}, by
    have h0 : Continuous (fun z : SourceCoordinateSlice => z.1 0) := by fun_prop
    have h2 : Continuous (fun z : SourceCoordinateSlice => z.1 2) := by fun_prop
    have h5 : Continuous (fun z : SourceCoordinateSlice => z.1 5) := by fun_prop
    have hg : Continuous (fun z : SourceCoordinateSlice => (z.2.2 : Gauge)) := by fun_prop
    exact (isOpen_lt continuous_const h0).inter ((isOpen_lt continuous_const h2).inter
      ((isOpen_lt continuous_const h5).inter ((scalarChart.isOpen.preimage (by fun_prop)).inter
        ((isOpen_lt continuous_const (firstGauge.toContinuousLinearMap.continuous.comp hg)).inter
          ((isOpen_lt continuous_const (secondGauge.toContinuousLinearMap.continuous.comp hg)).inter
            (isOpen_lt continuous_const (jacobian_continuous.comp hg)))))))⟩

def sourcePoint : physicalChart :=
  ⟨(sourceCoframe, 0, ⟨SourceQuantumConfigurationHilbert.sourceGauge, sourceGauge_mem_coordinateSlice⟩), by
    refine ⟨?_, ?_, ?_, zero_mem_scalarChart, source_firstGauge_pos, source_secondGauge_pos, ?_⟩
    · change (0 : ℝ) < 1; norm_num
    · change (0 : ℝ) < 1; norm_num
    · change (0 : ℝ) < 1; norm_num
    · rw [jacobian_source]; exact source_jacobian_pos⟩

def coordinateGaugeMeasure : Measure coordinateSlice :=
  (measureSpaceOfInnerProductSpace (E := coordinateSlice)).volume

def configurationMeasure : Measure SourceCoordinateSlice :=
  coframeMeasure.prod (SourceQuantumScalarHilbert.sliceMeasure.prod coordinateGaugeMeasure)

instance coordinateGaugeMeasure_locallyFinite : IsLocallyFiniteMeasure coordinateGaugeMeasure := by
  unfold coordinateGaugeMeasure
  infer_instance

instance configurationMeasure_locallyFinite : IsLocallyFiniteMeasure configurationMeasure := by
  unfold configurationMeasure
  infer_instance

instance configurationMeasure_regular : configurationMeasure.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure configurationMeasure

instance physicalChart_locallyCompact : LocallyCompactSpace physicalChart :=
  physicalChart.isOpen.locallyCompactSpace

def chartMeasure : Measure physicalChart :=
  configurationMeasure.comap (Subtype.val : physicalChart → SourceCoordinateSlice)

instance chartMeasure_regular : chartMeasure.Regular :=
  Measure.Regular.comap' configurationMeasure physicalChart.isOpenEmbedding'

def spatialVolume (z : physicalChart) : ℝ := z.val.1 0 * z.val.1 2 * z.val.1 5

theorem spatialVolume_pos (z : physicalChart) : 0 < spatialVolume z :=
  mul_pos (mul_pos z.property.1 z.property.2.1) z.property.2.2.1

def numberWeight (N : ℕ) (z : physicalChart) : ℝ :=
  jacobian (z.val.2.2 : Gauge) * spatialVolume z ^ (N+2)

theorem numberWeight_pos (N : ℕ) (z : physicalChart) : 0 < numberWeight N z :=
  mul_pos z.property.2.2.2.2.2.2 (pow_pos (spatialVolume_pos z) _)

theorem numberWeight_continuous (N : ℕ) : Continuous (numberWeight N) := by
  have hg : Continuous (fun z : physicalChart => (z.val.2.2 : Gauge)) := by fun_prop
  have hv : Continuous spatialVolume := by unfold spatialVolume; fun_prop
  exact (jacobian_continuous.comp hg).mul (hv.pow _)

theorem source_weight (N : ℕ) : numberWeight N sourcePoint = sourceJacobian := by
  simp [numberWeight, spatialVolume, sourcePoint, sourceCoframe_eq, jacobian_source]

def numberMeasure (N : ℕ) : Measure physicalChart :=
  chartMeasure.withDensity (fun z => ENNReal.ofReal (numberWeight N z))

instance numberMeasure_locallyFinite (N : ℕ) : IsLocallyFiniteMeasure (numberMeasure N) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (numberWeight_continuous N)

instance numberMeasure_regular (N : ℕ) : (numberMeasure N).Regular := inferInstance

abbrev SectorHilbert (N : ℕ) := Lp ℂ 2 (numberMeasure N)
instance sector_complete (N : ℕ) : CompleteSpace (SectorHilbert N) := inferInstance
instance sector_inner (N : ℕ) : InnerProductSpace ℂ (SectorHilbert N) := inferInstance

def testDomain (N : ℕ) : Submodule ℂ (SectorHilbert N) where
  carrier := {f | ∃ g : SourceCoordinateSlice → ℂ,
    f =ᵐ[numberMeasure N] (fun z : physicalChart => g z) ∧ HasCompactSupport g ∧
    ContDiff ℝ ∞ g ∧ tsupport g ⊆ (physicalChart : Set SourceCoordinateSlice)}
  zero_mem' := by
    refine ⟨0, Lp.coeFn_zero _ _ _, HasCompactSupport.zero, contDiff_const, ?_⟩
    simp
  add_mem' := by
    rintro f h ⟨g, hfg, hgk, hgc, hgs⟩ ⟨k, hhk, hkk, hkc, hks⟩
    refine ⟨g+k, ?_, hgk.add hkk, hgc.add hkc, ?_⟩
    · filter_upwards [Lp.coeFn_add f h, hfg, hhk] with z he hg hk
      simpa [hg, hk] using he
    · exact (tsupport_add g k).trans (union_subset hgs hks)
  smul_mem' := by
    rintro c f ⟨g, hfg, hgk, hgc, hgs⟩
    refine ⟨c • g, ?_, ?_, hgc.const_smul c, ?_⟩
    · filter_upwards [Lp.coeFn_smul c f, hfg] with z he hg
      simpa [hg] using he
    · exact hgk.smul_left (f := fun _ => c)
    · exact (tsupport_smul_subset_right (fun _ => c) g).trans hgs

theorem testDomain_dense (N : ℕ) : Dense (testDomain N : Set (SectorHilbert N)) :=
  OpenChartTestDomain.dense_compact_contDiff_inside physicalChart (numberMeasure N) (by norm_num)

abbrev FockHilbert := PiLp 2 (fun word : Occupation => SectorHilbert word.card)
instance fock_complete : CompleteSpace FockHilbert := inferInstance
instance fock_inner : InnerProductSpace ℂ FockHilbert := inferInstance

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

#print axioms source_jacobian_pos
#print axioms relative_source
#print axioms jacobian_source
#print axioms relativeMatrix_smooth
#print axioms coordinate_finrank
#print axioms sourcePoint
#print axioms numberWeight_pos
#print axioms fockTestDomain_dense
end LowEnergy.GaussHistoryHilbert
