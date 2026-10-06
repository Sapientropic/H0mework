import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFullCoordinates
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCutoff
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalFormPreparation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationScalarCoordinates
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open PreparationCoordinates CanonicalPreparationCutoff
open MeasureTheory Set Function Filter
open GaussHistoryHilbert (physicalChart)
open CanonicalGradedSpatial (Localizer)
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open CanonicalScalarPreparation CanonicalPreparationCore.Completed
open CanonicalPreparationCreation CanonicalGradedSpatialSource
open SaturationMonoid.Quantum.Forms
open scoped Topology ContDiff Distributions ENNReal LinearPMap

theorem actual_flat_source : fullCoordinates GaussHistoryHilbert.sourcePoint.val=flatSource := by
  rw [actual_sourcePoint_100]
  ext i
  fin_cases i <;> simp [joinCoordinates,flatSource,sourceGauge33,neg_div,source_gauge_scale]

def nativePsi (z : SourceCoordinateSlice) : ℝ := sourcePsi (fullCoordinates z)

theorem nativePsi_smooth : ContDiff ℝ ∞ nativePsi :=
  sourcePsi_smooth.comp fullCoordinates.contDiff

theorem nativePsi_compact : HasCompactSupport nativePsi :=
  sourcePsi_compact.comp_homeomorph fullCoordinates.toHomeomorph

theorem nativePsi_support : support nativePsi=fullCoordinates ⁻¹' sourceOpenBox := by
  rw [← sourcePsi_support]
  rfl

theorem nativePsi_tsupport : tsupport nativePsi ⊆ fullCoordinates ⁻¹' sourceClosedBox := by
  change tsupport (sourcePsi ∘ fullCoordinates.toHomeomorph) ⊆ _
  rw [tsupport_comp_eq_preimage]
  apply preimage_mono
  rw [tsupport,sourcePsi_support]
  exact closure_minimal (fun _ h i => (h i).le) sourceClosedBox_closed

theorem nativePsi_at_source : nativePsi GaussHistoryHilbert.sourcePoint.val=1 := by
  rw [nativePsi,actual_flat_source,sourcePsi_at_source]


theorem decoded_coframe (z : FlatConfiguration) (i : Fin 6) :
    (fullCoordinates.symm z).1 i=z ⟨i.val,by omega⟩ := rfl

theorem decoded_firstGauge (z : FlatConfiguration) :
    GaussHistoryHilbert.firstGauge (fullCoordinates.symm z).2.2.val=z 67 := by
  have h := congrFun (decode_original_rows (splitCoordinates z).2.2) 1
  exact h

theorem decoded_secondGauge (z : FlatConfiguration) :
    GaussHistoryHilbert.secondGauge (fullCoordinates.symm z).2.2.val=z 77 := by
  have h := congrFun (decode_original_rows (splitCoordinates z).2.2) 12
  exact h

private theorem source_coframe_positive (z : FlatConfiguration) (inside : z ∈ sourceClosedBox)
    (i : Fin 100) (source : flatSource i=1) : 0<z i := by
  have low := (abs_le.mp (inside i)).1
  rw [source] at low
  linarith [radius_small.2]

private theorem source_gauge_positive (z : FlatConfiguration) (inside : z ∈ sourceClosedBox)
    (i : Fin 100) (source : flatSource i=3*Real.sqrt 2/10) : 0<z i := by
  have low := (abs_le.mp (inside i)).1
  rw [source] at low
  have sqrtAtLeast : 1≤Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ),Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  linarith [radius_small.2]

theorem original_positive_guards (z : FlatConfiguration) (inside : z ∈ sourceClosedBox) :
    0<(fullCoordinates.symm z).1 0 ∧ 0<(fullCoordinates.symm z).1 2 ∧
    0<(fullCoordinates.symm z).1 5 ∧
    0<GaussHistoryHilbert.firstGauge (fullCoordinates.symm z).2.2.val ∧
    0<GaussHistoryHilbert.secondGauge (fullCoordinates.symm z).2.2.val := by
  rw [decoded_coframe,decoded_coframe,decoded_coframe,decoded_firstGauge,decoded_secondGauge]
  exact ⟨source_coframe_positive z inside 0 (by simp [flatSource]),
    source_coframe_positive z inside 2 (by simp [flatSource]),
    source_coframe_positive z inside 5 (by simp [flatSource]),
    source_gauge_positive z inside 67 (by simp [flatSource]),
    source_gauge_positive z inside 77 (by simp [flatSource])⟩

/-- The remaining two original guard mouths returned to the source majorants. -/
def ResidualChartGuard : Prop :=
  ∀ z ∈ sourceClosedBox,
    (fullCoordinates.symm z).2.1 ∈ SourceQuantumScalarChart.scalarChart ∧
      0<GaussHistoryHilbert.jacobian (fullCoordinates.symm z).2.2.val

/-- The return mouth for the original majorant/first-exit producer. -/
def SourceChartGuard : Prop :=
  ∀ z ∈ sourceClosedBox, fullCoordinates.symm z ∈ (physicalChart : Set SourceCoordinateSlice)

theorem sourceChartGuard_of_residual (residual : ResidualChartGuard) : SourceChartGuard := by
  intro z inside
  have pos := original_positive_guards z inside
  have rem := residual z inside
  exact ⟨pos.1,pos.2.1,pos.2.2.1,rem.1,pos.2.2.2.1,pos.2.2.2.2,rem.2⟩

def nativeLocalizer (guard : SourceChartGuard) : Localizer where
  toFun := nativePsi
  contDiff' := nativePsi_smooth
  hasCompactSupport' := nativePsi_compact
  tsupport_subset' := by
    intro z hz
    have inside := nativePsi_tsupport hz
    have generated := guard (fullCoordinates z) inside
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using generated

theorem nativeLocalizer_at_source (guard : SourceChartGuard) :
    nativeLocalizer guard GaussHistoryHilbert.sourcePoint.val=1 := nativePsi_at_source

theorem original_localized_space_nontrivial (guard : SourceChartGuard) :
    Nontrivial (CanonicalPreparationCore.Completed.zeroLocalizedSpace (nativeLocalizer guard)) :=
  CanonicalFormPreparation.localized_nontrivial _ (by rw [nativeLocalizer_at_source]; norm_num)

-- Exact original measure transported through the generated coordinate map.
def nativeFlatMeasure : Measure FlatConfiguration :=
  GaussHistoryHilbert.configurationMeasure.map fullCoordinates

theorem native_measure_return : nativeFlatMeasure.comap fullCoordinates=
    GaussHistoryHilbert.configurationMeasure :=
  fullCoordinates.toHomeomorph.measurableEmbedding.comap_map _

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem source_form_to_created_state (guard : SourceChartGuard)
    (A : zeroLocalizedSpace (nativeLocalizer guard) →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set (zeroLocalizedSpace (nativeLocalizer guard))))
    (R : zeroLocalizedSpace (nativeLocalizer guard) →L[ℂ] zeroLocalizedSpace (nativeLocalizer guard)) (selfAdjoint : IsSelfAdjoint R)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ x : (BoundedRemainder.operator A closed dense R).domain,
      ‖prepared (zeroLocalizedProfile (nativeLocalizer guard) x.val)‖=1 ∧
      ‖BoundedRemainder.operator A closed dense R x-(BoundedRemainder.energy A closed R : ℂ) • x.val‖<epsilon ∧
      prepared (zeroLocalizedProfile (nativeLocalizer guard) x.val)=
        sourceCreated (GaussHalfDensity.halfDensityEquiv 0 x.val.val) ∧
      (∀ y : A.domain, inner ℂ (BoundedRemainder.operator A closed dense R x) y.val=
        inner ℂ (A (BoundedRemainder.factorPoint A closed dense R x)) (A y)+
          inner ℂ x.val (R y.val)) ∧
      inner ℂ (prepared (zeroLocalizedProfile (nativeLocalizer guard) x.val))
        (CanonicalGradedCharge.chargeReader GaussComposite.nativeY
          (prepared (zeroLocalizedProfile (nativeLocalizer guard) x.val)))=-1 ∧
      (∀ (addition : Bool) (a s : Fin 2),
        ‖completedLeg addition a s (zeroLocalizedProfile (nativeLocalizer guard) x.val)‖≤
          legBound*localBound (outerCutoff (nativeLocalizer guard))) ∧
      ∀ (p k : PhysicalMomentum) (q : SourceQuantumScalarChart.NativeLie)
        (cut : ℕ) (z w : ℂ) (hz : 0<z.im) (hw : 0<w.im)
        (left right : Bool) (a s b t : Fin 2),
        Tendsto (fun ts : ℝ×ℝ => CanonicalPreparedFrequency.timeRead p k q cut z w
          (ne_of_gt hz) (ne_of_gt hw) ts.1 ts.2 left right a s b t
          (zeroLocalizedProfile (nativeLocalizer guard) x.val) (zeroLocalizedProfile (nativeLocalizer guard) x.val)) (atTop×ˢatTop)
          (𝓝 (CanonicalPreparedFrequency.frequencyRead p k q cut z w
            (ne_of_gt hz) (ne_of_gt hw) left right a s b t
            (zeroLocalizedProfile (nativeLocalizer guard) x.val) (zeroLocalizedProfile (nativeLocalizer guard) x.val))) := by
  exact CanonicalFormPreparation.form_to_created_state (nativeLocalizer guard)
    (by rw [nativeLocalizer_at_source]; norm_num) A closed dense R selfAdjoint epsilon positive

end LowEnergy.PreparationScalarCoordinates
