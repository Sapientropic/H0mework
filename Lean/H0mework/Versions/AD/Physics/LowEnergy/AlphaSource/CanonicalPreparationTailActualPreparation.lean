import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailNativeOperator
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeCutoff

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPreparedTail
open PreparationVacuumTailOperator PreparationVacuumTailSupport PreparationVacuumNativeClosure
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalGradedSpatialSource
open CanonicalGradedSpatial (Localizer)
open SaturationMonoid.Quantum.Forms
open Filter
open scoped Topology ContDiff LinearPMap
abbrev ArrayBound := ℕ → ℝ

theorem actual_full_tail_preparation (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)
    (epsilon : ℝ) (precision : 0<epsilon) :
    ∃ x : (BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense (completeNativeRemainder B positive input)).domain,
      ‖prepared (zeroLocalizedProfile actualNativeLocalizer x.val)‖=1 ∧
      ‖BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense (completeNativeRemainder B positive input) x-(BoundedRemainder.energy sourceClosedFactor sourceClosedFactor_closed (completeNativeRemainder B positive input) : ℂ) • x.val‖<epsilon ∧
      prepared (zeroLocalizedProfile actualNativeLocalizer x.val)=
        sourceCreated (GaussHalfDensity.halfDensityEquiv 0 x.val.val) ∧
      (∀ y : sourceClosedFactor.domain, inner ℂ (BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense (completeNativeRemainder B positive input) x) y.val=
        inner ℂ (sourceClosedFactor (BoundedRemainder.factorPoint sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense (completeNativeRemainder B positive input) x)) (sourceClosedFactor y)+
          inner ℂ x.val (completeNativeRemainder B positive input y.val)) ∧
      inner ℂ (prepared (zeroLocalizedProfile actualNativeLocalizer x.val))
        (CanonicalGradedCharge.chargeReader GaussComposite.nativeY
          (prepared (zeroLocalizedProfile actualNativeLocalizer x.val)))=-1 ∧
      (∀ (addition : Bool) (a s : Fin 2),
        ‖completedLeg addition a s (zeroLocalizedProfile actualNativeLocalizer x.val)‖≤
          legBound*localBound (outerCutoff actualNativeLocalizer)) ∧
      ∀ (p k : PhysicalMomentum) (q : SourceQuantumScalarChart.NativeLie)
        (cut : ℕ) (z w : ℂ) (hz : 0<z.im) (hw : 0<w.im)
        (left right : Bool) (a s b t : Fin 2),
        Tendsto (fun ts : ℝ×ℝ => CanonicalPreparedFrequency.timeRead p k q cut z w
          (ne_of_gt hz) (ne_of_gt hw) ts.1 ts.2 left right a s b t
          (zeroLocalizedProfile actualNativeLocalizer x.val) (zeroLocalizedProfile actualNativeLocalizer x.val)) (atTop×ˢatTop)
          (𝓝 (CanonicalPreparedFrequency.frequencyRead p k q cut z w
            (ne_of_gt hz) (ne_of_gt hw) left right a s b t
            (zeroLocalizedProfile actualNativeLocalizer x.val) (zeroLocalizedProfile actualNativeLocalizer x.val))) := by
  exact source_form_to_created_state actual_source_chart_guard
    sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
    (completeNativeRemainder B positive input) (completeNativeRemainder_isSelfAdjoint B positive input)
    epsilon precision

end LowEnergy.PreparationVacuumPreparedTail
