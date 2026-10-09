import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRemainder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourcePreparedState
open PreparationVacuumRawTableBounds PreparationVacuumPreparedTail PreparationVacuumTailOperator PreparationVacuumTailSupport
open PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalGradedSpatialSource
open CanonicalGradedSpatial (Localizer)
open SaturationMonoid.Quantum.Forms
open Filter
open scoped Topology ContDiff LinearPMap

-- Every field concerns the same source-generated operator-domain point.
structure SourcePreparation (epsilon : ℝ) where
  point : sourceOperator.domain
  unit : ‖prepared (zeroLocalizedProfile actualNativeLocalizer point.val)‖=1
  near : ‖sourceOperator point-(sourceEnergy : ℂ) • point.val‖<epsilon
  created : prepared (zeroLocalizedProfile actualNativeLocalizer point.val)=
    sourceCreated (GaussHalfDensity.halfDensityEquiv 0 point.val.val)
  form : ∀ y : sourceClosedFactor.domain,inner ℂ (sourceOperator point) y.val=
    inner ℂ (sourceClosedFactor (sourceFactorPoint point)) (sourceClosedFactor y)+inner ℂ point.val (sourceRemainder y.val)
  charge : inner ℂ (prepared (zeroLocalizedProfile actualNativeLocalizer point.val))
    (CanonicalGradedCharge.chargeReader GaussComposite.nativeY (prepared (zeroLocalizedProfile actualNativeLocalizer point.val)))=-1
  legs : ∀ (addition : Bool) (a s : Fin 2),
    ‖completedLeg addition a s (zeroLocalizedProfile actualNativeLocalizer point.val)‖≤
      legBound*localBound (outerCutoff actualNativeLocalizer)
  frequency : ∀ (p k : PhysicalMomentum) (q : SourceQuantumScalarChart.NativeLie)
    (cut : ℕ) (z w : ℂ) (hz : 0<z.im) (hw : 0<w.im) (left right : Bool) (a s b t : Fin 2),
    Tendsto (fun ts : ℝ×ℝ => CanonicalPreparedFrequency.timeRead p k q cut z w
      (ne_of_gt hz) (ne_of_gt hw) ts.1 ts.2 left right a s b t
      (zeroLocalizedProfile actualNativeLocalizer point.val) (zeroLocalizedProfile actualNativeLocalizer point.val)) (atTop×ˢatTop)
      (𝓝 (CanonicalPreparedFrequency.frequencyRead p k q cut z w
        (ne_of_gt hz) (ne_of_gt hw) left right a s b t
        (zeroLocalizedProfile actualNativeLocalizer point.val) (zeroLocalizedProfile actualNativeLocalizer point.val)))
  yukawaDomain : prepared (zeroLocalizedProfile actualNativeLocalizer point.val)∈GaussRadialDomain.closedY.domain
  yukawaValue : GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer point.val),yukawaDomain⟩=preparedY point.val
  yukawaCutoff : ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer point.val),yukawaDomain⟩-
    FullYSourceCutoffVolterra.cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer point.val))‖ ≤
      (915/916 : ℝ)^(n+1)*916*GaussYukawaCoefficient.bound
  yukawaLimit : Tendsto (fun n : ℕ=>FullYSourceCutoffVolterra.cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer point.val)))
    atTop (𝓝 (preparedY point.val))

theorem sourcePreparation_exists (epsilon : ℝ) (precision : 0<epsilon) : Nonempty (SourcePreparation epsilon) := by
  obtain ⟨x,unit,near,created,form,charge,legs,frequency⟩:=
    source_form_to_created_state actual_source_chart_guard sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
      sourceRemainder sourceRemainder_selfAdjoint epsilon precision
  obtain ⟨domain,value,estimate⟩:=original_prepared_Y_domain x.val
  have norm : ‖x.val‖=1 := (zeroLocalized_physical_norm actualNativeLocalizer x.val).symm.trans unit
  refine ⟨⟨x,unit,near,created,form,charge,legs,frequency,domain,value,?_,?_⟩⟩
  · intro n
    simpa only [norm,mul_one] using estimate n
  · exact prepared_cutoff_tendsto x.val

def sourcePreparation (epsilon : ℝ) (precision : 0<epsilon) : SourcePreparation epsilon :=
  Classical.choice (sourcePreparation_exists epsilon precision)

-- This is the original full-Y preparation mouth with all upstream B/Unit102
-- responsibilities discharged, and its witness retains the full CAR/form data.
theorem actual_source_full_tail_preparation_Y (epsilon : ℝ) (precision : 0<epsilon) :
    ∃ x : sourceOperator.domain,
      ‖prepared (zeroLocalizedProfile actualNativeLocalizer x.val)‖=1 ∧
      ‖sourceOperator x-(sourceEnergy : ℂ) • x.val‖<epsilon ∧
      prepared (zeroLocalizedProfile actualNativeLocalizer x.val)=sourceCreated (GaussHalfDensity.halfDensityEquiv 0 x.val.val) ∧
      ∃ h : prepared (zeroLocalizedProfile actualNativeLocalizer x.val)∈GaussRadialDomain.closedY.domain,
        ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer x.val),h⟩-
          FullYSourceCutoffVolterra.cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer x.val))‖ ≤
            (915/916 : ℝ)^(n+1)*916*GaussYukawaCoefficient.bound := by
  let generated:=sourcePreparation epsilon precision
  exact ⟨generated.point,generated.unit,generated.near,generated.created,generated.yukawaDomain,generated.yukawaCutoff⟩

end LowEnergy.PreparationVacuumSourcePreparedState
