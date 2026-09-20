import H0mework.Physics.Gauge.NonzeroSourceGaugeStationaryConfiguration

/-!
# Exact source/coframe admission and anti-separability regression

Putting gravity and gauge terms in one scalar expression is not by itself a
coupling theorem.  This module adds two independent guards:

1. an exact source-geometry admission predicate requiring the live tetrad and
   all three gauge backgrounds to match the same source; and
2. a mixed finite-difference witness equal to `9`, which is impossible for an
   action of the form `gravityOnly q.gravity + gaugeOnly q.gauge`.

The deliberately mismatched `timeModeProbe` coframe is rejected even though
it has the same carrier type and can be inserted into the raw configuration
structure.  This prevents type-level co-location from being cited as source
unification.
-/

namespace SaturationMonoid.PhysicsCore.NonseparableSourceCoframeRegression

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceGeneratedPhysicalPlebanskiConfiguration
open SourceRelativePhysicalStationaryFamily
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open DynamicTetradGaugeGeometry
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration

noncomputable section

/-- Admission requires exact source identity at the generated geometry layer,
not merely equal carrier dimensions or membership in one action sum. -/
structure ExactSourceGaugeGeometryAdmission
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) : Prop where
  tetrad_matches_source : q.gravity.tetrad = tetradVectorAtOrigin source
  curvature_matches_source : ∀ block : GaugeBlock,
    (selectedGaugeConfiguration q.gauge block).curvature =
      sourceGaugeCurvature source
  auxiliary_matches_source : ∀ block : GaugeBlock,
    (selectedGaugeConfiguration q.gauge block).auxiliary =
      sourceGaugeAuxiliary source (selectedGaugeCoupling boundary block)

theorem sourceNonseparableConfiguration_exactAdmission
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    ExactSourceGaugeGeometryAdmission source boundary
      (sourceNonseparableConfiguration source boundary) where
  tetrad_matches_source := rfl
  curvature_matches_source := by
    intro block
    cases block <;>
      rfl
  auxiliary_matches_source := by
    intro block
    cases block <;>
      rfl

theorem timeModeProbe_ne_sourceTetrad (source : Source) :
    timeModeProbe source ≠ tetradVectorAtOrigin source := by
  intro hequal
  have hvolume := congrArg (dynamicGaugeVolume source) hequal
  rw [timeModeProbe_volume, dynamicGaugeVolume_at_source] at hvolume
  norm_num at hvolume

def mismatchedCoframeConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    UnifiedConfiguration :=
  (sourceNonseparableConfiguration source boundary).withGravityTetrad
    (timeModeProbe source)

/-- A live tetrad from the wrong coframe state cannot pass exact source
admission, even though the raw configuration constructor accepts it. -/
theorem mismatchedCoframeConfiguration_rejected
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    ¬ ExactSourceGaugeGeometryAdmission source boundary
      (mismatchedCoframeConfiguration source boundary) := by
  intro hadmission
  apply timeModeProbe_ne_sourceTetrad source
  simpa [mismatchedCoframeConfiguration,
    UnifiedConfiguration.withGravityTetrad, Configuration.withTetrad] using
    hadmission.tetrad_matches_source

def sourceBackgroundGaugeConfiguration (source : Source) :
    StandardModelGaugeConfiguration :=
  sourceStandardModelGaugeConfiguration source unitBoundary

def stressProbeStandardModelGaugeConfiguration (source : Source) :
    StandardModelGaugeConfiguration where
  strong := gaugeStressProbeConfiguration source
  weak := sourceGaugeSectorConfiguration source (1 : ℝˣ)
  hypercharge := sourceGaugeSectorConfiguration source (1 : ℝˣ)

def rectangleConfiguration
    (source : Source) (tetrad : TetradVector)
    (gauge : StandardModelGaugeConfiguration) : UnifiedConfiguration where
  gravity := (sourceStationaryConfiguration source).withTetrad tetrad
  gauge := gauge

theorem rectangle_gravity_action_zero
    (source : Source) (tetrad : TetradVector)
    (gauge : StandardModelGaugeConfiguration) :
    sourceRelativeMasterAction source
      (rectangleConfiguration source tetrad gauge).gravity = 0 := by
  exact sourceRelativeAction_withTetrad_eq_zero source tetrad

theorem rectangle_source_background_action (source : Source) :
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (tetradVectorAtOrigin source)
        (sourceBackgroundGaugeConfiguration source)) = 0 := by
  rw [nonseparableMasterAction, rectangle_gravity_action_zero]
  simp [dynamicStandardModelGaugeAction,
    rectangleConfiguration, Configuration.withTetrad,
    sourceBackgroundGaugeConfiguration,
    sourceStandardModelGaugeConfiguration,
    sourceGaugeSector_action_withTetrad_eq_zero, unitBoundary]

theorem rectangle_time_background_action (source : Source) :
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (timeModeProbe source)
        (sourceBackgroundGaugeConfiguration source)) = 0 := by
  rw [nonseparableMasterAction, rectangle_gravity_action_zero]
  simp [dynamicStandardModelGaugeAction,
    rectangleConfiguration, Configuration.withTetrad,
    sourceBackgroundGaugeConfiguration,
    sourceStandardModelGaugeConfiguration,
    sourceGaugeSector_action_withTetrad_eq_zero, unitBoundary]

theorem rectangle_source_stressProbe_action (source : Source) :
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (tetradVectorAtOrigin source)
        (stressProbeStandardModelGaugeConfiguration source)) =
      (3 / 2 : ℝ) := by
  rw [nonseparableMasterAction, rectangle_gravity_action_zero]
  simp [dynamicStandardModelGaugeAction,
    rectangleConfiguration, Configuration.withTetrad,
    stressProbeStandardModelGaugeConfiguration,
    sourceGaugeSector_action_withTetrad_eq_zero, unitBoundary,
    gaugeStressProbe_action_at_source]

theorem rectangle_time_stressProbe_action (source : Source) :
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (timeModeProbe source)
        (stressProbeStandardModelGaugeConfiguration source)) =
      (21 / 2 : ℝ) := by
  rw [nonseparableMasterAction, rectangle_gravity_action_zero]
  simp [dynamicStandardModelGaugeAction,
    rectangleConfiguration, Configuration.withTetrad,
    stressProbeStandardModelGaugeConfiguration,
    sourceGaugeSector_action_withTetrad_eq_zero, unitBoundary,
    gaugeStressProbe_action_at_timeModeProbe]

/-- The mixed rectangle difference isolates the gravity--gauge interaction;
pure gravity and pure gauge summands would cancel. -/
def gravityGaugeMixedDifference (source : Source) : ℝ :=
  nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (timeModeProbe source)
        (stressProbeStandardModelGaugeConfiguration source)) -
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (timeModeProbe source)
        (sourceBackgroundGaugeConfiguration source)) -
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (tetradVectorAtOrigin source)
        (stressProbeStandardModelGaugeConfiguration source)) +
    nonseparableMasterAction source unitBoundary
      (rectangleConfiguration source (tetradVectorAtOrigin source)
        (sourceBackgroundGaugeConfiguration source))

theorem gravityGaugeMixedDifference_eq_nine (source : Source) :
    gravityGaugeMixedDifference source = 9 := by
  rw [gravityGaugeMixedDifference, rectangle_time_stressProbe_action,
    rectangle_time_background_action, rectangle_source_stressProbe_action,
    rectangle_source_background_action]
  norm_num

def AdditivelyGravityGaugeSeparable
    (action : UnifiedConfiguration → ℝ) : Prop :=
  ∃ gravityOnly : Configuration → ℝ,
    ∃ gaugeOnly : StandardModelGaugeConfiguration → ℝ,
      ∀ q, action q = gravityOnly q.gravity + gaugeOnly q.gauge

/-- Machine-level anti-regression: the Stage-5 action cannot be rewritten as
one function of gravity plus one function of gauge coordinates. -/
theorem nonseparableMasterAction_not_additively_separable (source : Source) :
    ¬ AdditivelyGravityGaugeSeparable
      (nonseparableMasterAction source unitBoundary) := by
  rintro ⟨gravityOnly, gaugeOnly, hsplit⟩
  have hzero : gravityGaugeMixedDifference source = 0 := by
    unfold gravityGaugeMixedDifference
    rw [hsplit, hsplit, hsplit, hsplit]
    simp [rectangleConfiguration]
    ring
  rw [gravityGaugeMixedDifference_eq_nine] at hzero
  norm_num at hzero

end
end SaturationMonoid.PhysicsCore.NonseparableSourceCoframeRegression
