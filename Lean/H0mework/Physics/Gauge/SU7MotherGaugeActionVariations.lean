import H0mework.Physics.Gauge.SU7MotherGaugeAction
import H0mework.Physics.Gauge.NonzeroSourceGaugeStationaryConfiguration

/-!
# Stage-5 variations and stationary source lifted through the mother action

Every Stage-5 Fréchet derivative is transferred along the exact P286 block
lift of the mother action.  The positive source therefore supplies a nonzero
stationary mother configuration in all block-lifted field directions.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherGaugeAction

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open SourceRelativePhysicalStationaryFamily
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction

noncomputable section

theorem motherLifted_actual_gravity_connection_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun connection : ConnectionJet =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (q.withGravityConnection connection)))
      (deltaOmega source q.gravity) q.gravity.connection := by
  apply (nonseparable_actual_gravity_connection_derivative
    source boundary q).congr_of_eventuallyEq
  filter_upwards [] with connection
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (q.withGravityConnection connection))

theorem motherLifted_actual_gravity_bivector_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun bivector : BivectorVector =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (q.withGravityBivector bivector)))
      (deltaB source q.gravity) q.gravity.bivector := by
  apply (nonseparable_actual_gravity_bivector_derivative
    source boundary q).congr_of_eventuallyEq
  filter_upwards [] with bivector
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (q.withGravityBivector bivector))

theorem motherLifted_actual_gravity_multiplier_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun multiplier : BivectorVector =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (q.withGravityMultiplier multiplier)))
      (deltaPhi source q.gravity) q.gravity.multiplier := by
  apply (nonseparable_actual_gravity_multiplier_derivative
    source boundary q).congr_of_eventuallyEq
  filter_upwards [] with multiplier
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (q.withGravityMultiplier multiplier))

theorem motherLifted_actual_gravity_tetrad_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun tetrad : TetradVector =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (q.withGravityTetrad tetrad)))
      (nonseparableDeltaTetrad source boundary q) q.gravity.tetrad := by
  apply (nonseparable_actual_gravity_tetrad_derivative
    source boundary q).congr_of_eventuallyEq
  filter_upwards [] with tetrad
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (q.withGravityTetrad tetrad))

theorem motherLifted_actual_selectedGauge_curvature_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun curvature : DynamicGaugeVector =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (withSelectedGaugeCurvature q block curvature)))
      (dynamicGaugeDeltaCurvature source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).curvature := by
  apply (nonseparable_actual_selectedGauge_curvature_derivative
    source boundary q block).congr_of_eventuallyEq
  filter_upwards [] with curvature
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (withSelectedGaugeCurvature q block curvature))

theorem motherLifted_actual_selectedGauge_auxiliary_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun auxiliary : DynamicGaugeVector =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (withSelectedGaugeAuxiliary q block auxiliary)))
      (dynamicGaugeDeltaAuxiliary source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).auxiliary := by
  apply (nonseparable_actual_selectedGauge_auxiliary_derivative
    source boundary q block).congr_of_eventuallyEq
  filter_upwards [] with auxiliary
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (withSelectedGaugeAuxiliary q block auxiliary))

theorem motherLifted_actual_selectedGauge_multiplier_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun multiplier : DynamicGaugeVector =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (liftStageFiveUnifiedConfiguration
            (withSelectedGaugeMultiplier q block multiplier)))
      (dynamicGaugeDeltaMultiplier source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier := by
  apply (nonseparable_actual_selectedGauge_multiplier_derivative
    source boundary q block).congr_of_eventuallyEq
  filter_upwards [] with multiplier
  exact (motherMasterAction_restricts_exactly_to_stageFive source boundary
    (withSelectedGaugeMultiplier q block multiplier))

/-- Every Stage-5 derivative is the derivative of the mother action along
the corresponding block-lifted mother direction. -/
theorem motherLifted_all_stageFive_variations_from_one_action
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
        (fun connection : ConnectionJet =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityConnection connection)))
        (deltaOmega source q.gravity) q.gravity.connection ∧
      HasFDerivAt
        (fun bivector : BivectorVector =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityBivector bivector)))
        (deltaB source q.gravity) q.gravity.bivector ∧
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityMultiplier multiplier)))
        (deltaPhi source q.gravity) q.gravity.multiplier ∧
      HasFDerivAt
        (fun tetrad : TetradVector =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityTetrad tetrad)))
        (nonseparableDeltaTetrad source boundary q) q.gravity.tetrad ∧
      ∀ block : GaugeBlock,
        HasFDerivAt
            (fun curvature : DynamicGaugeVector =>
              motherMasterAction source (motherBoundaryOfStageFive boundary)
                (liftStageFiveUnifiedConfiguration
                  (withSelectedGaugeCurvature q block curvature)))
            (dynamicGaugeDeltaCurvature source q.gravity.tetrad
              (selectedGaugeCoupling boundary block)
              (selectedGaugeConfiguration q.gauge block))
            (selectedGaugeConfiguration q.gauge block).curvature ∧
          HasFDerivAt
            (fun auxiliary : DynamicGaugeVector =>
              motherMasterAction source (motherBoundaryOfStageFive boundary)
                (liftStageFiveUnifiedConfiguration
                  (withSelectedGaugeAuxiliary q block auxiliary)))
            (dynamicGaugeDeltaAuxiliary source q.gravity.tetrad
              (selectedGaugeCoupling boundary block)
              (selectedGaugeConfiguration q.gauge block))
            (selectedGaugeConfiguration q.gauge block).auxiliary ∧
          HasFDerivAt
            (fun multiplier : DynamicGaugeVector =>
              motherMasterAction source (motherBoundaryOfStageFive boundary)
                (liftStageFiveUnifiedConfiguration
                  (withSelectedGaugeMultiplier q block multiplier)))
            (dynamicGaugeDeltaMultiplier source q.gravity.tetrad
              (selectedGaugeCoupling boundary block)
              (selectedGaugeConfiguration q.gauge block))
            (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier :=
  ⟨motherLifted_actual_gravity_connection_derivative source boundary q,
    motherLifted_actual_gravity_bivector_derivative source boundary q,
    motherLifted_actual_gravity_multiplier_derivative source boundary q,
    motherLifted_actual_gravity_tetrad_derivative source boundary q,
    fun block =>
      ⟨motherLifted_actual_selectedGauge_curvature_derivative
          source boundary q block,
        motherLifted_actual_selectedGauge_auxiliary_derivative
          source boundary q block,
        motherLifted_actual_selectedGauge_multiplier_derivative
          source boundary q block⟩⟩

def sourceMotherLiftedConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    SU7MotherUnifiedConfiguration :=
  liftStageFiveUnifiedConfiguration
    (sourceNonseparableConfiguration source boundary)

/-- The source-generated Stage-5 stationary point remains an actual
stationary point of the mother action in every block-lifted field direction.
-/
theorem sourceMotherLifted_all_actual_zero_derivatives
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceNonseparableConfiguration source boundary
    HasFDerivAt
        (fun connection : ConnectionJet =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityConnection connection)))
        (0 : ConnectionJet →L[ℝ] ℝ) q.gravity.connection ∧
      HasFDerivAt
        (fun bivector : BivectorVector =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityBivector bivector)))
        (0 : BivectorVector →L[ℝ] ℝ) q.gravity.bivector ∧
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityMultiplier multiplier)))
        (0 : BivectorVector →L[ℝ] ℝ) q.gravity.multiplier ∧
      HasFDerivAt
        (fun tetrad : TetradVector =>
          motherMasterAction source (motherBoundaryOfStageFive boundary)
            (liftStageFiveUnifiedConfiguration
              (q.withGravityTetrad tetrad)))
        (0 : TetradVector →L[ℝ] ℝ) q.gravity.tetrad ∧
      ∀ block : GaugeBlock,
        HasFDerivAt
            (fun curvature : DynamicGaugeVector =>
              motherMasterAction source (motherBoundaryOfStageFive boundary)
                (liftStageFiveUnifiedConfiguration
                  (withSelectedGaugeCurvature q block curvature)))
            (0 : GaugeCovector)
            (selectedGaugeConfiguration q.gauge block).curvature ∧
          HasFDerivAt
            (fun auxiliary : DynamicGaugeVector =>
              motherMasterAction source (motherBoundaryOfStageFive boundary)
                (liftStageFiveUnifiedConfiguration
                  (withSelectedGaugeAuxiliary q block auxiliary)))
            (0 : GaugeCovector)
            (selectedGaugeConfiguration q.gauge block).auxiliary ∧
          HasFDerivAt
            (fun multiplier : DynamicGaugeVector =>
              motherMasterAction source (motherBoundaryOfStageFive boundary)
                (liftStageFiveUnifiedConfiguration
                  (withSelectedGaugeMultiplier q block multiplier)))
            (0 : GaugeCovector)
            (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier := by
  dsimp only
  let q := sourceNonseparableConfiguration source boundary
  have stationary :=
    source_generates_nonseparableStationaryConfiguration source boundary
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (motherLifted_actual_gravity_connection_derivative
      source boundary q).congr_fderiv stationary.gravity_connection_zero
  · exact (motherLifted_actual_gravity_bivector_derivative
      source boundary q).congr_fderiv stationary.gravity_bivector_zero
  · exact (motherLifted_actual_gravity_multiplier_derivative
      source boundary q).congr_fderiv stationary.gravity_multiplier_zero
  · exact (motherLifted_actual_gravity_tetrad_derivative
      source boundary q).congr_fderiv stationary.total_tetrad_zero
  · intro block
    exact
      ⟨(motherLifted_actual_selectedGauge_curvature_derivative
          source boundary q block).congr_fderiv
            (stationary.gauge_curvature_zero block),
        (motherLifted_actual_selectedGauge_auxiliary_derivative
          source boundary q block).congr_fderiv
            (stationary.gauge_auxiliary_zero block),
        (motherLifted_actual_selectedGauge_multiplier_derivative
          source boundary q block).congr_fderiv
            (stationary.gauge_multiplier_zero block)⟩

theorem positiveSource_motherLifted_strongCurvature_ne_zero
    (boundary : EmpiricalReferenceScaleCouplings) :
    (fun pair => motherColorCoordinate
      (motherCurvature
        (sourceMotherLiftedConfiguration positiveSource boundary).gauge.connection
        pair)) ≠ 0 := by
  simpa [sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration]
    using positiveSource_nonseparable_strongCurvature_ne_zero boundary

/-- A nonzero stationary point of the mother action, witnessed at the actual
positive source. -/
theorem positiveSource_generates_nonzero_motherLiftedStationaryConfiguration
    (boundary : EmpiricalReferenceScaleCouplings) :
    (let q := sourceNonseparableConfiguration positiveSource boundary;
      HasFDerivAt
          (fun connection : ConnectionJet =>
            motherMasterAction positiveSource
              (motherBoundaryOfStageFive boundary)
              (liftStageFiveUnifiedConfiguration
                (q.withGravityConnection connection)))
          (0 : ConnectionJet →L[ℝ] ℝ) q.gravity.connection ∧
        (∀ block : GaugeBlock,
          HasFDerivAt
              (fun curvature : DynamicGaugeVector =>
                motherMasterAction positiveSource
                  (motherBoundaryOfStageFive boundary)
                  (liftStageFiveUnifiedConfiguration
                    (withSelectedGaugeCurvature q block curvature)))
              (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).curvature)) ∧
      (fun pair => motherColorCoordinate
        (motherCurvature
          (sourceMotherLiftedConfiguration positiveSource boundary).gauge.connection
          pair)) ≠ 0 := by
  have stationary :=
    sourceMotherLifted_all_actual_zero_derivatives positiveSource boundary
  exact ⟨⟨stationary.1, fun block => stationary.2.2.2.2 block |>.1⟩,
    positiveSource_motherLifted_strongCurvature_ne_zero boundary⟩


end
end SaturationMonoid.PhysicsCore.SU7MotherGaugeAction
