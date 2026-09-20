import H0mework.Physics.Admission.PhysicalDynamicsAdmissionCredential
import H0mework.Physics.Coframe.NonseparableSourceCoframeRegression

/-!
# Stage-5 nonseparable physical admission credential

The dependency-light Stage-4 physical dynamics credential remains the
compatibility boundary for the pre-P950 adapter.  This stronger credential
adds only post-source theorems:

* one live source tetrad generates the three gauge Hodge/volume/operators;
* every finite field coordinate is an actual derivative of the same
  nonseparable master action;
* the exact source configuration is stationary with nonzero gauge curvature;
* a separate live configuration has nonzero gauge stress;
* an intentionally mismatched coframe is rejected.

No stationarity law, gauge field, endpoint atomhood, or empirical coupling is
added to the raw source datum.
-/

namespace SaturationMonoid.PhysicsCore.NonseparablePhysicalUnifiedAdmission

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceGeneratedPhysicalPlebanskiConfiguration
open EmpiricalReferenceScaleCouplingBoundary
open PhysicalUnifiedAdmission
open UnifiedPhysicalMasterAction
open DynamicTetradGaugeGeometry
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration
open NonseparableSourceCoframeRegression

noncomputable section

/-- Stage-5 credential.  The nonzero-curvature hypothesis is an independently
proved source output; it is not a field equation or a stored stationary point.
-/
structure NonseparablePhysicalUnifiedAdmissionCredential
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) where
  stageFour : PhysicalDynamicsAdmissionCredential source boundary
  sourceGaugeCurvature_nonzero : sourceGaugeCurvature source ≠ 0
  shared_dynamic_geometry :
    (dynamicGaugeConstitutiveBlock source (tetradVectorAtOrigin source)
        boundary).spacetimeHodge =
        dynamicGaugeHodgeEquiv source (tetradVectorAtOrigin source) ∧
      dynamicStrongOperator source (tetradVectorAtOrigin source) boundary =
        hodgeConstitutiveOperator
          (dynamicGaugeHodgeEquiv source (tetradVectorAtOrigin source))
          boundary.strongCouplingSquared ∧
      dynamicWeakOperator source (tetradVectorAtOrigin source) boundary =
        hodgeConstitutiveOperator
          (dynamicGaugeHodgeEquiv source (tetradVectorAtOrigin source))
          boundary.weakCouplingSquared ∧
      dynamicHyperchargeOperator source (tetradVectorAtOrigin source) boundary =
        hodgeConstitutiveOperator
          (dynamicGaugeHodgeEquiv source (tetradVectorAtOrigin source))
          boundary.hyperchargeCouplingSquared
  exact_source_geometry_admission :
    ExactSourceGaugeGeometryAdmission source boundary
      (sourceNonseparableConfiguration source boundary)
  stationary_nonseparable_action :
    NonseparablePhysicalStationaryAtSource source boundary
      (sourceNonseparableConfiguration source boundary)
  all_actual_zero_derivatives :
    let q := sourceNonseparableConfiguration source boundary
    HasFDerivAt
        (fun connection : ConnectionJet =>
          nonseparableMasterAction source boundary
            (q.withGravityConnection connection))
        (0 : ConnectionJet →L[ℝ] ℝ) q.gravity.connection ∧
      HasFDerivAt
        (fun bivector : BivectorVector =>
          nonseparableMasterAction source boundary
            (q.withGravityBivector bivector))
        (0 : BivectorVector →L[ℝ] ℝ) q.gravity.bivector ∧
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          nonseparableMasterAction source boundary
            (q.withGravityMultiplier multiplier))
        (0 : BivectorVector →L[ℝ] ℝ) q.gravity.multiplier ∧
      HasFDerivAt
        (fun tetrad : TetradVector =>
          nonseparableMasterAction source boundary
            (q.withGravityTetrad tetrad))
        (0 : TetradVector →L[ℝ] ℝ) q.gravity.tetrad ∧
      ∀ block : GaugeBlock,
        HasFDerivAt
            (fun curvature : DynamicGaugeVector =>
              nonseparableMasterAction source boundary
                (withSelectedGaugeCurvature q block curvature))
            (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).curvature ∧
          HasFDerivAt
            (fun auxiliary : DynamicGaugeVector =>
              nonseparableMasterAction source boundary
                (withSelectedGaugeAuxiliary q block auxiliary))
            (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).auxiliary ∧
          HasFDerivAt
            (fun multiplier : DynamicGaugeVector =>
              nonseparableMasterAction source boundary
                (withSelectedGaugeMultiplier q block multiplier))
            (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier
  live_gauge_stress_nonzero :
    dynamicGaugeStressCovector source (tetradVectorAtOrigin source) (1 : ℝˣ)
      (gaugeStressProbeConfiguration source) ≠ 0
  mismatched_coframe_rejected :
    ¬ ExactSourceGaugeGeometryAdmission source boundary
      (mismatchedCoframeConfiguration source boundary)

def nonseparablePhysicalCredentialOf
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (stageFour : PhysicalDynamicsAdmissionCredential source boundary)
    (hcurvature : sourceGaugeCurvature source ≠ 0) :
    NonseparablePhysicalUnifiedAdmissionCredential source boundary where
  stageFour := stageFour
  sourceGaugeCurvature_nonzero := hcurvature
  shared_dynamic_geometry :=
    all_three_operators_share_dynamicHodge source
      (tetradVectorAtOrigin source) boundary
  exact_source_geometry_admission :=
    sourceNonseparableConfiguration_exactAdmission source boundary
  stationary_nonseparable_action :=
    source_generates_nonseparableStationaryConfiguration source boundary
  all_actual_zero_derivatives :=
    sourceNonseparable_all_actual_zero_derivatives source boundary
  live_gauge_stress_nonzero := gaugeStressProbe_covector_ne_zero source
  mismatched_coframe_rejected :=
    mismatchedCoframeConfiguration_rejected source boundary

def positiveNonseparablePhysicalUnifiedAdmissionCredential :
    NonseparablePhysicalUnifiedAdmissionCredential positiveSource unitBoundary :=
  nonseparablePhysicalCredentialOf positiveSource unitBoundary
    positivePhysicalDynamicsAdmissionCredential
    positiveSource_sourceGaugeCurvature_ne_zero

theorem positiveSource_generates_nonseparablePhysicalUnifiedAdmissionCredential :
    Nonempty
      (NonseparablePhysicalUnifiedAdmissionCredential
        positiveSource unitBoundary) :=
  ⟨positiveNonseparablePhysicalUnifiedAdmissionCredential⟩

theorem positiveStageFive_action_not_additively_separable :
    ¬ AdditivelyGravityGaugeSeparable
      (nonseparableMasterAction positiveSource unitBoundary) :=
  nonseparableMasterAction_not_additively_separable positiveSource

theorem positiveStageFive_mixedDifference_eq_nine :
    gravityGaugeMixedDifference positiveSource = 9 :=
  gravityGaugeMixedDifference_eq_nine positiveSource

end
end SaturationMonoid.PhysicsCore.NonseparablePhysicalUnifiedAdmission
