import H0mework.Physics.Gauge.SU7MotherSourceConfiguration
import H0mework.Physics.Gauge.SU7MotherFullGaugeStationarity
import H0mework.Physics.Admission.NonseparablePhysicalUnifiedAdmissionCredential

/-!
# Stage-6 SU(7) mother-connection physical credential

This downstream credential strengthens Stage 5 with one source-generated
SU(7) mother connection and an operational breaking datum.  It aggregates
only already-proved outputs:

* breaking selects exactly the P286 tangent image;
* projected mother curvature is the source P286 target;
* the canonical source mother output projects to the Stage-5 source gauge
  configuration and has zero cross-block penalty;
* the mother action restricts exactly to Stage 5;
* all four mother-gauge fields are stationary in every full `su(7)` matrix
  direction at the source lift;
* a concrete off-block perturbation has positive penalty.

It stores no P286 group certificate, P523 receipt, endpoint atomhood, Boolean
atomicity, or primitive law.  Exact P506/L0 lineage and endpoint `11` remain
in the separate narrow lineage-admission module.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherPhysicalUnifiedAdmission

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7MotherGaugeAction
open SU7MotherSourceConfiguration
open SU7MotherFullGaugeStationarity
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration
open NonseparablePhysicalUnifiedAdmission
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction

noncomputable section

structure SU7MotherPhysicalUnifiedAdmissionCredential
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) where
  stageFive :
    NonseparablePhysicalUnifiedAdmissionCredential source boundary
  breakingDatum : SU7SourceBreakingDatum
  breakingDatum_eq_source : breakingDatum = sourceBreakingDatum source
  sourceMother : SU7MotherUnifiedConfiguration
  sourceMother_eq_generated :
    sourceMother = sourceGeneratedMotherUnifiedConfiguration source boundary
  selectedConnection : SourceSelectedMotherConnection source
  selectedConnection_eq_source :
    selectedConnection = sourceSelectedMotherConnection source
  operational_breaking_exact : ∀ matrix : SU7MotherLieMatrix,
    SelectedBySourceBreaking source matrix ↔
      ∃ data : P286LieBlockData, p286LieBlockEmbed data = matrix
  source_curvature_projection_exact : ∀ pair : Fin 6,
    p286BlockCurvature
        (projectSelectedMotherConnection source selectedConnection) pair =
      sourceP286TargetCurvature source pair
  stageFive_projection_exact :
    projectMotherGaugeConfiguration sourceMother.gauge =
      sourceStandardModelGaugeConfiguration source boundary
  source_breaking_penalty_zero :
    motherBreakingPenalty sourceMother.gauge = 0
  exact_stageFive_restriction : ∀ q : UnifiedConfiguration,
    motherMasterAction source (motherBoundaryOfStageFive boundary)
        (liftStageFiveUnifiedConfiguration q) =
      nonseparableMasterAction source boundary q
  full_mother_gauge_stationary :
    FullSU7MotherGaugeStationary source boundary
  offBlock_perturbation_detected : ∀ q : StandardModelGaugeConfiguration,
    0 < motherBreakingPenalty
      (addOffBlockExteriorPerturbation
        (liftStageFiveGaugeConfiguration q))

def su7MotherPhysicalCredentialOf
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (stageFive :
      NonseparablePhysicalUnifiedAdmissionCredential source boundary) :
    SU7MotherPhysicalUnifiedAdmissionCredential source boundary where
  stageFive := stageFive
  breakingDatum := sourceBreakingDatum source
  breakingDatum_eq_source := rfl
  sourceMother := sourceGeneratedMotherUnifiedConfiguration source boundary
  sourceMother_eq_generated := rfl
  selectedConnection := sourceSelectedMotherConnection source
  selectedConnection_eq_source := rfl
  operational_breaking_exact := fun matrix =>
    selectedBySourceBreaking_iff_p286LieBlockImage source matrix
  source_curvature_projection_exact := fun pair =>
    sourceProjectedMother_curvature_eq_target source pair
  stageFive_projection_exact :=
    project_sourceGeneratedMotherGaugeConfiguration source boundary
  source_breaking_penalty_zero :=
    sourceGeneratedMother_breakingPenalty_zero source boundary
  exact_stageFive_restriction := fun q =>
    motherMasterAction_restricts_exactly_to_stageFive source boundary q
  full_mother_gauge_stationary :=
    source_generates_fullSU7MotherGaugeStationary source boundary
  offBlock_perturbation_detected := fun q =>
    motherBreakingPenalty_offBlockPerturbation_pos q

def positiveSU7MotherPhysicalUnifiedAdmissionCredential :
    SU7MotherPhysicalUnifiedAdmissionCredential positiveSource unitBoundary :=
  su7MotherPhysicalCredentialOf positiveSource unitBoundary
    positiveNonseparablePhysicalUnifiedAdmissionCredential

theorem positiveSource_generates_SU7MotherPhysicalCredential :
    Nonempty
      (SU7MotherPhysicalUnifiedAdmissionCredential
        positiveSource unitBoundary) :=
  ⟨positiveSU7MotherPhysicalUnifiedAdmissionCredential⟩

/-- The positive Stage-5 nonzero stationary point is an actual stationary
point of the Stage-6 mother action in every block-lifted field direction. -/
theorem positiveSU7Mother_nonzeroStationaryLift :
    (let q := sourceNonseparableConfiguration positiveSource unitBoundary;
      HasFDerivAt
          (fun connection : ConnectionJet =>
            motherMasterAction positiveSource
              (motherBoundaryOfStageFive unitBoundary)
              (liftStageFiveUnifiedConfiguration
                (q.withGravityConnection connection)))
          (0 : ConnectionJet →L[ℝ] ℝ) q.gravity.connection ∧
        (∀ block : GaugeBlock,
          HasFDerivAt
              (fun curvature : DynamicGaugeVector =>
                motherMasterAction positiveSource
                  (motherBoundaryOfStageFive unitBoundary)
                  (liftStageFiveUnifiedConfiguration
                    (withSelectedGaugeCurvature q block curvature)))
              (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).curvature)) ∧
      (fun pair => motherColorCoordinate
        (motherCurvature
          (sourceMotherLiftedConfiguration
            positiveSource unitBoundary).gauge.connection pair)) ≠ 0 :=
  positiveSource_generates_nonzero_motherLiftedStationaryConfiguration
    unitBoundary

/-- The definitive Stage-6 stationarity certificate: every matrix direction
of each mother-gauge field is included, and the positive source curvature is
nonzero. -/
theorem positiveSU7Mother_nonzeroFullGaugeStationary :
    FullSU7MotherGaugeStationary positiveSource unitBoundary ∧
      (fun pair => motherColorCoordinate
        (motherCurvature
          (sourceMotherLiftedConfiguration
            positiveSource unitBoundary).gauge.connection pair)) ≠ 0 :=
  positiveSource_generates_nonzero_fullSU7MotherGaugeStationary unitBoundary

end
end SaturationMonoid.PhysicsCore.SU7MotherPhysicalUnifiedAdmission
