import H0mework.Realization.Perfectification.SourceCoimage
import H0mework.Realization.Coherent.EquivariantPerfectAction
import H0mework.Realization.Coherent.Covariance

/-!
# Integral equivariant perfect realization

One source evaluation generates its exact perfect carrier and equivariant
dual action.  An actual Hilbert measurement is then settled without a hidden
compatibility premise.  If the measurement descends through the perfect
carrier, its coherent realization is classified as strictly covariant,
radially neutral with an explicit phase/direction residual, or radially
nonneutral at an actual source coordinate.  If it does not descend, the
source coordinate seen by the measurement but discarded by the evaluation
is retained explicitly.

Thus perfectification transports source action, but never manufactures an
action--measurement square.  No finite generation, projectivity,
determinant, automorphism, unitarity, faithfulness, or residual-vanishing
premise enters the total constructor.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralEquivariantPerfectRealization

noncomputable section

universe c d h

variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [AddCommGroup D]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)
variable (measurement : C →ₗ[ℤ] H)

abbrev PerfectCarrier := SourceGeneratedScalarExactEnvelope.Carrier evaluation

/-- One source action together with the owner-free coherent evolution against
which its actual measurement is read. -/
structure JointActionData where
  sourceAction : SourceGeneratedScalarEquivariantPerfectAction.ActionData evaluation
  coherentEvolution : H →ₗᵢ[ℂ] H

/-- The canonical measurement on the perfect carrier, when the evaluation
kernel is invisible to the actual measurement. -/
def perfectMeasurement
    (kernelCompatibility :
      LinearMap.ker evaluation ≤ LinearMap.ker measurement) :
    PerfectCarrier evaluation →ₗ[ℤ] H :=
  SourceGeneratedScalarPerfectification.canonicalFactor evaluation measurement
    kernelCompatibility

omit [InnerProductSpace ℂ H] in
@[simp] theorem perfectMeasurement_source_readback
    (kernelCompatibility :
      LinearMap.ker evaluation ≤ LinearMap.ker measurement) :
    (perfectMeasurement evaluation measurement kernelCompatibility).comp
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation) =
      measurement :=
  SourceGeneratedScalarPerfectification.canonicalFactor_comp evaluation
    measurement kernelCompatibility

/-- The generated perfect-carrier action and the actual coherent evolution
form one covariance datum. -/
def perfectCovarianceAction
    (data : JointActionData (H := H) evaluation)
    (readout : PerfectCarrier evaluation →ₗ[ℤ] H) :
    SourceGeneratedIntegralCoherentCovariance.ActionData readout where
  integralTransition :=
    SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
      evaluation data.sourceAction
  hilbertEvolution := data.coherentEvolution

/-- Exact vector residual readback on every source event.  Perfectification
neither erases nor manufactures the action--measurement mismatch. -/
theorem couplingResidual_source_readback
    (data : JointActionData (H := H) evaluation)
    (readout : PerfectCarrier evaluation →ₗ[ℤ] H)
    (readback : readout.comp
      (SourceGeneratedScalarPerfectification.canonicalMap evaluation) =
        measurement)
    (event : C) :
    SourceGeneratedIntegralCoherentCovariance.couplingResidual
        (perfectCovarianceAction evaluation data readout)
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) =
      data.coherentEvolution (measurement event) -
        measurement (data.sourceAction.carrierAction event) := by
  have readbackAt :
      readout
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) =
        measurement event := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun readback event
  have actionAt :
      SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
          evaluation data.sourceAction
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) =
        SourceGeneratedScalarPerfectification.canonicalMap evaluation
          (data.sourceAction.carrierAction event) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun
      (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction_canonicalMap
        evaluation data.sourceAction) event
  have nextReadback :
      readout
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation
            (data.sourceAction.carrierAction event)) =
        measurement (data.sourceAction.carrierAction event) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun readback
      (data.sourceAction.carrierAction event)
  rw [SourceGeneratedIntegralCoherentCovariance.couplingResidual,
    perfectCovarianceAction, readbackAt,
    actionAt, nextReadback]

/-- Exact radial readback.  The coherent evolution is an isometry, so this
coordinate measures only the source event's gain/loss under transition. -/
theorem radialResidual_source_readback
    (data : JointActionData (H := H) evaluation)
    (readout : PerfectCarrier evaluation →ₗ[ℤ] H)
    (readback : readout.comp
      (SourceGeneratedScalarPerfectification.canonicalMap evaluation) =
        measurement)
    (event : C) :
    SourceGeneratedIntegralCoherentCovariance.radialResidual
        (perfectCovarianceAction evaluation data readout)
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) =
      ‖measurement event‖ -
        ‖measurement (data.sourceAction.carrierAction event)‖ := by
  have readbackAt :
      readout
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) =
        measurement event := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun readback event
  have actionAt :
      SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction
          evaluation data.sourceAction
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) =
        SourceGeneratedScalarPerfectification.canonicalMap evaluation
          (data.sourceAction.carrierAction event) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun
      (SourceGeneratedScalarEquivariantPerfectAction.perfectCarrierAction_canonicalMap
        evaluation data.sourceAction) event
  have nextReadback :
      readout
          (SourceGeneratedScalarPerfectification.canonicalMap evaluation
            (data.sourceAction.carrierAction event)) =
        measurement (data.sourceAction.carrierAction event) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun readback
      (data.sourceAction.carrierAction event)
  rw [SourceGeneratedIntegralCoherentCovariance.radialResidual,
    perfectCovarianceAction, readbackAt,
    actionAt, nextReadback, data.coherentEvolution.norm_map]

/-- An actual source action--measurement square propagates from source events
to every point of the generated perfect carrier. -/
theorem perfect_covariant_of_source_commuting
    (data : JointActionData (H := H) evaluation)
    (readout : PerfectCarrier evaluation →ₗ[ℤ] H)
    (readback : readout.comp
      (SourceGeneratedScalarPerfectification.canonicalMap evaluation) =
        measurement)
    (sourceCommuting : ∀ event : C,
      data.coherentEvolution (measurement event) =
        measurement (data.sourceAction.carrierAction event)) :
    ∀ value : PerfectCarrier evaluation,
      SourceGeneratedIntegralCoherentCovariance.couplingResidual
        (perfectCovarianceAction evaluation data readout) value = 0 := by
  intro value
  obtain ⟨event, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) value
  change SourceGeneratedIntegralCoherentCovariance.couplingResidual
      (perfectCovarianceAction evaluation data readout)
      (SourceGeneratedScalarPerfectification.canonicalMap evaluation event) = 0
  rw [couplingResidual_source_readback evaluation measurement data readout
    readback]
  exact sub_eq_zero.mpr (sourceCommuting event)

/-- A measurement that descends through the perfect carrier, together with
the complete covariance disposition of its coherent evolution. -/
structure RealizedFace [CompleteSpace H]
    (data : JointActionData (H := H) evaluation) where
  readout : PerfectCarrier evaluation →ₗ[ℤ] H
  source_readback :
    readout.comp
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation) =
      measurement
  covariance : SourceGeneratedIntegralCoherentCovariance.CovarianceDisposition
    (perfectCovarianceAction evaluation data readout)

def generateRealizedFace [CompleteSpace H]
    (data : JointActionData (H := H) evaluation)
    (kernelCompatibility :
      LinearMap.ker evaluation ≤ LinearMap.ker measurement) :
    RealizedFace evaluation measurement data where
  readout := perfectMeasurement evaluation measurement kernelCompatibility
  source_readback :=
    perfectMeasurement_source_readback evaluation measurement kernelCompatibility
  covariance := SourceGeneratedIntegralCoherentCovariance.settleCovariance
    (perfectCovarianceAction evaluation data
      (perfectMeasurement evaluation measurement kernelCompatibility))

/-- Total measurement disposition.  The negative branch is not a defect of
the source carrier: it records an exact source direction lost by the current
evaluation language but still detected by the actual measurement. -/
inductive RealizationDisposition [CompleteSpace H]
    (data : JointActionData (H := H) evaluation) : Type (max c d h + 2)
  | realized (face : RealizedFace evaluation measurement data)
  | representationResidual
      (coordinate :
        SourceGeneratedScalarPerfectification.FaithfulFactorizationResidual
        evaluation measurement)

/-- Total source-generated settlement: either the measurement factors and
receives the full coherent covariance disposition, or an explicit source
coordinate witnesses the representation loss. -/
def settleRealization [CompleteSpace H]
    (data : JointActionData (H := H) evaluation) :
    RealizationDisposition evaluation measurement data := by
  cases SourceGeneratedPerfectification.settleFaithfulFactorization evaluation
      measurement with
  | factors factor factorization =>
      have kernelCompatibility :
          LinearMap.ker evaluation ≤ LinearMap.ker measurement :=
        (SourceGeneratedPerfectification.faithful_factorization_exists_iff
          evaluation measurement).mp ⟨factor, factorization⟩
      exact .realized
        (generateRealizedFace evaluation measurement data kernelCompatibility)
  | residual coordinate =>
      exact .representationResidual
        ⟨coordinate.coordinate, coordinate.invisible_to_dual,
          coordinate.visible_to_actual⟩

/-- The complete joint output: the source square always generates its
equivariant exact-perfect action; the measurement is independently and
totally settled without being used to manufacture that action. -/
structure GeneratedJointState [CompleteSpace H]
    (data : JointActionData (H := H) evaluation) where
  perfectAction : SourceGeneratedScalarEquivariantPerfectAction.GeneratedAction
    evaluation data.sourceAction
  realization : RealizationDisposition evaluation measurement data

def generate [CompleteSpace H]
    (data : JointActionData (H := H) evaluation) :
    GeneratedJointState evaluation measurement data where
  perfectAction := SourceGeneratedScalarEquivariantPerfectAction.generate
    evaluation data.sourceAction
  realization := settleRealization evaluation measurement data

theorem generated_total [CompleteSpace H]
    (data : JointActionData (H := H) evaluation) :
    Nonempty (GeneratedJointState evaluation measurement data) :=
  ⟨generate evaluation measurement data⟩

end

end SourceGeneratedIntegralEquivariantPerfectRealization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
