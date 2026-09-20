import H0mework.Physics.ActionForcing.FixedOccurrenceP286ActionForcingBridge
import H0mework.Physics.QuarticDynamics.FixedConstitutiveAnchor

/-!
# Fixed P506/L0 action selection of the radial-quartic P286 field

The fixed U6 mother-action occurrence write already carries a canonical
temporal P286 charge.  This module reads that charge at the distinguished
unit spatial occurrence and feeds it to the coefficient-free radial-quartic
action-principal operator.  It then identifies the selected global field with
the field installed by the existing radial constitutive actual and verifies
its Hessian against the same occurrence action forcing.

Thus the radial inverse principal is selected by a fixed source/current action
event.  No residual coordinate, target field, zero-fiber receipt, branch, or
caller-supplied coefficient enters the selection.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticActionSelection

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ActionForcingBridge
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineSourceGeneratedP286AffineConnectionGerm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

private def PointE0 : BasePoint :=
  canonicalCauchySlicePoint 0 SpatialE0

/-- The radial charge selected directly from the fixed source/current
occurrence write at the canonical unit spatial occurrence. -/
def fixedP506L0U6ActionSelectedRadialCharge : P286CoordinateCarrier :=
  completeJointP286CanonicalOccurrenceWriteProfile Source U6 PointE0
    canonicalLorentzianTimeDirection

/-- The occurrence-selected charge is exactly the previously exposed
mother-action charge.  The unit-radius normalization is fixed by the canonical
coordinate occurrence rather than supplied by a caller. -/
theorem fixedP506L0U6ActionSelectedRadialCharge_eq_motherActionCharge :
    fixedP506L0U6ActionSelectedRadialCharge =
      fixedP506L0U6OccurrenceP286MotherActionCharge := by
  have profile :
      completeJointP286CanonicalOccurrenceWriteProfile Source U6 PointE0 =
        p286SpatialRadiusSquared PointE0 •
          p286TemporalGaugeOneForm
            fixedP506L0U6OccurrenceP286MotherActionCharge := by
    exact
      fixedP506L0_U6_occurrenceWriteProfile_zeroSlice_radialTemporal SpatialE0
  have radius : p286SpatialRadiusSquared PointE0 = 1 := by
    simp [PointE0, SpatialE0, p286SpatialRadiusSquared,
      p286SpatialMetricCovectorOperator, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, p286BaseCoordinate_apply,
      Fin.sum_univ_three]
  have temporal := congrFun profile canonicalLorentzianTimeDirection
  simpa [fixedP506L0U6ActionSelectedRadialCharge, radius] using temporal

/-- Global radial-quartic P286 connection selected by the fixed occurrence
action event. -/
def fixedP506L0U6ActionSelectedRadialQuarticTemporalConnection :
    BasePoint → P286GaugeOneForm :=
  p286RadialQuarticTemporalConnection
    fixedP506L0U6ActionSelectedRadialCharge

/-- The global P286 connection update selected by the fixed occurrence action. -/
def fixedP506L0U6ActionSelectedRadialQuarticConnectionActual :
    StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate U6
    fixedP506L0U6ActionSelectedRadialQuarticTemporalConnection 1

/-- The same source's constitutive action leg applied after the selected
radial connection update. -/
def fixedP506L0U6ActionSelectedRadialQuarticConstitutiveActual :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveWrittenCurrent Source
    fixedP506L0U6ActionSelectedRadialQuarticConnectionActual

theorem fixedP506L0U6ActionSelectedRadialQuarticTemporalConnection_eq :
    fixedP506L0U6ActionSelectedRadialQuarticTemporalConnection =
      p286RadialQuarticTemporalConnection
        fixedP506L0U6OccurrenceP286MotherActionCharge := by
  rw [fixedP506L0U6ActionSelectedRadialQuarticTemporalConnection,
    fixedP506L0U6ActionSelectedRadialCharge_eq_motherActionCharge]

/-- The already installed radial connection actual is literally the update
selected by the fixed source/current occurrence action. -/
theorem fixedP506L0U6RadialQuarticConnectionActual_eq_actionSelected :
    fixedP506L0U6RadialQuarticConnectionActual =
      fixedP506L0U6ActionSelectedRadialQuarticConnectionActual := by
  unfold fixedP506L0U6RadialQuarticConnectionActual
    fixedP506L0U6ActionSelectedRadialQuarticConnectionActual
  rw [fixedP506L0U6ActionSelectedRadialQuarticTemporalConnection_eq]

theorem fixedP506L0U6RadialQuarticConstitutiveActual_eq_actionSelected :
    fixedP506L0U6RadialQuarticConstitutiveActual =
      fixedP506L0U6ActionSelectedRadialQuarticConstitutiveActual := by
  unfold fixedP506L0U6RadialQuarticConstitutiveActual
    fixedP506L0U6ActionSelectedRadialQuarticConstitutiveActual
  rw [fixedP506L0U6RadialQuarticConnectionActual_eq_actionSelected]

/-- The Hessian response of the action-selected global field realizes the
same fixed-U6 occurrence action forcing on the complete zero slice. -/
theorem fixedP506L0U6ActionSelectedRadialQuartic_response_eq_occurrenceForcing_zeroSlice
    (space : StageNineSpatialPoint) :
    let contact := canonicalCauchySlicePoint 0 space
    p286HolonomicSecondJetEulerLagrangeResponse
        (p286RadialQuarticTemporalSecondJet
          fixedP506L0U6ActionSelectedRadialCharge contact) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) := by
  rw [fixedP506L0U6ActionSelectedRadialCharge_eq_motherActionCharge]
  exact
    fixedP506L0_U6_radialQuarticActionPrincipal_response_eq_occurrenceForcing_zeroSlice
      space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticActionSelection
