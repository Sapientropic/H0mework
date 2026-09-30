import H0mework.NavierStokes.Restart.NativeAccumulationRoot
import H0mework.NavierStokes.Restart.BoundedPreAccumulationVelocityStrongTrace
import H0mework.NavierStokes.VelocityEndpoint.AbsoluteWholeMildNativeContinuation

/-!
# Whole-NS velocity join in the bounded analytic fibre

This transporter uses the analytic contact time as the left endpoint of the
already generated absolute whole-mild write.  Every fixed physical velocity
coordinate of the pre-accumulation path converges to that write's initial row,
and the right write retains its unforced mild identity.

The result is deliberately a velocity-carrier join.  It does not relabel the pointwise velocity row
as a whole-vorticity `H¹` landing.  That stronger landing is the next independent PDE obligation.
No endpoint, path, branch, obstruction, or continuation is accepted from the caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation

noncomputable section

/-! ## The one bounded-fibre recognition of the original cofinal endpoint -/

/-- The weak physical velocity endpoint generated at the analytic
accumulation interface. -/
def accumulationBoundaryVelocityEndpoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartVelocityEndpointState :=
  (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
    initial elapsedBounded).family.endpointReceipt.velocityEndpoint

/-- Every fixed nonzero contact velocity row lands at the generated
bounded-fibre endpoint. -/
theorem wholeRestartContactVelocityState_tendsto_accumulationBoundary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : NonzeroIntegerWavevector) :
    Tendsto
      (fun index : Nat =>
        WithLp.ofLp (wholeRestartContactVelocityState initial index wave))
      atTop
      (nhds
        (WithLp.ofLp
          (accumulationBoundaryVelocityEndpoint
            initial elapsedBounded wave))) := by
  apply tendsto_pi_nhds.mpr
  intro coordinate
  have trajectoryTendsto :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint
      initial elapsedBounded wave coordinate
  have sampled := trajectoryTendsto.comp
    (wholeRestartContactEndpointPreAccumulationTime_tendsto_atTop
      initial elapsedBounded)
  convert sampled using 1
  · funext index
    simp only [Function.comp_apply]
    rw [wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint]
  · rfl

/-- The conditional analytic endpoint is the velocity coordinate of the
original root's canonical cofinal occurrence. -/
theorem sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt_velocityEndpoint_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).velocityEndpoint =
      accumulationBoundaryVelocityEndpoint initial elapsedBounded := by
  let receipt :=
    sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial
  apply lp.ext
  funext wave
  ext coordinate
  have cofinalCoordinateTendsto :=
    velocityWeakTendsto_coordinate
      (fun index => wholeRestartContactVelocityState initial
        (receipt.subsequence index))
      receipt.velocityEndpoint receipt.velocityWeak_tendsto wave coordinate
  have analyticRowTendsto :=
    (wholeRestartContactVelocityState_tendsto_accumulationBoundary
      initial elapsedBounded wave).comp
      receipt.subsequence_strictMono.tendsto_atTop
  have analyticCoordinateTendsto :=
    tendsto_pi_nhds.mp analyticRowTendsto coordinate
  exact tendsto_nhds_unique cofinalCoordinateTendsto analyticCoordinateTendsto

/-- The bounded analytic Galerkin ledger is the same core compiler image as
the original cofinal root ledger. -/
theorem sourceGeneratedWholeRestartVelocityEndpointLedger_toCore_eq_nativeTemporal
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).toCore =
      sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial := by
  let boundedLedger :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).toCore
  let nativeLedger :=
    sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial
  have endpointDataEq :
      boundedLedger.family.endpointReceipt =
        nativeLedger.family.endpointReceipt := by
    have endpointEq :
        boundedLedger.family.endpointReceipt.velocityEndpoint =
          nativeLedger.family.endpointReceipt.velocityEndpoint :=
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt_velocityEndpoint_eq
        initial elapsedBounded).symm
    cases hleft : boundedLedger.family.endpointReceipt with
    | mk velocityEndpoint velocityEndpoint_transverse velocityEndpoint_reality =>
      cases hright : nativeLedger.family.endpointReceipt with
      | mk velocityEndpoint' velocityEndpoint_transverse' velocityEndpoint_reality' =>
        simp only [hleft, hright] at endpointEq
        subst velocityEndpoint'
        rfl
  have familyEq : boundedLedger.family = nativeLedger.family := by
    calc
      boundedLedger.family =
          generatedWholeRestartVelocityEndpointGalerkinFamilyCore
            nu boundedLedger.family.endpointReceipt := rfl
      _ = generatedWholeRestartVelocityEndpointGalerkinFamilyCore
            nu nativeLedger.family.endpointReceipt :=
        congrArg
          (generatedWholeRestartVelocityEndpointGalerkinFamilyCore nu)
          endpointDataEq
      _ = nativeLedger.family := rfl
  calc
    boundedLedger =
        generatedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
          boundedLedger.family := rfl
    _ = generatedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
          nativeLedger.family :=
      congrArg
        generatedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        familyEq
    _ = nativeLedger := rfl

/-- The bounded analytic whole write is a faithful presentation of the
original cofinal root's pointwise whole write. -/
theorem sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath_eq_nativeTemporal
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
        initial elapsedBounded =
      sourceGeneratedNativeTemporalAbsoluteWholePath initial := by
  funext time
  unfold sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
  unfold sourceGeneratedNativeTemporalAbsoluteWholePath
  unfold sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
  unfold sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
  rw [
    sourceGeneratedWholeRestartVelocityEndpointLedger_toCore_eq_nativeTemporal
      initial elapsedBounded]

/-- The selected absolute time is unchanged by the bounded analytic
presentation of the original cofinal write. -/
theorem sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime_eq_nativeTemporal
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
        initial elapsedBounded =
      sourceGeneratedNativeTemporalSelectedAbsoluteTime initial := by
  unfold sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
  unfold sourceGeneratedNativeTemporalSelectedAbsoluteTime
  unfold sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
  unfold sourceGeneratedNativeTemporalPositiveTimeH1Slice
  unfold sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
  unfold sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
  rw [
    sourceGeneratedWholeRestartVelocityEndpointLedger_toCore_eq_nativeTemporal
      initial elapsedBounded]

/-- The accumulation event's own time, placed in the literal absolute interval of the existing
whole-mild right write.  The subtype bounds are consequences of the event's generated `time_eq`; a
caller cannot choose another clock point. -/
def nativeAccumulationBoundaryAbsoluteTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
      (wholeRestartVelocityAccumulationTime initial)
      (wholeRestartVelocityAccumulationTime initial + 1) :=
  let event :=
    (sourceGeneratedNativeAccumulationContact
      initial elapsedBounded).boundaryOccurrence.event
  ⟨event.time, by
    rw [event.time_eq]
    constructor <;> linarith⟩

@[simp] theorem nativeAccumulationBoundaryAbsoluteTime_value
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded).1 =
      (sourceGeneratedNativeAccumulationContact
        initial elapsedBounded).boundaryOccurrence.event.time :=
  rfl

/-- Direct same-`T` whole-NS consumer.

The first conclusion retains the analytic time.  The second is the complete
left coordinate trace; the third identifies the right initial row; the fourth
is the unforced mild identity on the right interval.  This theorem carries no
root-world support or boundary disposition authority. -/
theorem sourceGeneratedNativeAccumulationContact_wholeNS_velocityJoin
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let contact :=
      sourceGeneratedNativeAccumulationContact initial elapsedBounded
    let event := contact.boundaryOccurrence.event
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    event.time = wholeRestartVelocityAccumulationTime initial ∧
      (∀ (wave : NonzeroIntegerWavevector) (coordinate : Coordinate),
        Tendsto
          (fun time =>
            wholeRestartBoundedPreAccumulationVelocityTrajectory
              initial elapsedBounded time wave coordinate)
          atTop
          (nhds (weak.velocityEndpoint wave coordinate))) ∧
      (∀ output : IntegerWavevector,
        sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
            initial elapsedBounded
            (nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded)
            output =
          wholeRestartVelocityEndpointCoefficient weak.velocityEndpoint output) ∧
      (∀ (output : IntegerWavevector), output ≠ 0 →
        ∀ time :
          Icc
            (wholeRestartVelocityAccumulationTime initial)
            (wholeRestartVelocityAccumulationTime initial + 1),
          sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
              initial elapsedBounded time output =
            fixedWaveHeatDuhamelValue 1 nu.coeff output
              (wholeRestartVelocityEndpointCoefficient
                weak.velocityEndpoint output)
              (wholeVelocityLerayProjectionSpaceTime output
                ((sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
                  initial elapsedBounded).core.nonlinearLimit output))
              (endpointAbsoluteToLocalTime
                (wholeRestartVelocityAccumulationTime initial) time)) := by
  dsimp only
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      (sourceGeneratedNativeAccumulationContact
        initial elapsedBounded).boundaryOccurrence.event.time_eq
  · intro wave coordinate
    exact
      wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint
        initial elapsedBounded wave coordinate
  · intro output
    let zeroTime :
        Icc
          (wholeRestartVelocityAccumulationTime initial)
          (wholeRestartVelocityAccumulationTime initial + 1) :=
      ⟨wholeRestartVelocityAccumulationTime initial, by
        constructor <;> linarith⟩
    have boundaryTime_eq :
        nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded =
          zeroTime := by
      apply Subtype.ext
      exact
        (sourceGeneratedNativeAccumulationContact
          initial elapsedBounded).boundaryOccurrence.event.time_eq
    rw [boundaryTime_eq]
    simpa only [zeroTime] using continuation.absolutePath_initial_row output
  · intro output outputNe time
    exact continuation.absolutePath_row_mild_identity output outputNe time

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin
end NavierStokes
end SaturationMonoid
