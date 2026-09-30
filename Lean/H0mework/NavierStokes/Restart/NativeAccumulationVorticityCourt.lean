import H0mework.NavierStokes.Restart.NativeAccumulationWholeNSVelocityJoin
import H0mework.NavierStokes.VelocityEndpoint.PositiveTimeH1Reentry
import H0mework.NavierStokes.Restart.FiniteTimeVorticityDivergence
import H0mework.NavierStokes.Restart.FiniteTimeHighFrequencyTailDivergence
import H0mework.NavierStokes.EndpointTransport.FixedWindowLanding
import H0mework.NavierStokes.VelocityEndpoint.PhysicalRightTrace
import H0mework.Foundation.Semantics.RootReality

/-!
# Same-T whole-vorticity analytic fibre

Inside the bounded elapsed-time fibre, the original root's cofinal endpoint is
the analytic velocity endpoint at `T`.  Its absolute whole-mild write has a
strong physical right trace, every finite vorticity window lands at the same
curl row, and every complementary high-frequency tail diverges.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationVorticityCourt

open Filter Set
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.TotalReality
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ZeroLawRootAdmission
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityFixedWindowLanding
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation

noncomputable section

/-- A strong whole-vorticity landing at the exact analytic accumulation
contact. -/
structure NativeAccumulationWholeVorticityStrongLandingAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Type 2 where
  boundaryOccurrence :
    GeneratedNativeAccumulationConditionalOccurrenceAt initial
  boundaryOccurrence_eq : boundaryOccurrence =
    generatedNativeAccumulationConditionalOccurrence initial elapsedBounded
  endpoint : ComplexVorticityHilbertState
  contact_tendsto :
    Tendsto
      (fun index => (run initial index).contact.physicalState)
      atTop (nhds endpoint)

/-- The actual finite process excludes every strong whole-vorticity realization at its generated
accumulation occurrence.  No terminal claim or alternate boundary current is involved. -/
theorem nativeAccumulationWholeVorticityStrongLandingAt_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    IsEmpty
      (NativeAccumulationWholeVorticityStrongLandingAt
        initial elapsedBounded) := by
  refine ⟨?_⟩
  intro landing
  have vorticityDiverges :
      Tendsto (restartPhysicalVorticityMass initial) atTop atTop :=
    tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded
  exact
    (vorticityMass_tendsto_atTop_excludes_strongContactLanding
      initial vorticityDiverges landing.endpoint)
      landing.contact_tendsto

/-- Identify every stage of the bounded-time endpoint family with the native
Galerkin write emitted by the original cofinal root. -/
theorem sourceGeneratedNativeTemporalGalerkinWrite_eq_boundedFamilyStage
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : Nat) :
    HEq (sourceGeneratedNativeTemporalGalerkinWrite initial radius)
      ((generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.stage radius) := by
  unfold sourceGeneratedNativeTemporalGalerkinWrite
  have endpointEq :
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
          initial).velocityEndpoint =
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.velocityEndpoint :=
    sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt_velocityEndpoint_eq
      initial elapsedBounded
  let canonicalEndpoint :
      { endpoint : WholeRestartVelocityEndpointState //
        WholeRestartVelocityEndpointReality endpoint } :=
    ⟨(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).velocityEndpoint,
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).velocityEndpoint_reality⟩
  let boundedEndpoint :
      { endpoint : WholeRestartVelocityEndpointState //
        WholeRestartVelocityEndpointReality endpoint } :=
    ⟨(generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt.velocityEndpoint,
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt.velocityEndpoint_reality⟩
  have endpointDataEq : canonicalEndpoint = boundedEndpoint := by
    apply Subtype.ext
    exact endpointEq
  have stageHEq :
      HEq
        (generatedWholeRestartVelocityEndpointGalerkinStage
          nu canonicalEndpoint.1 canonicalEndpoint.2 radius)
        (generatedWholeRestartVelocityEndpointGalerkinStage
          nu boundedEndpoint.1 boundedEndpoint.2 radius) := by
    rw [endpointDataEq]
  have sourceStageEq :
      sourceGeneratedNativeTemporalGalerkinWrite initial radius =
        generatedWholeRestartVelocityEndpointGalerkinStage
          nu canonicalEndpoint.1 canonicalEndpoint.2 radius := by
    unfold sourceGeneratedNativeTemporalGalerkinWrite
    congr
  have boundedStageEq :
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.stage radius =
        generatedWholeRestartVelocityEndpointGalerkinStage
          nu boundedEndpoint.1 boundedEndpoint.2 radius := by
    rfl
  exact (heq_of_eq sourceStageEq).trans
    (stageHEq.trans (heq_of_eq boundedStageEq.symm))

/-- The absolute whole-mild write is strongly right-continuous at the exact
cofinal velocity endpoint when the analytic clock recognizes a finite `T`. -/
theorem sourceGeneratedNativeTemporalCofinalWholeMild_physicalRightTrace_at_accumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun time :
          Icc
            (wholeRestartVelocityAccumulationTime initial)
            (wholeRestartVelocityAccumulationTime initial + 1) =>
        puncturedEuclideanize
          (sourceGeneratedNativeTemporalAbsoluteWholePath initial time))
      (nhds
        (nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded))
      (nhds
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
          initial).velocityEndpoint) := by
  let boundaryTime :=
    nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded
  have boundaryLocalTime :
      endpointAbsoluteToLocalTime
          (wholeRestartVelocityAccumulationTime initial) boundaryTime =
        (⟨0, by norm_num⟩ : Icc (0 : Real) 1) := by
    apply Subtype.ext
    change
      (sourceGeneratedNativeAccumulationContact
          initial elapsedBounded).boundaryOccurrence.event.time -
          wholeRestartVelocityAccumulationTime initial = 0
    rw [(sourceGeneratedNativeAccumulationContact
      initial elapsedBounded).boundaryOccurrence.event.time_eq]
    ring
  have clockTendsto :
      Tendsto
        (endpointAbsoluteToLocalTime
          (wholeRestartVelocityAccumulationTime initial))
        (nhds boundaryTime)
        (nhds (⟨0, by norm_num⟩ : Icc (0 : Real) 1)) := by
    rw [← boundaryLocalTime]
    exact
      (endpointAbsoluteToLocalTime_continuous
        (wholeRestartVelocityAccumulationTime initial)).continuousAt
  have rightTrace :=
    sourceGeneratedNativeTemporalWholeMildReadWrite_physical_tendsto_initial
      initial
  have absoluteRightTrace := rightTrace.comp clockTendsto
  simpa only [boundaryTime, Function.comp_def,
    sourceGeneratedNativeTemporalAbsoluteWholePath] using
    absoluteRightTrace

/-- The first Galerkin write and the bounded-fibre `T` readout agree on every
registered finite vorticity window. -/
theorem sourceGeneratedNativeTemporalGalerkinWrite_initial_eq_accumulationBoundary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : Nat) :
    (sourceGeneratedNativeTemporalGalerkinWrite
        initial radius).trajectory 0 =
      accumulationBoundaryFiniteVorticityState initial elapsedBounded
        (wholeRestartModes radius) := by
  rw [(sourceGeneratedNativeTemporalGalerkinWrite initial radius).initial,
    sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt_velocityEndpoint_eq
      initial elapsedBounded]
  apply lp.ext
  funext wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · simp [wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      wholeRestartVelocityEndpointFiniteProjection_apply,
      accumulationBoundaryFiniteVorticityState,
      accumulationBoundaryFormalVorticityRow,
      accumulationBoundaryVelocityEndpoint, waveMem]
  · simp [wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      accumulationBoundaryFiniteVorticityState, waveMem]

/-- Under local bounded-time recognition, the complete original contact
sequence converges strongly on each finite window to the initial state of the
already emitted cofinal Galerkin write. -/
theorem sourceGeneratedNativeTemporalGalerkinWrite_sameT_observer_tendsto
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : Nat) :
    Tendsto
      (fun index =>
        complexSharpSupportProjection (wholeRestartModes radius)
          (run initial index).contact.physicalState)
      atTop
      (nhds
        ((sourceGeneratedNativeTemporalGalerkinWrite
          initial radius).trajectory 0)) := by
  rw [sourceGeneratedNativeTemporalGalerkinWrite_initial_eq_accumulationBoundary
    initial elapsedBounded radius]
  exact contactPhysicalState_fixedWindow_tendsto_accumulationBoundary
    initial elapsedBounded (wholeRestartModes radius)

/-- The original cofinal subsequence inherits the whole-vorticity
high-frequency failure under bounded-time recognition. -/
theorem sourceGeneratedNativeTemporalCofinal_highFrequencyTail_tendsto_atTop
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : Nat) :
    Tendsto
      (fun index =>
        restartPhysicalHighFrequencyTailMass initial
          ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
            initial).subsequence index)
          radius)
      atTop atTop := by
  exact
    (tendsto_restartPhysicalHighFrequencyTailMass_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded radius).comp
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).subsequence_strictMono.tendsto_atTop

/-- Complete analytic failure payload on one bounded accumulation fibre,
anchored to the original root's independently emitted cofinal occurrence. -/
structure SourceGeneratedNativeAccumulationVorticityFailureAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Type 2 where
  rootCofinalOccurrence :
    (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
      (.cofinal : NativeTemporalCurrent initial)
  rootCofinalOccurrence_eq :
    rootCofinalOccurrence =
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence
  boundaryOccurrence :
    GeneratedNativeAccumulationConditionalOccurrenceAt initial
  boundaryOccurrence_eq : boundaryOccurrence =
    generatedNativeAccumulationConditionalOccurrence initial elapsedBounded
  eventTime_eq :
    boundaryOccurrence.event.time = wholeRestartVelocityAccumulationTime initial
  leftVelocityCoordinate_tendsto :
    let weak :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    ∀ (wave : NonzeroIntegerWavevector) (coordinate : Coordinate),
      Tendsto
        (fun time =>
          wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded time wave coordinate)
        atTop
        (nhds (weak.velocityEndpoint wave coordinate))
  rightInitialRow_eq :
    ∀ output : IntegerWavevector,
      sourceGeneratedNativeTemporalAbsoluteWholePath initial
          (nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded)
          output =
        wholeRestartVelocityEndpointCoefficient
          (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore
            initial).family.endpointReceipt.velocityEndpoint output
  rightPhysical_tendsto :
    Tendsto
      (fun time :
          Icc
            (wholeRestartVelocityAccumulationTime initial)
            (wholeRestartVelocityAccumulationTime initial + 1) =>
        puncturedEuclideanize
          (sourceGeneratedNativeTemporalAbsoluteWholePath initial time))
      (nhds
        (nativeAccumulationBoundaryAbsoluteTime initial elapsedBounded))
      (nhds
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
          initial).velocityEndpoint)
  rightUnforcedMildIdentity :
    ∀ (output : IntegerWavevector), output ≠ 0 ->
      ∀ time :
        Icc
          (wholeRestartVelocityAccumulationTime initial)
          (wholeRestartVelocityAccumulationTime initial + 1),
        sourceGeneratedNativeTemporalAbsoluteWholePath initial time output =
          fixedWaveHeatDuhamelValue 1 nu.coeff output
            (wholeRestartVelocityEndpointCoefficient
              (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore
                initial).family.endpointReceipt.velocityEndpoint
              output)
            (wholeVelocityLerayProjectionSpaceTime output
              ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
                initial).core.nonlinearLimit output))
            (endpointAbsoluteToLocalTime
              (wholeRestartVelocityAccumulationTime initial) time)
  rowLanding :
    ∀ wave : IntegerWavevector,
      Tendsto
        (fun index => (run initial index).contact.physicalState wave)
        atTop
        (nhds (accumulationBoundaryFormalVorticityRow
          initial elapsedBounded wave))
  fixedWindowLanding :
    ∀ modes : Finset IntegerWavevector,
      Tendsto
        (fun index =>
          complexSharpSupportProjection modes
            (run initial index).contact.physicalState)
        atTop
        (nhds (accumulationBoundaryFiniteVorticityState
          initial elapsedBounded modes))
  vorticityDiverges :
    Tendsto (restartPhysicalVorticityMass initial) atTop atTop
  highFrequencyTailDiverges :
    ∀ radius : Nat,
      Tendsto
        (fun index =>
          restartPhysicalHighFrequencyTailMass initial index radius)
        atTop atTop
  strongLanding_empty :
    IsEmpty
      (NativeAccumulationWholeVorticityStrongLandingAt
        initial elapsedBounded)

/-- Package the same-`T` velocity write, finite-window landings and
whole-vorticity failure generated in the bounded analytic fibre. -/
def sourceGeneratedNativeAccumulationVorticityFailure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    SourceGeneratedNativeAccumulationVorticityFailureAt
      initial elapsedBounded := by
  let contact := sourceGeneratedNativeAccumulationContact initial elapsedBounded
  have velocityJoin :=
    sourceGeneratedNativeAccumulationContact_wholeNS_velocityJoin
      initial elapsedBounded
  refine
    { rootCofinalOccurrence :=
        (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence
      rootCofinalOccurrence_eq := rfl
      boundaryOccurrence := contact.boundaryOccurrence
      boundaryOccurrence_eq := contact.boundaryOccurrence_eq
      eventTime_eq := ?_
      leftVelocityCoordinate_tendsto := ?_
      rightInitialRow_eq := ?_
      rightPhysical_tendsto :=
        sourceGeneratedNativeTemporalCofinalWholeMild_physicalRightTrace_at_accumulation
          initial elapsedBounded
      rightUnforcedMildIdentity := ?_
      rowLanding := ?_
      fixedWindowLanding := ?_
      vorticityDiverges := ?_
      highFrequencyTailDiverges := ?_
      strongLanding_empty :=
        nativeAccumulationWholeVorticityStrongLandingAt_isEmpty
          initial elapsedBounded }
  · exact velocityJoin.1
  · exact velocityJoin.2.1
  · intro output
    change
      (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial)
            (nativeAccumulationBoundaryAbsoluteTime
              initial elapsedBounded)) output = _
    have boundaryLocalTime :
        endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial)
            (nativeAccumulationBoundaryAbsoluteTime
              initial elapsedBounded) =
          (⟨0, by norm_num⟩ : Icc (0 : Real) 1) := by
      apply Subtype.ext
      change
        contact.boundaryOccurrence.event.time -
            wholeRestartVelocityAccumulationTime initial = 0
      rw [contact.boundaryOccurrence.event.time_eq]
      ring
    rw [boundaryLocalTime]
    exact
      (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
        initial).initial_row output
  · intro output outputNe time
    change
      (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial) time) output = _
    exact
      (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
        initial).row_mild_identity output outputNe _
  · exact contactPhysicalState_row_tendsto_accumulationBoundary
      initial elapsedBounded
  · exact contactPhysicalState_fixedWindow_tendsto_accumulationBoundary
      initial elapsedBounded
  · exact
      tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
        initial elapsedBounded
  · exact
      nativeTemporalCofinalWrite_target_highFrequencyTailDiverges
        initial elapsedBounded

/-- The bounded-fibre failure recognizes the original root's exact cofinal
occurrence; executing that occurrence yields the unconditional physical
reentry already generated by the source. -/
theorem sourceGeneratedNativeAccumulationVorticityFailure_physicalNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial
        (sourceGeneratedNativeAccumulationVorticityFailure
          initial elapsedBounded).rootCofinalOccurrence =
      sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial := by
  rw [(sourceGeneratedNativeAccumulationVorticityFailure
    initial elapsedBounded).rootCofinalOccurrence_eq]
  exact
    nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent initial

/-- The source-owned high-frequency failure is large in the exact Hilbert
residual used by a whole-vorticity landing criterion, not only after the
Euclidean-mass readout. -/
theorem sourceGeneratedNativeAccumulationWholeVorticityHighFrequencyResidual_norm_tendsto_atTop
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius : ℕ) :
    Tendsto
      (fun index : ℕ =>
        ‖complexSharpSupportProjection
              (wholeRestartModes radius)
              (run initial index).contact.physicalState -
            (run initial index).contact.physicalState‖)
      atTop atTop := by
  rw [tendsto_atTop]
  intro bound
  let scale : ℝ := max bound 0 + 1
  have scalePos : 0 < scale := by
    dsimp only [scale]
    linarith [le_max_right bound 0]
  have residualMassTendsto :=
    (sourceGeneratedNativeAccumulationVorticityFailure
      initial elapsedBounded).highFrequencyTailDiverges radius
  filter_upwards [
      (tendsto_atTop.1 residualMassTendsto) (3 * scale ^ 2 + 1)] with
      index residualMassLarge
  let residual :=
    complexSharpSupportProjection
        (wholeRestartModes radius)
        (run initial index).contact.physicalState -
      (run initial index).contact.physicalState
  have residualMassLe :
      restartPhysicalHighFrequencyTailMass initial index radius ≤
        3 * ‖residual‖ ^ 2 := by
    simpa only [restartPhysicalHighFrequencyTailMass, residual] using
      ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeVorticityEuclideanMass_le_three_mul_norm_sq
        residual
  have scaleLtResidual : scale < ‖residual‖ := by
    by_contra scaleNotLt
    have residualLeScale : ‖residual‖ ≤ scale :=
      le_of_not_gt scaleNotLt
    have residualNonneg : 0 ≤ ‖residual‖ := norm_nonneg _
    have residualSqLeScaleSq : ‖residual‖ ^ 2 ≤ scale ^ 2 :=
      (sq_le_sq₀ residualNonneg scalePos.le).2 residualLeScale
    nlinarith
  exact (le_max_left bound 0).trans
    (le_add_of_nonneg_right zero_le_one) |>.trans scaleLtResidual.le

/-- Bounded analytic strong-face readout at the exact cofinal root visit.  Its
failure witness is the dependent responsibility carried by the cofinal whole
write, while the local bounded fibre supplies the contact time and finite
observer limits. -/
structure NativeTemporalCofinalExactStrongFaceExitAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Type 2 where
  private mk ::
  boundaryOccurrence :
    GeneratedNativeAccumulationConditionalOccurrenceAt initial
  boundaryOccurrence_eq : boundaryOccurrence =
    generatedNativeAccumulationConditionalOccurrence initial elapsedBounded
  finiteObserverCommutes :
    let receipt :=
      sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial
    ∀ radius : Nat,
      Tendsto
          (fun index =>
            complexSharpSupportProjection (wholeRestartModes radius)
              (run initial
                (receipt.subsequence index)).contact.physicalState)
          atTop
          (nhds
            ((sourceGeneratedNativeTemporalGalerkinWrite
              initial radius).trajectory 0))
  strongFaceFailure : NativeTemporalCofinalStrongFaceFailureAt initial
  strongFaceFailure_eq :
    strongFaceFailure =
      nativeTemporalCofinalEntryStrongFaceFailure initial
        (((nativeTemporalCofinalWritePatch initial
          (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
            initial)).toLedgerWriteEvolution).destination
              (nativeTemporalCofinalEntry initial)).1
  physicalExecution :
    let authority := nativeTemporalCofinalVisitAuthority initial
    let next :=
      generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial authority.toLedgerReadout.occurrence
    HEq authority.toLedgerReadout.wholeLedgerWriteBack
        (nativeTemporalCofinalWrite initial) ∧
      0 < next.duration ∧
      next.receipt.wholePath
          ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
        (sourceGeneratedNativeTemporalPositiveTimeH1Slice
          initial).vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave (next.initialState wave) =
          (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
            initial).wholePath
            (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
            wave

/-- Read the carried cofinal strong-face responsibility in the bounded
analytic fibre.  Boundedness supplies the contact time and finite observers;
the failure witness comes from the original whole-ledger target row. -/
noncomputable def sourceGeneratedNativeTemporalCofinalExactStrongFaceExit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    NativeTemporalCofinalExactStrongFaceExitAt
      initial elapsedBounded := by
  let receipt :=
    sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial
  refine
    { boundaryOccurrence :=
        generatedNativeAccumulationConditionalOccurrence
          initial elapsedBounded
      boundaryOccurrence_eq := rfl
      finiteObserverCommutes := ?_
      strongFaceFailure :=
        nativeTemporalCofinalEntryStrongFaceFailure initial
          (((nativeTemporalCofinalWritePatch initial
            (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
              initial)).toLedgerWriteEvolution).destination
                (nativeTemporalCofinalEntry initial)).1
      strongFaceFailure_eq := rfl
      physicalExecution := ?_ }
  · dsimp only
    intro radius
    exact
      (sourceGeneratedNativeTemporalGalerkinWrite_sameT_observer_tendsto
        initial elapsedBounded radius).comp
        receipt.subsequence_strictMono.tendsto_atTop
  · dsimp only
    have physical :=
      sourceGeneratedNativeTemporalCofinalRootPhysicalExecution initial
    dsimp only at physical
    refine ⟨?_, physical.2.2⟩
    exact heq_of_eq (nativeTemporalCofinalAuthority_generates_write initial)

/-- The strong-face failure readout commutes with the exact cofinal
answer-and-next.  Total reality locates that temporal difference at two
registered occurrences, while the same root realization retains the
whole-ledger write and physical execution. -/
theorem sourceGeneratedNativeTemporalCofinalExactStrongFaceExit_grounded
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let root := nativeTemporalAuthoritativeRoot initial
    let cofinalVisit : LawfulWorldStateAt root :=
      .cofinal (nativeTemporalCofinalVisit initial)
    let nextVisit : LawfulWorldStateAt root :=
      (nativeTemporalCofinalNextCurrent initial).visit
    let difference : RootTotalReality.RootDifference root :=
      (cofinalVisit, nextVisit)
    nextVisit.current =
        (.galerkin 0 : NativeTemporalCurrent initial) ∧
      ActualDifferenceAt (RootTotalReality.semantics root) difference ∧
      (RootTotalReality.semantics root).StructuralIdentityAt difference ∧
      HEq (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.wholeLedgerWriteBack
        (root.toLedgerRoot.generatedAtTemporalVisit cofinalVisit).wholeLedgerWriteBack ∧
      (∀ endpoint : ComplexVorticityHilbertState,
        ¬ Tendsto
          (fun index => (run initial index).contact.physicalState)
          atTop (nhds endpoint)) := by
  dsimp only
  let root := nativeTemporalAuthoritativeRoot initial
  let cofinalVisit : LawfulWorldStateAt root :=
    .cofinal (nativeTemporalCofinalVisit initial)
  let nextVisit : LawfulWorldStateAt root :=
    (nativeTemporalCofinalNextCurrent initial).visit
  let difference : RootTotalReality.RootDifference root :=
    (cofinalVisit, nextVisit)
  have different : cofinalVisit ≠ nextVisit := by
    intro same
    have currentSame :=
      congrArg SourceNativeTemporalVisitAt.current same
    change
      (.cofinal : NativeTemporalCurrent initial) = .galerkin 0
      at currentSame
    cases currentSame
  have actual :
      ActualDifferenceAt (RootTotalReality.semantics root) difference :=
    RootTotalReality.actualDifference root different
  have structural :
      (RootTotalReality.semantics root).StructuralIdentityAt difference := by
    rcases (RootTotalReality.isTotal root).locate difference actual with
      redundant | identity
    · exact False.elim
        (different
          (LawfulWorldStateAt.eq_of_registeredOccurrence_eq redundant))
    · exact identity
  let exit :=
    sourceGeneratedNativeTemporalCofinalExactStrongFaceExit
      initial elapsedBounded
  refine
    ⟨rfl, actual, structural, ?_,
      exit.strongFaceFailure.fails elapsedBounded⟩
  rfl

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationVorticityCourt
end NavierStokes
end SaturationMonoid
