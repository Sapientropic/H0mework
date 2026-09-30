import H0mework.NavierStokes.NativeWork.StandingPaidActionMaterialInstruction
import H0mework.NavierStokes.Accumulation.MovingInventoryScaleRelativeClockFold
import H0mework.NavierStokes.VelocityGalerkin.FiniteObservationTimeTightness
import H0mework.NavierStokes.Restart.CompleteSerrinLanding

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube
open ThreeDimensionalVorticityCoefficientFullReceiptNormalizedWorkEulerEscrow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSerrinActionExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMovingInventoryScaleRelativeClockFold
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedKineticAdvance

noncomputable section

abbrev source := stackedStandingActionMediumSource

/-! ## Exact action/kinetic compensator normal form -/

def kineticCompensatedPotential
    (alpha : Real) (state : source.State) : Real :=
  standingActionMixedClockPotential state +
    alpha * puncturedWholeVorticityKineticMass
      state.1.physical.contact.physicalState

theorem kineticCompensatedPotential_nonneg
    (alpha : Real) (alphaNonneg : 0 ≤ alpha)
    (state : source.State) :
    0 ≤ kineticCompensatedPotential alpha state := by
  unfold kineticCompensatedPotential
  exact add_nonneg
    (standingActionMixedClockPotential_nonneg state)
    (mul_nonneg alphaNonneg
      (puncturedWholeVorticityKineticMass_nonneg _))

def kineticCompensatedClockState
    (alpha : Real) (alphaNonneg : 0 ≤ alpha)
    (state : source.State) :
    SourceGeneratedRootClockStateAt source state where
  potential := kineticCompensatedPotential alpha state
  potential_nonneg := kineticCompensatedPotential_nonneg
    alpha alphaNonneg state

/-- On a retained standing, the mixed action face and the kinetic ledger
are one exact current-side coboundary. -/
theorem rootResidual_kineticCompensated_coboundary
    (alpha : Real)
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    let state := source.stateAfter stage
    let nextState := source.stateAfter (stage + 1)
    kineticCompensatedPotential alpha state -
          kineticCompensatedPotential alpha nextState -
        source.clockAt state =
      (standingActionRootResidualFaceCapacityDrop state +
          (nativeRestartStandingActionValuedArithmeticMaterial
            state).endpointResidualReadout) /
        state.2.yCellCoreCharge +
      alpha *
        (puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            nextState.1.physical.contact.physicalState) := by
  dsimp only
  have mixed := standingActionRootResidualMixedClock_coboundary
    stackedInitialActionMaterialInstruction stage effect rootResidual
  dsimp only [source, stackedStandingActionMediumSource] at mixed ⊢
  unfold kineticCompensatedPotential
  calc
    (standingActionMixedClockPotential
          (stackedStandingActionMediumSource.stateAfter stage) +
          alpha * puncturedWholeVorticityKineticMass
            (stackedStandingActionMediumSource.stateAfter
              stage).1.physical.contact.physicalState) -
        (standingActionMixedClockPotential
            (stackedStandingActionMediumSource.stateAfter (stage + 1)) +
          alpha * puncturedWholeVorticityKineticMass
            (stackedStandingActionMediumSource.stateAfter
              (stage + 1)).1.physical.contact.physicalState) -
        stackedStandingActionMediumSource.clockAt
          (stackedStandingActionMediumSource.stateAfter stage) =
      (standingActionMixedClockPotential
            (stackedStandingActionMediumSource.stateAfter stage) -
          standingActionMixedClockPotential
            (stackedStandingActionMediumSource.stateAfter (stage + 1)) -
          stackedStandingActionMediumSource.clockAt
            (stackedStandingActionMediumSource.stateAfter stage)) +
        alpha *
          (puncturedWholeVorticityKineticMass
              (stackedStandingActionMediumSource.stateAfter
                stage).1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
              (stackedStandingActionMediumSource.stateAfter
                (stage + 1)).1.physical.contact.physicalState) := by
        ring
    _ = _ := by
      have added := congrArg
        (fun value : Real => value + alpha *
          (puncturedWholeVorticityKineticMass
              ((standingActionWholeRestartMediumSource
                stackedInitialActionMaterialInstruction).stateAfter
                  stage).1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
              ((standingActionWholeRestartMediumSource
                stackedInitialActionMaterialInstruction).stateAfter
                  (stage + 1)).1.physical.contact.physicalState))
        mixed
      simpa only [stackedStandingActionMediumSource] using added

/-- The coupled clock advance is exactly the source-sector coercivity
equation.  This theorem neither assumes nor selects a future branch. -/
theorem rootResidual_kineticCompensated_domination_iff
    (alpha : Real)
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    let state := source.stateAfter stage
    let nextState := source.stateAfter (stage + 1)
    source.clockAt state +
          kineticCompensatedPotential alpha nextState ≤
        kineticCompensatedPotential alpha state ↔
      -(nativeRestartStandingActionValuedArithmeticMaterial
          state).endpointResidualReadout ≤
        standingActionRootResidualFaceCapacityDrop state +
          alpha * state.2.yCellCoreCharge *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState) := by
  dsimp only
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  have coboundary := rootResidual_kineticCompensated_coboundary
    alpha stage effect rootResidual
  dsimp only at coboundary
  have chargePos : 0 < state.2.yCellCoreCharge :=
    state.2.yCellCoreCharge_pos
  constructor
  · intro domination
    have quotientNonneg :
        0 ≤
          (standingActionRootResidualFaceCapacityDrop state +
              (nativeRestartStandingActionValuedArithmeticMaterial
                state).endpointResidualReadout) /
            state.2.yCellCoreCharge +
          alpha *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState) := by
      rw [← coboundary]
      linarith
    have scaled := mul_nonneg quotientNonneg chargePos.le
    rw [add_mul, div_mul_cancel₀ _ chargePos.ne'] at scaled
    dsimp only [state, nextState] at scaled ⊢
    nlinarith
  · intro sector
    have scaledNonneg :
        0 ≤
          standingActionRootResidualFaceCapacityDrop state +
            (nativeRestartStandingActionValuedArithmeticMaterial
              state).endpointResidualReadout +
          (alpha *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState)) *
            state.2.yCellCoreCharge := by
      dsimp only [state, nextState] at sector ⊢
      nlinarith
    have quotientNonneg :
        0 ≤
          (standingActionRootResidualFaceCapacityDrop state +
              (nativeRestartStandingActionValuedArithmeticMaterial
                state).endpointResidualReadout) /
            state.2.yCellCoreCharge +
          alpha *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState) := by
      apply (mul_nonneg_iff_of_pos_right chargePos).mp
      rw [add_mul, div_mul_cancel₀ _ chargePos.ne']
      simpa only [mul_assoc, mul_left_comm, mul_comm] using scaledNonneg
    rw [← coboundary] at quotientNonneg
    linarith

/-! ## Faithful whole-action form of the coupled sector -/

/-- The actual whole tangent read on the five oriented child coordinates.
Unlike the canonical y-cell charge, this readout vanishes on the zero
physical source. -/
def actualDyadicWholeActionReadout
    (state : source.State) : Real :=
  state.2.dyadicChildReadoutOf
    (classicalWholeNSVorticityTangent butterflyGainViscosity
      state.1.physical.contact.physicalState)

theorem actualDyadicWholeActionReadout_eq_zero_of_physicalState_eq_zero
    (state : source.State)
    (physicalZero : state.1.physical.contact.physicalState = 0) :
    actualDyadicWholeActionReadout state = 0 := by
  have nonlinearZero : ∀ output : IntegerWavevector,
      wholeStateVorticityNonlinearCoefficientAt
        (0 : ComplexVorticityHilbertState) output = 0 := by
    intro output
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      (∅ : Finset IntegerWavevector)
      (0 : ComplexVorticityHilbertState) (by intro wave _; rfl) output]
    simp [finiteStateVorticityNonlinearCoefficientAt]
  rw [actualDyadicWholeActionReadout, physicalZero]
  simp [classicalWholeNSVorticityTangent,
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf,
    nonlinearZero]

/-- Complete physical mass-power readout on the same current dyadic child
face.  This is the quadratic action valuation paired with the actual state,
not the canonical linear orientation token. -/
def actualDyadicChildFaceNetPower
    (state : source.State) : Real :=
  ∑ wave ∈ state.2.dyadicChildModes,
    instantaneousWholeNetPowerRow butterflyGainViscosity
      state.1.physical.contact.physicalState wave

/-- The concrete source seed generates a strictly positive complete
child-face power.  This is the source-specific coordinate absent from the
zero-current no-go. -/
theorem initial_actualDyadicChildFaceNetPower_pos :
    0 < actualDyadicChildFaceNetPower source.initial := by
  unfold actualDyadicChildFaceNetPower source
    stackedStandingActionMediumSource
    standingActionWholeRestartMediumSource
    SourceGeneratedActionMaterialInstructionAt.dyadicChildModes
    SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
    SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
  change
    0 < ∑ wave ∈ butterflyFirstStackChildFaceModes,
      instantaneousWholeNetPowerRow butterflyGainViscosity
        stackedShortCurrent.contact.physicalState wave
  apply Finset.sum_pos
  · intro wave waveMem
    exact stackedShortContact_childFace_netPower_pos wave waveMem
  · exact ⟨butterflyFirstStackAxisEight, by
      simp [butterflyFirstStackChildFaceModes]⟩

private theorem wholeRestartModes_mono_clock
    {smaller larger : Nat} (radiusLe : smaller ≤ larger) :
    wholeRestartModes smaller ⊆ wholeRestartModes larger := by
  intro wave waveMem
  rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
    Finset.mem_erase] at waveMem ⊢
  refine ⟨waveMem.1, ?_⟩
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
    at waveMem ⊢
  intro coordinate
  have coordinateMem := waveMem.2 coordinate
  rw [Finset.mem_Icc] at coordinateMem ⊢
  have castLe : (smaller : Int) ≤ larger := by exact_mod_cast radiusLe
  constructor <;> omega

private theorem standingActionCompilerInventory_nested (stage : Nat) :
    (source.stateAfter stage).2.modes ⊆
      (source.stateAfter (stage + 1)).2.modes := by
  let instruction := (source.stateAfter stage).2
  have nextInstruction : (source.stateAfter (stage + 1)).2 =
      instruction.advance := by rfl
  rw [nextInstruction]
  change instruction.modes ⊆ instruction.advance.modes
  rw [instruction.advance_modes]
  intro wave waveMem
  apply instruction.actionClosure_subset_nextModes
  apply Finset.mem_erase.mpr
  exact ⟨fun waveZero => instruction.modes_zeroNotMem (waveZero ▸ waveMem),
    modes_subset_wholeFiniteSupportActionModes instruction.modes waveMem⟩

theorem butterflyFirstStackModes_subset_initialActionInventory :
    butterflyFirstStackModes ⊆ (source.stateAfter 0).2.modes := by
  have sourceSubset : butterflyFirstStackModes ⊆ wholeRestartModes 4 := by
    decide
  have radiusLe : 4 ≤ (source.stateAfter 0).2.radius := by
    exact stackedInitialActionMaterialInstruction.cellScale_le_radius
  exact sourceSubset.trans (wholeRestartModes_mono_clock radiusLe)

/-- The moving clock starts on the complete sixteen-row physical source
carrier.  Every successor uses the compiler-owned capture inventory, so an
exact payment still resets into a tail smaller than the generated tolerance. -/
def standingActionRunInventory : Nat → Finset IntegerWavevector
  | 0 => butterflyFirstStackModes
  | stage + 1 => (source.stateAfter (stage + 1)).2.modes

theorem standingActionRunInventory_zeroNotMem : ∀ stage : Nat,
    (0 : IntegerWavevector) ∉ standingActionRunInventory stage
  | 0 => butterflyFirstStackModes_zeroNotMem
  | stage + 1 => (source.stateAfter (stage + 1)).2.modes_zeroNotMem

/-- The source carrier embeds into the first generated capture inventory;
afterward ordinary action-closure nesting takes over definitionally. -/
theorem standingActionRunInventory_nested (stage : Nat) :
    standingActionRunInventory stage ⊆
      standingActionRunInventory (stage + 1) := by
  cases stage with
  | zero =>
      exact butterflyFirstStackModes_subset_initialActionInventory.trans
        (standingActionCompilerInventory_nested 0)
  | succ stage =>
      exact standingActionCompilerInventory_nested (stage + 1)

theorem standingActionAnchorLevel_pos (stage : Nat) :
    0 < (source.stateAfter stage).1.standing.anchorLevel := by
  let current := run stackedShortCurrent stage
  have levelPosReal := wholeRestartCoefficientCeiling_pos current.contact
  change 0 < (wholeRestartCoefficientLevel current.contact : Real)
    at levelPosReal
  have levelPos : 0 < wholeRestartCoefficientLevel current.contact := by
    exact_mod_cast levelPosReal
  have levelLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_currentLevel_le_anchorLevel
      (runCellStanding stackedShortCurrent stage)
  have runAnchorPos :
      0 < (runCellStanding stackedShortCurrent stage).anchorLevel :=
    levelPos.trans_le levelLe
  have runtimeEq :=
    standingActionWholeRestartMediumSource_stateAfter_current
      stackedInitialActionMaterialInstruction stage
  have anchorEq := congrArg
    (fun runtime : GeneratedWholeRestartRuntimeCurrent
        butterflyGainViscosity => runtime.standing.anchorLevel)
    runtimeEq
  calc
    0 < (runCellStanding stackedShortCurrent stage).anchorLevel := runAnchorPos
    _ = (source.stateAfter stage).1.standing.anchorLevel := by
      rw [show (runCellStanding stackedShortCurrent stage).anchorLevel =
          (runRuntime stackedShortCurrent stage).standing.anchorLevel by rfl]
      simpa only [source, stackedStandingActionMediumSource] using anchorEq.symm

/-- Moving-ledger alignment: edge `stage + 1` uses the action inventory
generated at current `stage`, before that edge's physical contact is chosen. -/
def shiftedStandingActionInventory : Nat → Finset IntegerWavevector
  | 0 => standingActionRunInventory 0
  | stage + 1 => standingActionRunInventory stage

theorem shiftedStandingActionInventory_zeroNotMem : ∀ stage : Nat,
    (0 : IntegerWavevector) ∉ shiftedStandingActionInventory stage
  | 0 => standingActionRunInventory_zeroNotMem 0
  | stage + 1 => standingActionRunInventory_zeroNotMem stage

theorem shiftedStandingActionInventory_nested (stage : Nat) :
    shiftedStandingActionInventory stage ⊆
      shiftedStandingActionInventory (stage + 1) := by
  cases stage with
  | zero => rfl
  | succ stage => exact standingActionRunInventory_nested stage

@[simp] theorem shiftedStandingActionInventory_succ (stage : Nat) :
    shiftedStandingActionInventory (stage + 1) =
      standingActionRunInventory stage := rfl

/-- The moving-ledger base at index `stage` is exactly the finite mass of
the action instruction installed on root current `stage`. -/
theorem shiftedStandingActionMassBase_eq_currentMaterial
    (stage : Nat) :
    shiftedMovingInventoryMassBase stackedShortCurrent
        shiftedStandingActionInventory stage =
      finiteStateVorticityCoefficientEnstrophy
          (standingActionRunInventory stage)
          (run stackedShortCurrent stage).contact.physicalState + 1 := by
  unfold shiftedMovingInventoryMassBase
  rw [shiftedStandingActionInventory_succ,
    run_succ_initialState]

/-- Exact edge alignment.  Moving edge `stage + 1` is the signed finite-mass
change between the current action material and its compiler-owned successor;
it is not the positive-part fresh-gain debit. -/
theorem standingActionMovingEdgePayment_eq_materialBoundary
    (stage : Nat) :
    runMovingInventoryEdgePayment stackedShortCurrent
        shiftedStandingActionInventory (stage + 1) =
      finiteStateVorticityCoefficientEnstrophy
          (standingActionRunInventory (stage + 1))
          (run stackedShortCurrent (stage + 1)).contact.physicalState -
        finiteStateVorticityCoefficientEnstrophy
          (standingActionRunInventory stage)
          (run stackedShortCurrent stage).contact.physicalState := by
  rw [runMovingInventoryEdgePayment_eq_nextFiniteMass_sub_current
    stackedShortCurrent shiftedStandingActionInventory
      shiftedStandingActionInventory_zeroNotMem]
  rw [shiftedStandingActionInventory_succ,
    shiftedStandingActionInventory_succ]
  have targetBoundary := congrArg
    (finiteStateVorticityCoefficientEnstrophy
      (standingActionRunInventory (stage + 1)))
    (run_succ_initialState stackedShortCurrent (stage + 1))
  have sourceBoundary := congrArg
    (finiteStateVorticityCoefficientEnstrophy
      (standingActionRunInventory stage))
    (run_succ_initialState stackedShortCurrent stage)
  rw [targetBoundary, sourceBoundary]

/-- The signed moving edge contains the complete actual power integral on
the current instruction; successor capture can only add nonnegative material.
Thus the quantitative producer may target the physical action integral
directly, without routing through a positive-part expansion debit. -/
theorem standingActionProjectedPowerIntegral_le_movingEdgePayment
    (stage : Nat) :
    (∫ actual in (0 : Real)..
        (run stackedShortCurrent (stage + 1)).contact.time.1,
      actualProjectedWholeNetEnstrophyPower
        (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
        (standingActionRunInventory stage) actual) ≤
      runMovingInventoryEdgePayment stackedShortCurrent
        shiftedStandingActionInventory (stage + 1) := by
  unfold runMovingInventoryEdgePayment
  rw [shiftedStandingActionInventory_succ,
    shiftedStandingActionInventory_succ]
  have captureNonneg := wholeInventoryCaptureMass_nonneg_of_subset
    (standingActionRunInventory_nested stage)
    (run stackedShortCurrent (stage + 2)).initialState
  linarith

/-- Complementary mass left outside the action compiler's current inventory.
This is a finite current-side asset, not a successor liability. -/
def standingActionMovingTailPotential (stage : Nat) : Real :=
  wholeTailVorticityMass (standingActionRunInventory stage)
    (run stackedShortCurrent stage).contact.physicalState

theorem standingActionMovingTailPotential_nonneg (stage : Nat) :
    0 ≤ standingActionMovingTailPotential stage := by
  exact wholeTailVorticityMass_nonneg _ _

/-- Exact moving-tail factorization.  The signed inventory edge and the
complete whole-mass liability are the two projections of the current
complementary-mass drop. -/
theorem standingActionMovingEdgePayment_add_wholeMassLiability_eq_tailDrop
    (stage : Nat) :
    runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1) +
        (wholeVorticityEuclideanMass
            (run stackedShortCurrent stage).contact.physicalState -
          wholeVorticityEuclideanMass
            (run stackedShortCurrent (stage + 1)).contact.physicalState) =
      standingActionMovingTailPotential stage -
        standingActionMovingTailPotential (stage + 1) := by
  rw [standingActionMovingEdgePayment_eq_materialBoundary]
  unfold standingActionMovingTailPotential
  rw [wholeTailVorticityMass_eq_whole_sub_finite,
    wholeTailVorticityMass_eq_whole_sub_finite]
  ring

/-- Root remaining-cell debt plus the complement of the compiler-owned
action inventory.  Both summands are current-side nonnegative material. -/
def standingActionMovingResidualPotential (stage : Nat) : Real :=
  (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.sourceRemainingDeficit +
    standingActionMovingTailPotential stage

theorem standingActionMovingResidualPotential_nonneg (stage : Nat) :
    0 ≤ standingActionMovingResidualPotential stage := by
  let material := nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter stage)
  have deficitNonneg : 0 ≤ material.standingMaterial.sourceRemainingDeficit := by
    rw [material.standingMaterial.sourceRemainingDeficit_eq]
    exact (source.stateAfter stage).1.standing.remainingCellDeficit_nonneg
  exact add_nonneg deficitNonneg
    (standingActionMovingTailPotential_nonneg stage)

/-- The moving bankroll is not a new account: it is exactly the unoccupied
physical capacity below the live standing wall. -/
theorem standingActionMovingResidualPotential_eq_anchor_sub_inventory
    (stage : Nat) :
    standingActionMovingResidualPotential stage =
      ((source.stateAfter stage).1.standing.anchorLevel : Real) - 1 -
        finiteStateVorticityCoefficientEnstrophy
          (standingActionRunInventory stage)
          (run stackedShortCurrent stage).contact.physicalState := by
  let material := nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter stage)
  have currentEq :
      (source.stateAfter stage).1.physical =
        run stackedShortCurrent stage := by
    have generated :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    exact congrArg (fun current => current.physical) generated
  unfold standingActionMovingResidualPotential
  rw [material.standingMaterial.sourceRemainingDeficit_eq]
  rw [(source.stateAfter stage).1.standing.remainingCellDeficit_eq_anchorLevel_sub_physicalMass]
  unfold standingActionMovingTailPotential
  rw [wholeTailVorticityMass_eq_whole_sub_finite]
  have wholeMassEq := congrArg
    (fun current : GeneratedWholeRestartCurrent butterflyGainViscosity =>
      wholeVorticityEuclideanMass current.contact.physicalState)
    currentEq
  rw [wholeMassEq]
  ring

theorem standingActionMovingResidualPotential_le_anchor_sub_one
    (stage : Nat) :
    standingActionMovingResidualPotential stage ≤
      ((source.stateAfter stage).1.standing.anchorLevel : Real) - 1 := by
  rw [standingActionMovingResidualPotential_eq_anchor_sub_inventory]
  have inventoryNonneg : 0 ≤
      finiteStateVorticityCoefficientEnstrophy
        (standingActionRunInventory stage)
        (run stackedShortCurrent stage).contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  linarith

private theorem clearStanding_remainingCellDeficit_lt_one
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    (GeneratedWholeRestartCellStandingAt.clear :
        GeneratedWholeRestartCellStandingAt current).remainingCellDeficit < 1 := by
  have rawNonneg : 0 ≤ wholeRestartRawCoefficientCeiling current.contact := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    linarith [
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
        current.contact.physicalState]
  have ceilingLt := Nat.ceil_lt_add_one rawNonneg
  change
    (wholeRestartCoefficientLevel current.contact : Real) <
      wholeRestartRawCoefficientCeiling current.contact + 1 at ceilingLt
  rw [wholeRestartRawCoefficientCeiling_eq] at ceilingLt
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    at ceilingLt
  change
    (wholeRestartCoefficientLevel current.contact : Real) - 1 -
        wholeVorticityEuclideanMass current.contact.physicalState < 1
  linarith

private theorem actionInstruction_advance_floor
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.advance.floor = instruction.floor := by
  unfold SourceGeneratedActionMaterialInstructionAt.advance
  split <;> rfl

theorem standingActionInstruction_floor_eq_one : ∀ stage : Nat,
    (source.stateAfter stage).2.floor = 1
  | 0 => rfl
  | stage + 1 => by
      change (source.stateAfter stage).2.advance.floor = 1
      rw [actionInstruction_advance_floor,
        standingActionInstruction_floor_eq_one stage]

theorem standingActionInstruction_tolerance_le_one (stage : Nat) :
    (source.stateAfter stage).2.tolerance.1 ≤ 1 := by
  let instruction := (source.stateAfter stage).2
  let current := (source.stateAfter stage).1.physical
  let base := wholeVorticityEuclideanMass current.contact.physicalState + 1
  let upper :=
    ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficientUpper
      butterflyGainViscosity
  have baseOne : 1 ≤ base := by
    dsimp only [base]
    linarith [
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
        current.contact.physicalState]
  have basePos : 0 < base := lt_of_lt_of_le (by norm_num) baseOne
  have upperOne : 1 ≤ upper := by
    dsimp only [upper]
    unfold ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficientUpper
    linarith [
      ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption.sourceOwnedLocalQuadraticFifthCoefficientUpper_nonneg
        butterflyGainViscosity]
  have upperPos : 0 < upper := lt_of_lt_of_le (by norm_num) upperOne
  have quarterPowerLeOne :
      (1 / 4 : Real) ^ (5 / 4 : Real) ≤ 1 := by
    have generated := Real.rpow_le_rpow
      (show (0 : Real) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : Real) ≤ 1 by norm_num)
      (show (0 : Real) ≤ 5 / 4 by norm_num)
    simpa using generated
  have chargeLeOne :
      fullReceiptRetainedCharge butterflyGainViscosity 1 ≤ 1 := by
    unfold fullReceiptRetainedCharge
    have denominatorOne : 1 ≤ upper * 4 ^ (7 : Nat) := by
      dsimp only [upper]
      nlinarith [show (1 : Real) ≤ 4 ^ (7 : Nat) by norm_num]
    have denominatorPos : 0 < upper * 4 ^ (7 : Nat) := by positivity
    apply (div_le_one denominatorPos).2
    simpa only [one_mul] using quarterPowerLeOne.trans denominatorOne
  have basePowerOne : 1 ≤
      base ^ (fullReceiptRetainedResidenceExponent - 1) := by
    have exponentNonneg : 0 ≤
        fullReceiptRetainedResidenceExponent - 1 := by
      unfold fullReceiptRetainedResidenceExponent
      norm_num
    have generated := Real.rpow_le_rpow
      (show (0 : Real) ≤ 1 by norm_num) baseOne exponentNonneg
    simpa using generated
  have denominatorOne : 1 ≤
      6 * base ^ (fullReceiptRetainedResidenceExponent - 1) := by
    nlinarith
  have denominatorPos : 0 <
      6 * base ^ (fullReceiptRetainedResidenceExponent - 1) := by
    positivity
  have firstLeOne :
      fullReceiptRetainedCharge butterflyGainViscosity 1 /
          (6 * base ^ (fullReceiptRetainedResidenceExponent - 1)) ≤ 1 := by
    apply (div_le_one denominatorPos).2
    exact chargeLeOne.trans denominatorOne
  have toleranceLeFirst : instruction.tolerance.1 ≤
      fullReceiptRetainedCharge butterflyGainViscosity instruction.floor /
        (6 * base ^ (fullReceiptRetainedResidenceExponent - 1)) := by
    unfold SourceGeneratedActionMaterialInstructionAt.tolerance
      currentFullReceiptScaleTolerance
    exact min_le_left _ _
  rw [standingActionInstruction_floor_eq_one stage] at toleranceLeFirst
  exact toleranceLeFirst.trans firstLeOne

/-- Exact one-cell payment resets the moving bankroll inside a uniformly
bounded cell gap.  The only additional amount is the successor instruction's
own generated capture tolerance. -/
theorem standingActionMovingResidualPotential_next_lt_one_add_tolerance_of_exact
    (stage : Nat)
    (commutes :
      (nativeRestartStandingActionValuedArithmeticMaterial
          (source.stateAfter stage)).arithmeticMaterial.whole =
        (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial.left.parallel
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial.right) :
    standingActionMovingResidualPotential (stage + 1) <
      1 + (source.stateAfter (stage + 1)).2.tolerance.1 := by
  let material := nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter stage)
  have standingCommutes :
      material.standingMaterial.arithmeticMaterial.whole =
        material.standingMaterial.arithmeticMaterial.left.parallel
          material.standingMaterial.arithmeticMaterial.right := by
    rw [← material.arithmeticMaterial_eq]
    exact commutes
  have targetClear :=
    material.standingMaterial.targetStanding_eq_clear_of_commutes
      standingCommutes
  have nextStandingClear :
      (source.stateAfter (stage + 1)).1.standing = .clear := by
    change (source.stateAfter stage).1.standing.next = .clear
    rw [← material.standingMaterial.targetStanding_eq]
    exact targetClear
  have deficitLt :
      (source.stateAfter (stage + 1)).1.standing.remainingCellDeficit < 1 := by
    rw [nextStandingClear]
    exact clearStanding_remainingCellDeficit_lt_one
      (source.stateAfter (stage + 1)).1.physical
  have tailLt := (source.stateAfter (stage + 1)).2.currentTail_lt
  have currentEq :
      (source.stateAfter (stage + 1)).1.physical =
        run stackedShortCurrent (stage + 1) := by
    have generated :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction (stage + 1)
    exact congrArg (fun current => current.physical) generated
  unfold standingActionMovingResidualPotential
  rw [(nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter (stage + 1))).standingMaterial.sourceRemainingDeficit_eq]
  unfold standingActionMovingTailPotential standingActionRunInventory
  have tailEq :
      wholeTailVorticityMass (source.stateAfter (stage + 1)).2.modes
          (run stackedShortCurrent (stage + 1)).contact.physicalState =
        wholeTailVorticityMass (source.stateAfter (stage + 1)).2.modes
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState := by
    rw [currentEq]
  rw [tailEq]
  linarith

theorem standingActionMovingResidualPotential_next_lt_two_of_exact
    (stage : Nat)
    (commutes :
      (nativeRestartStandingActionValuedArithmeticMaterial
          (source.stateAfter stage)).arithmeticMaterial.whole =
        (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial.left.parallel
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial.right) :
    standingActionMovingResidualPotential (stage + 1) < 2 := by
  have reset :=
    standingActionMovingResidualPotential_next_lt_one_add_tolerance_of_exact
      stage commutes
  have toleranceLe := standingActionInstruction_tolerance_le_one (stage + 1)
  linarith

def standingActionMovingScalePowerCoefficient : Real :=
  fullReceiptRetainedCharge butterflyGainViscosity 1 / 4

theorem standingActionMovingScalePowerCoefficient_pos :
    0 < standingActionMovingScalePowerCoefficient := by
  unfold standingActionMovingScalePowerCoefficient
  exact div_pos (fullReceiptRetainedCharge_pos butterflyGainViscosity
    (by norm_num)) (by norm_num)

theorem standingActionMovingScalePowerCoefficient_le_one :
    standingActionMovingScalePowerCoefficient ≤ 1 := by
  have upperOne : (1 : Real) ≤
      sourceOwnedWholeStateBarrierSeventhCoefficientUpper
        butterflyGainViscosity := by
    unfold sourceOwnedWholeStateBarrierSeventhCoefficientUpper
    linarith [
      ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption.sourceOwnedLocalQuadraticFifthCoefficientUpper_nonneg
        butterflyGainViscosity]
  have quarterPowerLeOne :
      (1 / 4 : Real) ^ (5 / 4 : Real) ≤ 1 := by
    have generated := Real.rpow_le_rpow
      (by norm_num : (0 : Real) ≤ 1 / 4)
      (by norm_num : (1 / 4 : Real) ≤ 1)
      (by norm_num : (0 : Real) ≤ 5 / 4)
    simpa using generated
  have denominatorOne : (1 : Real) ≤
      sourceOwnedWholeStateBarrierSeventhCoefficientUpper
          butterflyGainViscosity * 4 ^ (7 : Nat) := by
    have fourPowerOne : (1 : Real) ≤ 4 ^ (7 : Nat) := by norm_num
    nlinarith
  have chargeLeOne :
      fullReceiptRetainedCharge butterflyGainViscosity 1 ≤ 1 := by
    unfold fullReceiptRetainedCharge
    have denominatorPos : 0 <
        sourceOwnedWholeStateBarrierSeventhCoefficientUpper
          butterflyGainViscosity * 4 ^ (7 : Nat) := by positivity
    apply (div_le_one denominatorPos).2
    simpa only [one_mul] using quarterPowerLeOne.trans denominatorOne
  unfold standingActionMovingScalePowerCoefficient
  linarith

def standingActionMovingResidualWeight (anchor : Nat) : Real :=
  1 / (standingActionMovingScalePowerCoefficient *
    (((anchor : Real) + 1) ^ (5 / 4 : Real)))

theorem standingActionMovingResidualWeight_pos (anchor : Nat) :
    0 < standingActionMovingResidualWeight anchor := by
  unfold standingActionMovingResidualWeight
  exact one_div_pos.mpr (mul_pos
    standingActionMovingScalePowerCoefficient_pos
    (Real.rpow_pos_of_pos (by positivity) _))

def standingActionMovingResetModel (anchor : Nat) : Real :=
  2 * standingActionMovingResidualWeight (anchor + 1)

theorem summable_standingActionMovingResetModel :
    Summable standingActionMovingResetModel := by
  have baseSeries : Summable fun index : Nat =>
      1 / ((index : Real) ^ (5 / 4 : Real)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have shiftedSeries : Summable fun index : Nat =>
      1 / (((index + 2 : Nat) : Real) ^ (5 / 4 : Real)) := by
    have addTwoInjective : Function.Injective
        (fun index : Nat => index + 2) := by
      intro left right equality
      exact Nat.add_right_cancel equality
    have shifted : Summable
        ((fun index : Nat => 1 / ((index : Real) ^ (5 / 4 : Real))) ∘
          fun index : Nat => index + 2) :=
      baseSeries.comp_injective addTwoInjective
    exact shifted.congr fun index => by rfl
  have coefficientNe : standingActionMovingScalePowerCoefficient ≠ 0 :=
    standingActionMovingScalePowerCoefficient_pos.ne'
  apply (shiftedSeries.mul_left
    (2 / standingActionMovingScalePowerCoefficient)).congr
  intro anchor
  unfold standingActionMovingResetModel
    standingActionMovingResidualWeight
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [show (anchor : Real) + 2 = (anchor : Real) + 1 + 1 by ring]
  field_simp [coefficientNe]

def standingActionMovingResetReserve (anchor : Nat) : Real :=
  ∑' offset : Nat, standingActionMovingResetModel (anchor + offset)

theorem standingActionMovingResetReserve_nonneg (anchor : Nat) :
    0 ≤ standingActionMovingResetReserve anchor := by
  unfold standingActionMovingResetReserve
  apply tsum_nonneg
  intro offset
  unfold standingActionMovingResetModel
  exact mul_nonneg (by norm_num)
    (standingActionMovingResidualWeight_pos _).le

theorem standingActionMovingResetReserve_step (anchor : Nat) :
    standingActionMovingResetReserve anchor =
      standingActionMovingResetModel anchor +
        standingActionMovingResetReserve (anchor + 1) := by
  let shifted := fun offset : Nat =>
    standingActionMovingResetModel (anchor + offset)
  have shiftedSummable : Summable shifted := by
    dsimp only [shifted]
    have shiftedRight : Summable fun offset =>
        standingActionMovingResetModel (offset + anchor) :=
      (summable_nat_add_iff
        (f := standingActionMovingResetModel) anchor).mpr
          summable_standingActionMovingResetModel
    exact shiftedRight.congr fun offset => by rw [Nat.add_comm]
  have split := shiftedSummable.sum_add_tsum_nat_add 1
  simpa only [standingActionMovingResetReserve, shifted,
    Finset.sum_range_one, Nat.add_zero, Nat.add_assoc, Nat.one_add,
    Nat.add_comm, Nat.add_left_comm] using split.symm

/-- At every reachable high standing, the first reset row already dominates
the physical seventh-order clock model at either neighbouring coefficient
level.  This is pure source arithmetic: the `5/4` reset weight decays much
more slowly than the seventh-order clock. -/
theorem standingActionBarrierModel_le_nextResidualWeight
    (anchor level : Nat)
    (anchorLower : 88 ≤ anchor)
    (levelNeighbour : level = anchor ∨ level + 1 = anchor) :
    standingActionBarrierModel butterflyGainViscosity level ≤
      standingActionMovingResidualWeight (anchor + 1) := by
  have levelLower : 87 ≤ level := by
    rcases levelNeighbour with rfl | neighbour
    · omega
    · omega
  have anchorLeLevelAddOne : anchor ≤ level + 1 := by
    rcases levelNeighbour with rfl | neighbour <;> omega
  have levelOne : (1 : Real) ≤ (level : Real) := by
    exact_mod_cast (show 1 ≤ level by omega)
  have levelNonneg : (0 : Real) ≤ (level : Real) := by positivity
  have anchorBaseOne : (1 : Real) ≤ (anchor : Real) + 2 := by
    have anchorNonneg : (0 : Real) ≤ (anchor : Real) := by positivity
    linarith
  have anchorBaseLeLevelSq :
      (anchor : Real) + 2 ≤ (level : Real) ^ (2 : Nat) := by
    have castAnchorLe : (anchor : Real) ≤ (level : Real) + 1 := by
      exact_mod_cast anchorLeLevelAddOne
    have levelLarge : (3 : Real) ≤ (level : Real) := by
      exact_mod_cast (show 3 ≤ level by omega)
    nlinarith [sq_nonneg ((level : Real) - 2)]
  have anchorPowerLeSquare :
      ((anchor : Real) + 2) ^ (5 / 4 : Real) ≤
        ((anchor : Real) + 2) ^ (2 : Nat) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le anchorBaseOne
        (by norm_num : (5 / 4 : Real) ≤ 2)
  have anchorSquareLeLevelFourth :
      ((anchor : Real) + 2) ^ (2 : Nat) ≤
        (level : Real) ^ (4 : Nat) := by
    have leftNonneg : 0 ≤ (anchor : Real) + 2 := by positivity
    have rightNonneg : 0 ≤ (level : Real) ^ (2 : Nat) := by positivity
    have squared := mul_self_le_mul_self leftNonneg anchorBaseLeLevelSq
    norm_num [pow_succ] at squared ⊢
    nlinarith
  have levelFourthLeSeventh :
      (level : Real) ^ (4 : Nat) ≤ (level : Real) ^ (7 : Nat) := by
    have cubeOne : (1 : Real) ≤ (level : Real) ^ (3 : Nat) :=
      one_le_pow₀ levelOne
    have fourthNonneg : 0 ≤ (level : Real) ^ (4 : Nat) := by positivity
    nlinarith [mul_nonneg fourthNonneg (sub_nonneg.mpr cubeOne)]
  have powerLe :
      ((anchor : Real) + 2) ^ (5 / 4 : Real) ≤
        (level : Real) ^ (7 : Nat) :=
    anchorPowerLeSquare.trans
      (anchorSquareLeLevelFourth.trans levelFourthLeSeventh)
  have coefficientOne : (1 : Real) ≤
      sourceOwnedWholeStateBarrierSeventhCoefficient
        butterflyGainViscosity :=
    butterflyGainBarrierSeventhCoefficient_gt_one.le
  have denominatorLe :
      standingActionMovingScalePowerCoefficient *
          (((anchor + 1 : Nat) : Real) + 1) ^ (5 / 4 : Real) ≤
        sourceOwnedWholeStateBarrierSeventhCoefficient
            butterflyGainViscosity *
          (level : Real) ^ (7 : Nat) := by
    have scaleLe := standingActionMovingScalePowerCoefficient_le_one
    have powerNonneg : 0 ≤
        ((anchor : Real) + 2) ^ (5 / 4 : Real) :=
      Real.rpow_nonneg (by positivity) _
    have levelPowerNonneg : 0 ≤ (level : Real) ^ (7 : Nat) := by positivity
    have first := mul_le_mul_of_nonneg_right scaleLe powerNonneg
    have first' :
        standingActionMovingScalePowerCoefficient *
            ((anchor : Real) + 2) ^ (5 / 4 : Real) ≤
          ((anchor : Real) + 2) ^ (5 / 4 : Real) := by
      simpa only [one_mul] using first
    have second := powerLe.trans
      (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right coefficientOne levelPowerNonneg)
    calc
      standingActionMovingScalePowerCoefficient *
            (((anchor + 1 : Nat) : Real) + 1) ^ (5 / 4 : Real) =
          standingActionMovingScalePowerCoefficient *
            ((anchor : Real) + 2) ^ (5 / 4 : Real) := by
        congr 2
        norm_num [Nat.cast_add]
        ring
      _ ≤ _ := first'.trans second
  have denominatorPos : 0 <
      standingActionMovingScalePowerCoefficient *
        (((anchor + 1 : Nat) : Real) + 1) ^ (5 / 4 : Real) := by
    exact mul_pos standingActionMovingScalePowerCoefficient_pos
      (Real.rpow_pos_of_pos (by positivity) _)
  unfold standingActionBarrierModel standingActionMovingResidualWeight
  simpa only [one_div] using
    one_div_le_one_div_of_le denominatorPos denominatorLe

theorem two_mul_barrierModel_le_movingResetReserve
    (anchor level : Nat)
    (anchorLower : 88 ≤ anchor)
    (levelNeighbour : level = anchor ∨ level + 1 = anchor) :
    2 * standingActionBarrierModel butterflyGainViscosity level ≤
      standingActionMovingResetReserve anchor := by
  have modelLeWeight := standingActionBarrierModel_le_nextResidualWeight
    anchor level anchorLower levelNeighbour
  have step := standingActionMovingResetReserve_step anchor
  have nextReserveNonneg := standingActionMovingResetReserve_nonneg
    (anchor + 1)
  unfold standingActionMovingResetModel at step
  linarith

/-- Advancing one cell releases enough finite tail reserve to install the
successor's uniformly bounded residual bankroll at the smaller next weight. -/
theorem two_mul_nextWeight_le_resetReserve_drop (anchor : Nat) :
    2 * standingActionMovingResidualWeight (anchor + 1) ≤
      standingActionMovingResetReserve anchor -
        standingActionMovingResetReserve (anchor + 1) := by
  have step := standingActionMovingResetReserve_step anchor
  unfold standingActionMovingResetModel at step
  linarith

def standingActionMovingClockPotential (stage : Nat) : Real :=
  let anchor := (source.stateAfter stage).1.standing.anchorLevel
  standingActionBarrierTail butterflyGainViscosity anchor +
    standingActionMovingResetReserve anchor +
      standingActionMovingResidualWeight anchor *
        standingActionMovingResidualPotential stage

theorem standingActionMovingClockPotential_nonneg (stage : Nat) :
    0 ≤ standingActionMovingClockPotential stage := by
  unfold standingActionMovingClockPotential
  exact add_nonneg
    (add_nonneg (standingActionBarrierTail_nonneg _ _)
      (standingActionMovingResetReserve_nonneg _))
    (mul_nonneg (standingActionMovingResidualWeight_pos _).le
      (standingActionMovingResidualPotential_nonneg stage))

def standingActionMovingClockState (stage : Nat) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) where
  potential := standingActionMovingClockPotential stage
  potential_nonneg := standingActionMovingClockPotential_nonneg stage

/-- Causally prepaid clock face.  The moving/root reserve and the physical
kinetic entropy are installed together before the current outcome is
resolved.  Kinetic entropy is antitone on every actual edge, so adding this
account never asks a successor branch to refill it. -/
def standingActionMovingKineticClockPotential (stage : Nat) : Real :=
  standingActionMovingClockPotential stage +
    puncturedWholeVorticityKineticMass
        (source.stateAfter stage).1.physical.contact.physicalState /
      (2 * butterflyGainViscosity.coeff)

theorem standingActionMovingKineticClockPotential_nonneg (stage : Nat) :
    0 ≤ standingActionMovingKineticClockPotential stage := by
  unfold standingActionMovingKineticClockPotential
  exact add_nonneg
    (standingActionMovingClockPotential_nonneg stage)
    (div_nonneg
      (puncturedWholeVorticityKineticMass_nonneg _)
      (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le))

def standingActionMovingKineticClockState (stage : Nat) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) where
  potential := standingActionMovingKineticClockPotential stage
  potential_nonneg :=
    standingActionMovingKineticClockPotential_nonneg stage

/-- Any settlement already paid by the moving account lifts to the prepaid
moving/kinetic face.  The lift consumes only the exact kinetic antitonicity
of the same physical edge. -/
def standingActionMovingKineticClockAdvance_of_movingAdvance
    (stage : Nat)
    (advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1))) :
    SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (standingActionMovingKineticClockState stage)
      (standingActionMovingKineticClockState (stage + 1)) := by
  have movingDomination :
      source.clockAt (source.stateAfter stage) +
          standingActionMovingClockPotential (stage + 1) ≤
        standingActionMovingClockPotential stage := by
    have settlement := advance.settlement
    have wasteNonneg := advance.waste_nonneg
    change
      standingActionMovingClockPotential stage =
        source.clockAt (source.stateAfter stage) +
          standingActionMovingClockPotential (stage + 1) + advance.waste
      at settlement
    linarith
  have kineticLe := nextContact_kineticMass_le
    (source.stateAfter stage).1.physical
  have nextKineticEq :
      puncturedWholeVorticityKineticMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState =
        puncturedWholeVorticityKineticMass
          (source.stateAfter stage).1.physical.nextContact.physicalState := by
    rfl
  have denominatorPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have kineticScaled :=
    (div_le_div_iff_of_pos_right denominatorPos).2 kineticLe
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt (source.stateAfter stage) +
        standingActionMovingKineticClockPotential (stage + 1) ≤
      standingActionMovingKineticClockPotential stage
  unfold standingActionMovingKineticClockPotential
  rw [nextKineticEq]
  linarith

/-- Exact one-cell branches pay the physical clock with the canonical
barrier tail and simultaneously fund the uniformly bounded successor
residual bankroll.  Both accounts live in the same clock state. -/
def standingActionMovingClockRootExactAdvance
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1)) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have materialCommutes : material.arithmeticMaterial.whole =
      material.arithmeticMaterial.left.parallel
        material.arithmeticMaterial.right := by
    unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
      at commutes
    rw [effect.effect_eq] at commutes
    exact commutes
  have paid := standingActionRootExact_paymentIncrement_eq_one effect commutes
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel + 1 := by
    change state.1.standing.next.anchorLevel = _
    rw [cellStanding_anchorLevel_next, paid]
  have clockLe := standingActionRootExact_clock_le_barrierModel
    stackedInitialActionMaterialInstruction stage effect commutes
  have anchorCurrent : state.1.standing.anchorLevel =
      (runCellStanding stackedShortCurrent stage).anchorLevel := by
    have currentEq : state.1 = runRuntime stackedShortCurrent stage := by
      exact standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    rw [currentEq]
    rfl
  rw [← anchorCurrent] at clockLe
  have clockLe' : source.clockAt state ≤
      standingActionBarrierModel butterflyGainViscosity
        state.1.standing.anchorLevel := by
    simpa only [state, source, stackedStandingActionMediumSource] using clockLe
  have resetLt :=
    standingActionMovingResidualPotential_next_lt_two_of_exact
      stage materialCommutes
  have currentBankrollNonneg :=
    standingActionMovingResidualPotential_nonneg stage
  have currentWeightNonneg :=
    (standingActionMovingResidualWeight_pos
      state.1.standing.anchorLevel).le
  have nextWeightPos := standingActionMovingResidualWeight_pos
    (state.1.standing.anchorLevel + 1)
  have weightedResetLt :
      standingActionMovingResidualWeight
            (state.1.standing.anchorLevel + 1) *
          standingActionMovingResidualPotential (stage + 1) <
        2 * standingActionMovingResidualWeight
          (state.1.standing.anchorLevel + 1) :=
    by
      simpa only [mul_comm] using
        (mul_lt_mul_of_pos_left resetLt nextWeightPos)
  have resetDrop := two_mul_nextWeight_le_resetReserve_drop
    state.1.standing.anchorLevel
  have barrierStep := standingActionBarrierTail_step
    butterflyGainViscosity state.1.standing.anchorLevel
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt state +
        (standingActionBarrierTail butterflyGainViscosity
              nextState.1.standing.anchorLevel +
          standingActionMovingResetReserve
              nextState.1.standing.anchorLevel +
            standingActionMovingResidualWeight
                nextState.1.standing.anchorLevel *
              standingActionMovingResidualPotential (stage + 1)) ≤
      standingActionBarrierTail butterflyGainViscosity
            state.1.standing.anchorLevel +
        standingActionMovingResetReserve state.1.standing.anchorLevel +
          standingActionMovingResidualWeight state.1.standing.anchorLevel *
            standingActionMovingResidualPotential stage
  rw [anchorNext, barrierStep]
  nlinarith [clockLe']

def standingActionMovingKineticClockRootExactAdvance
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingKineticClockState stage)
      (standingActionMovingKineticClockState (stage + 1)) :=
  standingActionMovingKineticClockAdvance_of_movingAdvance stage
    (standingActionMovingClockRootExactAdvance stage effect commutes)

/-- On a root residual the remaining-cell debt absorbs the complete
whole-mass debit, while the moving tail absorbs its complementary liability.
Their single current-side potential therefore has the signed moving edge as
its exact coboundary. -/
theorem standingActionMovingResidualPotential_coboundary
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial) :
    standingActionMovingResidualPotential stage -
        standingActionMovingResidualPotential (stage + 1) =
      runMovingInventoryEdgePayment stackedShortCurrent
        shiftedStandingActionInventory (stage + 1) := by
  let material := nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter stage)
  have standingResidual := material.standingResidualOf residual
  have deficit := material.standingMaterial.deficit_commutes
  rw [material.standingMaterial.paymentShadow_eq_zero_of_residual
    standingResidual] at deficit
  norm_num at deficit
  rw [material.standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq,
    material.standingMaterial.rawValuedMaterial.sourcePhysicalState_eq,
    material.standingMaterial.rawValuedMaterial.targetPhysicalState_eq]
      at deficit
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
      at deficit
  have physicalCurrentEq :
      (source.stateAfter stage).1.physical =
        run stackedShortCurrent stage := by
    have currentEq :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    exact congrArg (fun current => current.physical) currentEq
  have massDebitEq :
      wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.nextContact.physicalState -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState =
        wholeVorticityEuclideanMass
            (run stackedShortCurrent (stage + 1)).contact.physicalState -
          wholeVorticityEuclideanMass
            (run stackedShortCurrent stage).contact.physicalState := by
    rw [physicalCurrentEq, run_succ, next_contact]
    rfl
  have nextSourceDeficit :
      (nativeRestartStandingActionValuedArithmeticMaterial
          (source.stateAfter (stage + 1))).standingMaterial.sourceRemainingDeficit =
        material.standingMaterial.targetRemainingDeficit := by
    change
      (source.stateAfter (stage + 1)).1.standing.remainingCellDeficit =
        material.standingMaterial.targetStanding.remainingCellDeficit
    rw [material.standingMaterial.targetStanding_eq]
    rfl
  have massLiability :=
    standingActionMovingEdgePayment_add_wholeMassLiability_eq_tailDrop stage
  have deficitDrop :
      (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).standingMaterial.sourceRemainingDeficit -
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).standingMaterial.targetRemainingDeficit =
        wholeVorticityEuclideanMass
            (run stackedShortCurrent (stage + 1)).contact.physicalState -
          wholeVorticityEuclideanMass
            (run stackedShortCurrent stage).contact.physicalState := by
    dsimp only [material] at deficit
    calc
      _ = wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState -
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState := by
          rw [deficit]
          abel_nf
          ac_rfl
      _ = _ := massDebitEq
  unfold standingActionMovingResidualPotential
  rw [nextSourceDeficit]
  dsimp only [material]
  linarith [deficitDrop, massLiability]

/-- Both coupled constructors are standing residuals.  Their compiler-owned
successor therefore retains the exact same anchor; no scale-threshold
increment belongs in their local source settlement. -/
theorem standingActionAnchorLevel_succ_eq_of_residual
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial) :
    (source.stateAfter (stage + 1)).1.standing.anchorLevel =
      (source.stateAfter stage).1.standing.anchorLevel := by
  let state := source.stateAfter stage
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have standingResidual := material.standingResidualOf residual
  have shadowZero :=
    material.standingMaterial.paymentShadow_eq_zero_of_residual
      standingResidual
  have incrementZero : state.1.standing.paymentIncrement = 0 := by
    rw [material.standingMaterial.paymentShadow_eq] at shadowZero
    exact shadowZero
  change state.1.standing.next.anchorLevel = state.1.standing.anchorLevel
  rw [cellStanding_anchorLevel_next, incrementZero, Nat.add_zero]

/-- On a root residual the shared anchor and reset reserve remain fixed;
the weighted moving bankroll is therefore the entire clock currency. -/
def standingActionMovingClockRootResidualAdvance
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (payment : source.clockAt (source.stateAfter stage) ≤
      standingActionMovingResidualWeight
          (source.stateAfter stage).1.standing.anchorLevel *
        runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1)) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1)) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have standingResidual := material.standingResidualOf residual
  have shadowZero :=
    material.standingMaterial.paymentShadow_eq_zero_of_residual
      standingResidual
  have incrementZero : state.1.standing.paymentIncrement = 0 := by
    rw [material.standingMaterial.paymentShadow_eq] at shadowZero
    exact shadowZero
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel := by
    change state.1.standing.next.anchorLevel = _
    rw [cellStanding_anchorLevel_next, incrementZero, Nat.add_zero]
  have coboundary :=
    standingActionMovingResidualPotential_coboundary stage residual
  have scaledCoboundary := congrArg
    (fun value : Real =>
      standingActionMovingResidualWeight state.1.standing.anchorLevel * value)
    coboundary
  have payment' : source.clockAt state ≤
      standingActionMovingResidualWeight state.1.standing.anchorLevel *
        runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1) := by
    simpa only [state] using payment
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt state +
        (standingActionBarrierTail butterflyGainViscosity
              nextState.1.standing.anchorLevel +
          standingActionMovingResetReserve
              nextState.1.standing.anchorLevel +
            standingActionMovingResidualWeight
                nextState.1.standing.anchorLevel *
              standingActionMovingResidualPotential (stage + 1)) ≤
      standingActionBarrierTail butterflyGainViscosity
            state.1.standing.anchorLevel +
        standingActionMovingResetReserve state.1.standing.anchorLevel +
          standingActionMovingResidualWeight state.1.standing.anchorLevel *
            standingActionMovingResidualPotential stage
  rw [anchorNext]
  nlinarith [scaledCoboundary]

/-- The natural source scale law for the moving clock.  Its `5/4` power is
cancelled exactly by the recursively summable anchor weight. -/
noncomputable def standingActionMovingClockRootResidualAdvance_of_scalePowerFloor
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (powerFloor : ∀ actual ∈ Set.Icc (0 : Real)
        (run stackedShortCurrent (stage + 1)).contact.time.1,
      standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) ≤
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          (standingActionRunInventory stage) actual) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1)) := by
  let anchorBase : Real :=
    ((source.stateAfter stage).1.standing.anchorLevel : Real) + 1
  have anchorBasePos : 0 < anchorBase := by
    dsimp only [anchorBase]
    positivity
  have anchorPowerPos : 0 <
      standingActionMovingScalePowerCoefficient *
        anchorBase ^ (5 / 4 : Real) :=
    mul_pos standingActionMovingScalePowerCoefficient_pos
      (Real.rpow_pos_of_pos anchorBasePos _)
  have integralLower := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume)
    (run stackedShortCurrent (stage + 1)).contact.time_pos.le
    (continuous_const.intervalIntegrable 0
      (run stackedShortCurrent (stage + 1)).contact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
      (standingActionRunInventory stage)).intervalIntegrable
        0 (run stackedShortCurrent (stage + 1)).contact.time.1)
    powerFloor
  have scaledClockLeIntegral :
      (standingActionMovingScalePowerCoefficient *
          anchorBase ^ (5 / 4 : Real)) *
          (run stackedShortCurrent (stage + 1)).contact.time.1 ≤
        ∫ actual in (0 : Real)..
            (run stackedShortCurrent (stage + 1)).contact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
            (standingActionRunInventory stage) actual := by
    simpa [anchorBase, intervalIntegral.integral_const, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using integralLower
  have scaledClockLeEdge := scaledClockLeIntegral.trans
    (standingActionProjectedPowerIntegral_le_movingEdgePayment stage)
  have sourceClockEq :
      source.clockAt (source.stateAfter stage) =
        (run stackedShortCurrent (stage + 1)).contact.time.1 := by
    have currentEq :
        (source.stateAfter stage).1.physical =
          run stackedShortCurrent stage := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction stage
      exact congrArg (fun current => current.physical) generated
    change
      (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [currentEq, run_succ, next_contact]
  have weightEq :
      standingActionMovingResidualWeight
          (source.stateAfter stage).1.standing.anchorLevel =
        (standingActionMovingScalePowerCoefficient *
          anchorBase ^ (5 / 4 : Real))⁻¹ := by
    unfold standingActionMovingResidualWeight
    dsimp only [anchorBase]
    rw [one_div]
  have payment : source.clockAt (source.stateAfter stage) ≤
      standingActionMovingResidualWeight
          (source.stateAfter stage).1.standing.anchorLevel *
        runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1) := by
    rw [sourceClockEq, weightEq]
    have scaled := mul_le_mul_of_nonneg_left scaledClockLeEdge
      (inv_nonneg.mpr anchorPowerPos.le)
    rw [← mul_assoc, inv_mul_cancel₀ anchorPowerPos.ne', one_mul] at scaled
    exact scaled
  exact standingActionMovingClockRootResidualAdvance stage residual payment

/-- Total root settlement under one branch-free actual-path scale law.
Exact incidence consumes the barrier/reset account; both residual outcomes
consume the weighted moving bankroll. -/
noncomputable def standingActionMovingClockRootSettlement_of_scalePowerFloor
    (stage : Nat)
    (powerFloor : ∀ actual ∈ Set.Icc (0 : Real)
        (run stackedShortCurrent (stage + 1)).contact.time.1,
      standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) ≤
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          (standingActionRunInventory stage) actual) :
    SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact .exactPayment
        (standingActionMovingClockRootExactAdvance stage effect commutes)
  | generatedResidual effect residual expansion expansionEq payment =>
      have canonicalResidual : GeneratedParallelResidualAt
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage))
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial := by
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at residual
        rw [effect.effect_eq] at residual
        exact residual
      exact .generatedResidual
        (standingActionMovingClockRootResidualAdvance_of_scalePowerFloor
          stage canonicalResidual powerFloor)
  | obstruction obstruction demand =>
      have canonicalResidual : GeneratedParallelResidualAt
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage))
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial := by
        have residual := obstruction.residual
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at residual
        rw [obstruction.effect.effect_eq] at residual
        exact residual
      exact .obstructionAlternative
        (standingActionMovingClockRootResidualAdvance_of_scalePowerFloor
          stage canonicalResidual powerFloor)

/-- Current-only physical invariant consumed by the total moving clock
settlement.  It is indexed by the actual run occurrence and contains no
future branch or successor proof. -/
def ButterflyMovingScalePowerAt (stage : Nat) : Prop :=
  ∀ actual ∈ Set.Icc (0 : Real)
      (run stackedShortCurrent (stage + 1)).contact.time.1,
    standingActionMovingScalePowerCoefficient *
        (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
        (standingActionRunInventory stage) actual

/-- Exact endpoint transport: one full-path invariant occurrence becomes
the time-zero power instruction of the generated successor receipt. -/
theorem ButterflyMovingScalePowerAt.endpoint_power_margin
    {stage : Nat}
    (invariant : ButterflyMovingScalePowerAt stage) :
    standingActionMovingScalePowerCoefficient *
        (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        (run stackedShortCurrent (stage + 1)).nextReceipt
        (standingActionRunInventory stage) 0 := by
  have endpoint := invariant
    (run stackedShortCurrent (stage + 1)).contact.time.1
    ⟨(run stackedShortCurrent (stage + 1)).contact.time_pos.le, le_rfl⟩
  rw [run_succ, next_contact] at endpoint
  have seam := next_netPower_zero_eq_current_selectedEndpoint
    (run stackedShortCurrent stage) (standingActionRunInventory stage)
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).nextContact.prefixReceipt
          (standingActionRunInventory stage)
          (run stackedShortCurrent stage).nextContact.time.1 := by
    rw [run_succ]
    exact seam
  rw [powerEq]
  exact endpoint

/-- Exact inventory-expansion seam for the local source advance.  Retained
rows transport automatically; the newly installed action rows pay only the
change of the anchor-normalized threshold. -/
theorem ButterflyMovingScalePowerAt.next_zero_margin_of_newRows
    {stage : Nat}
    (invariant : ButterflyMovingScalePowerAt stage)
    (newRowsPay :
      (standingActionMovingScalePowerCoefficient *
            (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
              (5 / 4 : Real) -
          standingActionMovingScalePowerCoefficient *
            (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
              (5 / 4 : Real)) ≤
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0) :
    standingActionMovingScalePowerCoefficient *
        (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        (run stackedShortCurrent (stage + 1)).nextReceipt
        (standingActionRunInventory (stage + 1)) 0 := by
  have retained := invariant.endpoint_power_margin
  have split := actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    (run stackedShortCurrent (stage + 1)).nextReceipt
    (standingActionRunInventory stage)
    (standingActionRunInventory (stage + 1))
    (standingActionRunInventory_nested stage)
  rw [split]
  linarith

def standingActionMovingResidualClockState (stage : Nat) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) where
  potential := standingActionMovingResidualPotential stage
  potential_nonneg := standingActionMovingResidualPotential_nonneg stage

/-- Exact interface boundary for the coupled constructors.  Once the root
residual is fixed, the compiler-owned moving bankroll generates a clock
advance exactly when its signed physical edge pays this occurrence's clock.
No successor liability or alternate potential remains hidden behind the
root-clock interface. -/
theorem standingActionMovingResidualClockAdvance_nonempty_iff
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial) :
    Nonempty (SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (standingActionMovingResidualClockState stage)
        (standingActionMovingResidualClockState (stage + 1))) ↔
      source.clockAt (source.stateAfter stage) ≤
        runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1) := by
  have coboundary :=
    standingActionMovingResidualPotential_coboundary stage residual
  constructor
  · rintro ⟨advance⟩
    have settlement := advance.settlement
    have wasteNonneg := advance.waste_nonneg
    change
      standingActionMovingResidualPotential stage =
        source.clockAt (source.stateAfter stage) +
          standingActionMovingResidualPotential (stage + 1) +
            advance.waste at settlement
    linarith
  · intro payment
    refine ⟨sourceGeneratedRootClockAdvance_of_potential_domination ?_⟩
    change
      source.clockAt (source.stateAfter stage) +
          standingActionMovingResidualPotential (stage + 1) ≤
        standingActionMovingResidualPotential stage
    linarith

/-- Direct analytic splice into the coupled clock consumer.  A complete
actual-path unit power floor on the compiler-owned inventory pays the same
occurrence's clock, hence generates the root advance through the moving
bankroll.  This is a subordinate source theorem; the final public law must
generate `powerFloor` recursively rather than expose it as a premise. -/
noncomputable def standingActionMovingResidualClockAdvance_of_projectedPowerFloor
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (powerFloor : ∀ actual ∈ Set.Icc (0 : Real)
        (run stackedShortCurrent (stage + 1)).contact.time.1,
      (1 : Real) ≤
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          (standingActionRunInventory stage) actual) :
    SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (standingActionMovingResidualClockState stage)
      (standingActionMovingResidualClockState (stage + 1)) := by
  have integralLower := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume)
    (run stackedShortCurrent (stage + 1)).contact.time_pos.le
    (continuous_const.intervalIntegrable 0
      (run stackedShortCurrent (stage + 1)).contact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
      (standingActionRunInventory stage)).intervalIntegrable
        0 (run stackedShortCurrent (stage + 1)).contact.time.1)
    powerFloor
  have clockLeIntegral :
      (run stackedShortCurrent (stage + 1)).contact.time.1 ≤
        ∫ actual in (0 : Real)..
            (run stackedShortCurrent (stage + 1)).contact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
            (standingActionRunInventory stage) actual := by
    simpa [intervalIntegral.integral_const, smul_eq_mul] using integralLower
  have clockLeEdge := clockLeIntegral.trans
    (standingActionProjectedPowerIntegral_le_movingEdgePayment stage)
  have sourceClockEq :
      source.clockAt (source.stateAfter stage) =
        (run stackedShortCurrent (stage + 1)).contact.time.1 := by
    have currentEq :
        (source.stateAfter stage).1.physical =
          run stackedShortCurrent stage := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction stage
      exact congrArg (fun current => current.physical) generated
    change
      (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [currentEq, run_succ, next_contact]
  have payment : source.clockAt (source.stateAfter stage) ≤
      runMovingInventoryEdgePayment stackedShortCurrent
        shiftedStandingActionInventory (stage + 1) := by
    rw [sourceClockEq]
    exact clockLeEdge
  exact Classical.choice
    ((standingActionMovingResidualClockAdvance_nonempty_iff
      stage residual).2 payment)

/-- The canonical core charge and its complete complement/action residual
recombine exactly to the actual whole-action readout. -/
theorem actualDyadicWholeActionReadout_eq_core_add_complement
    (state : source.State) :
    actualDyadicWholeActionReadout state =
      state.2.yCellCoreCharge + state.2.yCellComplementActionReadout := by
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have axis := congrArg (fun row : ComplexCoordinateVector => (row 1).re)
    (material.wholeAction_commutes state.2.dyadicChildAxis)
  have plusZero := congrArg
    (fun row : ComplexCoordinateVector => (row 0).re)
    (material.wholeAction_commutes state.2.dyadicChildPlus)
  have plusTwo := congrArg
    (fun row : ComplexCoordinateVector => (row 2).re)
    (material.wholeAction_commutes state.2.dyadicChildPlus)
  have minusZero := congrArg
    (fun row : ComplexCoordinateVector => (row 0).re)
    (material.wholeAction_commutes state.2.dyadicChildMinus)
  have minusTwo := congrArg
    (fun row : ComplexCoordinateVector => (row 2).re)
    (material.wholeAction_commutes state.2.dyadicChildMinus)
  rw [material.actionInstruction_eq] at axis plusZero plusTwo minusZero minusTwo
  unfold actualDyadicWholeActionReadout
    SourceGeneratedActionMaterialInstructionAt.yCellCoreCharge
    SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge
    SourceGeneratedActionMaterialInstructionAt.yCellComplementActionReadout
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
  simp only [Pi.add_apply, Complex.add_re]
    at axis plusZero plusTwo minusZero minusTwo
  simp only [Pi.add_apply, Complex.add_re]
  linarith

/-- Faithful source form of the coupled clock sector.  The nominal y-cell
clock is paid by the actual whole action, the exact Euler write-back, and the
same current-side capacity/kinetic debits. -/
theorem rootResidual_kineticCompensated_domination_iff_actualAction
    (alpha : Real)
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    let state := source.stateAfter stage
    let nextState := source.stateAfter (stage + 1)
    source.clockAt state +
          kineticCompensatedPotential alpha nextState ≤
        kineticCompensatedPotential alpha state ↔
      source.clockAt state * state.2.yCellCoreCharge ≤
        standingActionRootResidualFaceCapacityDrop state +
          alpha * state.2.yCellCoreCharge *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState) +
          source.clockAt state * actualDyadicWholeActionReadout state +
          state.2.yCellEulerErrorReadout := by
  dsimp only
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  have sector := rootResidual_kineticCompensated_domination_iff
    alpha stage effect rootResidual
  have endpoint := state.2.yCellEndpointResidualReadout_eq_action_add_euler
  have actual := actualDyadicWholeActionReadout_eq_core_add_complement state
  have materialEndpoint :
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).endpointResidualReadout =
          (source.stateAfter stage).2.yCellEndpointResidualReadout := rfl
  have clockEq : source.clockAt (source.stateAfter stage) =
      (source.stateAfter stage).1.physical.nextContact.time.1 := rfl
  dsimp only [state, nextState] at endpoint actual ⊢
  dsimp only [source, stackedStandingActionMediumSource] at sector materialEndpoint clockEq endpoint actual ⊢
  rw [sector, materialEndpoint, endpoint, actual, clockEq]
  constructor <;> intro domination <;> linarith

/-! ## Total-disposition kinetic splice -/

/-- Fixed current-side kinetic coefficient.  It converts the exact kinetic
drop of the selected receipt into its whole prefix-mass payment; it contains
no stage table or future branch. -/
def butterflyActionKineticCoefficient : Real :=
  (2 * butterflyGainViscosity.coeff)⁻¹

theorem butterflyActionKineticCoefficient_nonneg :
    0 ≤ butterflyActionKineticCoefficient := by
  unfold butterflyActionKineticCoefficient
  exact inv_nonneg.mpr
    (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le)

def butterflyActionKineticClockState (stage : Nat) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) :=
  kineticCompensatedClockState butterflyActionKineticCoefficient
    butterflyActionKineticCoefficient_nonneg (source.stateAfter stage)

/-- A settlement already generated by one of the four immediate constructors
lifts to the kinetic-prepaid face using only kinetic antitonicity on the same
actual edge.  No reserve predicate is transported. -/
def butterflyActionKineticClockAdvance_of_mixedAdvance
    (stage : Nat)
    (advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (standingActionMixedClockState (source.stateAfter stage))
      (standingActionMixedClockState (source.stateAfter (stage + 1)))) :
    SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyActionKineticClockState stage)
      (butterflyActionKineticClockState (stage + 1)) := by
  have mixedDomination :
      source.clockAt (source.stateAfter stage) +
          standingActionMixedClockPotential (source.stateAfter (stage + 1)) ≤
        standingActionMixedClockPotential (source.stateAfter stage) := by
    have settlement := advance.settlement
    have wasteNonneg := advance.waste_nonneg
    change
      standingActionMixedClockPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          standingActionMixedClockPotential (source.stateAfter (stage + 1)) +
            advance.waste at settlement
    linarith
  have kineticLe := nextContact_kineticMass_le
    (source.stateAfter stage).1.physical
  have nextKineticEq :
      puncturedWholeVorticityKineticMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState =
        puncturedWholeVorticityKineticMass
          (source.stateAfter stage).1.physical.nextContact.physicalState := by
    rfl
  have scaledKineticLe := mul_le_mul_of_nonneg_left kineticLe
    butterflyActionKineticCoefficient_nonneg
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt (source.stateAfter stage) +
        kineticCompensatedPotential butterflyActionKineticCoefficient
          (source.stateAfter (stage + 1)) ≤
      kineticCompensatedPotential butterflyActionKineticCoefficient
        (source.stateAfter stage)
  unfold kineticCompensatedPotential
  rw [nextKineticEq]
  linarith

def butterflyActionKineticClockSettlement_of_mixedSettlement
    (stage : Nat)
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (settlement : SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMixedClockState (source.stateAfter stage))
      (standingActionMixedClockState (source.stateAfter (stage + 1)))
      outcome) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyActionKineticClockState stage)
      (butterflyActionKineticClockState (stage + 1)) outcome := by
  cases settlement with
  | exactPayment advance =>
      exact .exactPayment
        (butterflyActionKineticClockAdvance_of_mixedAdvance stage advance)
  | generatedResidual advance =>
      exact .generatedResidual
        (butterflyActionKineticClockAdvance_of_mixedAdvance stage advance)
  | obstructionAlternative advance =>
      exact .obstructionAlternative
        (butterflyActionKineticClockAdvance_of_mixedAdvance stage advance)
  | obstructionIncompatible incompatible =>
      exact .obstructionIncompatible incompatible

/-- The signed physical debit emitted by one genuinely coupled current.
Every summand is read from the same selected receipt and its installed action
material.  Positivity is deliberately not stored here: it is the concrete
source law still to be generated on the actual coupled constructors. -/
def butterflyCoupledActionKineticCurrentDebit (stage : Nat) : Real :=
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  standingActionRootResidualFaceCapacityDrop state +
      butterflyActionKineticCoefficient * state.2.yCellCoreCharge *
        (puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            nextState.1.physical.contact.physicalState) +
      source.clockAt state * actualDyadicWholeActionReadout state +
      state.2.yCellEulerErrorReadout -
    source.clockAt state * state.2.yCellCoreCharge

/-- The source-side obligation is exactly nonnegativity of the signed debit
generated above.  It contains no branch, future instruction or recurrence
argument. -/
def ButterflyCoupledActionKineticCurrentDebitAt (stage : Nat) : Prop :=
  0 ≤ butterflyCoupledActionKineticCurrentDebit stage

/-- On either actual coupled constructor, the signed debit is not a second
ledger: it is exactly the current kinetic/action clock coboundary, scaled by
the positive y-cell charge carried by the same material. -/
theorem butterflyCoupledActionKineticCurrentDebit_eq_clockCoboundary
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    butterflyCoupledActionKineticCurrentDebit stage =
      (source.stateAfter stage).2.yCellCoreCharge *
        (kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter stage) -
          kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter (stage + 1)) -
          source.clockAt (source.stateAfter stage)) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  have coboundary := rootResidual_kineticCompensated_coboundary
    butterflyActionKineticCoefficient stage effect rootResidual
  have actual := actualDyadicWholeActionReadout_eq_core_add_complement state
  have endpoint := state.2.yCellEndpointResidualReadout_eq_action_add_euler
  have materialEndpoint :
      (nativeRestartStandingActionValuedArithmeticMaterial
        state).endpointResidualReadout =
          state.2.yCellEndpointResidualReadout := rfl
  have clockEq : source.clockAt state =
      state.1.physical.nextContact.time.1 := rfl
  have actionRemainderEq :
      source.clockAt state * actualDyadicWholeActionReadout state +
            state.2.yCellEulerErrorReadout -
          source.clockAt state * state.2.yCellCoreCharge =
        (nativeRestartStandingActionValuedArithmeticMaterial
          state).endpointResidualReadout := by
    rw [clockEq, actual, materialEndpoint, endpoint]
    ring
  have debitEq :
      butterflyCoupledActionKineticCurrentDebit stage =
        standingActionRootResidualFaceCapacityDrop state +
          (nativeRestartStandingActionValuedArithmeticMaterial
            state).endpointResidualReadout +
          butterflyActionKineticCoefficient * state.2.yCellCoreCharge *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState) := by
    unfold butterflyCoupledActionKineticCurrentDebit
    dsimp only [state, nextState]
    dsimp only [state, nextState] at actionRemainderEq
    rw [← actionRemainderEq]
    ring
  dsimp only [state, nextState] at coboundary debitEq ⊢
  have scaled := congrArg
    (fun value : Real =>
      (source.stateAfter stage).2.yCellCoreCharge * value)
    coboundary
  rw [mul_add, mul_div_cancel₀ _
    (source.stateAfter stage).2.yCellCoreCharge_pos.ne'] at scaled
  rw [debitEq]
  nlinarith [scaled]

theorem butterflyCoupledActionKineticCurrentDebit_nonneg_iff
    (stage : Nat) :
    ButterflyCoupledActionKineticCurrentDebitAt stage ↔
      let state := source.stateAfter stage
      let nextState := source.stateAfter (stage + 1)
      source.clockAt state * state.2.yCellCoreCharge ≤
        standingActionRootResidualFaceCapacityDrop state +
          butterflyActionKineticCoefficient * state.2.yCellCoreCharge *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                nextState.1.physical.contact.physicalState) +
          source.clockAt state * actualDyadicWholeActionReadout state +
          state.2.yCellEulerErrorReadout := by
  unfold ButterflyCoupledActionKineticCurrentDebitAt
    butterflyCoupledActionKineticCurrentDebit
  dsimp only
  constructor <;> intro debit <;> linarith

/-- Current-only physical normal form of the signed debit.  The capacity and
kinetic rows collapse to the exact prefix mass of this selected receipt; the
only signed remainder is the same action surplus plus its Euler write-back. -/
theorem butterflyCoupledActionKineticCurrentDebit_eq_prefixAction
    (stage : Nat) :
    butterflyCoupledActionKineticCurrentDebit stage =
      let state := source.stateAfter stage
      let prefixMass := wholePrefixVorticityMass
        state.1.physical.nextContact.time
        state.1.physical.nextReceipt.stateLimit
      (2 * butterflyGainViscosity.coeff *
            finiteModeKineticAmbientFactor state.2.dyadicChildModes +
          state.2.yCellCoreCharge) * prefixMass +
        source.clockAt state *
          (actualDyadicWholeActionReadout state -
            state.2.yCellCoreCharge) +
        state.2.yCellEulerErrorReadout := by
  dsimp only
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  let prefixMass := wholePrefixVorticityMass
    state.1.physical.nextContact.time
    state.1.physical.nextReceipt.stateLimit
  have ledger := state.1.physical.nextContact_kineticDissipation_eq
  have dropEq :
      puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState =
        2 * butterflyGainViscosity.coeff * prefixMass := by
    dsimp only [prefixMass]
    linarith
  have nextKineticEq :
      puncturedWholeVorticityKineticMass
          nextState.1.physical.contact.physicalState =
        puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState := by
    rfl
  have capacityEq :
      standingActionRootResidualFaceCapacityDrop state =
        (2 * butterflyGainViscosity.coeff *
          finiteModeKineticAmbientFactor state.2.dyadicChildModes) *
            prefixMass := by
    unfold standingActionRootResidualFaceCapacityDrop
      standingPaidFaceCapacity
    rw [show state.1.next.physical.contact.physicalState =
      state.1.physical.nextContact.physicalState by rfl]
    calc
      finiteModeKineticAmbientFactor state.2.dyadicChildModes *
              puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
            finiteModeKineticAmbientFactor state.2.dyadicChildModes *
              puncturedWholeVorticityKineticMass
                state.1.physical.nextContact.physicalState =
          finiteModeKineticAmbientFactor state.2.dyadicChildModes *
            (puncturedWholeVorticityKineticMass
                state.1.physical.contact.physicalState -
              puncturedWholeVorticityKineticMass
                state.1.physical.nextContact.physicalState) := by ring
      _ = finiteModeKineticAmbientFactor state.2.dyadicChildModes *
          (2 * butterflyGainViscosity.coeff * prefixMass) := by rw [dropEq]
      _ = _ := by ring
  have coefficientNe : 2 * butterflyGainViscosity.coeff ≠ 0 :=
    (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos).ne'
  have kineticEq :
      butterflyActionKineticCoefficient * state.2.yCellCoreCharge *
          (puncturedWholeVorticityKineticMass
              state.1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
              nextState.1.physical.contact.physicalState) =
        state.2.yCellCoreCharge * prefixMass := by
    rw [nextKineticEq, dropEq]
    unfold butterflyActionKineticCoefficient
    field_simp [coefficientNe, butterflyGainViscosity.coeff_pos.ne']
  unfold butterflyCoupledActionKineticCurrentDebit
  dsimp only [state, nextState, prefixMass]
  dsimp only [state, nextState, prefixMass] at capacityEq kineticEq
  rw [capacityEq, kineticEq]
  ring

/-- The concrete current-side payment carried by the coupled action
material.  Both liability and payment are projections of the selected
receipt; this type contains no scalar supplied by a caller. -/
def ButterflyCoupledEndpointResidualPaymentAt (stage : Nat) : Prop :=
  let state := source.stateAfter stage
  let prefixMass := wholePrefixVorticityMass
    state.1.physical.nextContact.time
    state.1.physical.nextReceipt.stateLimit
  (-state.2.yCellEndpointResidualReadout) ≤
    (2 * butterflyGainViscosity.coeff *
          finiteModeKineticAmbientFactor state.2.dyadicChildModes +
        state.2.yCellCoreCharge) * prefixMass

/-- Final same-material mouth on a coupled action residual.  The normalizer's
negative endpoint readout is the entire liability; the current prefix mass is
the entire payment.  No headroom, next branch or future reserve survives. -/
theorem butterflyCoupledActionKineticCurrentDebit_iff_endpointResidual
    (stage : Nat) :
    ButterflyCoupledActionKineticCurrentDebitAt stage ↔
      ButterflyCoupledEndpointResidualPaymentAt stage := by
  let state := source.stateAfter stage
  have actual := actualDyadicWholeActionReadout_eq_core_add_complement state
  have endpoint := state.2.yCellEndpointResidualReadout_eq_action_add_euler
  have clockEq : source.clockAt state =
      state.1.physical.nextContact.time.1 := rfl
  have actionEq :
      source.clockAt state *
            (actualDyadicWholeActionReadout state -
              state.2.yCellCoreCharge) +
          state.2.yCellEulerErrorReadout =
        state.2.yCellEndpointResidualReadout := by
    rw [clockEq, actual, endpoint]
    ring
  unfold ButterflyCoupledActionKineticCurrentDebitAt
    ButterflyCoupledEndpointResidualPaymentAt
  rw [butterflyCoupledActionKineticCurrentDebit_eq_prefixAction stage]
  dsimp only
  dsimp only [state] at actionEq
  constructor <;> intro payment <;> linarith [actionEq]

/-- Exact selected-receipt form of the coupled debit.  The kinetic term is
definitionally the current prefix-mass payment after applying the source-fixed
coefficient; no density lower bound is introduced. -/
theorem butterflyCoupledActionKineticCurrentDebit_iff_prefixMass
    (stage : Nat) :
    ButterflyCoupledActionKineticCurrentDebitAt stage ↔
      let state := source.stateAfter stage
      source.clockAt state * state.2.yCellCoreCharge ≤
        standingActionRootResidualFaceCapacityDrop state +
          state.2.yCellCoreCharge *
            wholePrefixVorticityMass
              state.1.physical.nextContact.time
              state.1.physical.nextReceipt.stateLimit +
          source.clockAt state * actualDyadicWholeActionReadout state +
          state.2.yCellEulerErrorReadout := by
  dsimp only
  let state := source.stateAfter stage
  have ledger := state.1.physical.nextContact_kineticDissipation_eq
  have dropEq :
      puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState =
        2 * butterflyGainViscosity.coeff *
          wholePrefixVorticityMass
            state.1.physical.nextContact.time
            state.1.physical.nextReceipt.stateLimit := by
    linarith
  have coefficientNe : 2 * butterflyGainViscosity.coeff ≠ 0 :=
    (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos).ne'
  have kineticTermEq :
      butterflyActionKineticCoefficient * state.2.yCellCoreCharge *
          (puncturedWholeVorticityKineticMass
              state.1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
              (source.stateAfter (stage + 1)).1.physical.contact.physicalState) =
        state.2.yCellCoreCharge *
          wholePrefixVorticityMass
            state.1.physical.nextContact.time
            state.1.physical.nextReceipt.stateLimit := by
    have nextEq :
        puncturedWholeVorticityKineticMass
            (source.stateAfter (stage + 1)).1.physical.contact.physicalState =
          puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState := by
      rfl
    rw [nextEq, dropEq]
    unfold butterflyActionKineticCoefficient
    field_simp [coefficientNe, butterflyGainViscosity.coeff_pos.ne']
  unfold ButterflyCoupledActionKineticCurrentDebitAt
    butterflyCoupledActionKineticCurrentDebit
  dsimp only [state]
  rw [kineticTermEq]
  constructor <;> intro payment <;> linarith

/-- Endpoint-only normal form.  The action and Euler rows recombine exactly
into the physical dyadic-face readout gain of this selected contact.  Thus the
live source theorem is a single current-edge inequality, not a hidden
coercivity or recurrence interface. -/
theorem butterflyCoupledActionKineticCurrentDebit_iff_faceGain
    (stage : Nat) :
    ButterflyCoupledActionKineticCurrentDebitAt stage ↔
      let state := source.stateAfter stage
      source.clockAt state * state.2.yCellCoreCharge ≤
        standingActionRootResidualFaceCapacityDrop state +
          state.2.yCellCoreCharge *
            wholePrefixVorticityMass
              state.1.physical.nextContact.time
              state.1.physical.nextReceipt.stateLimit +
          (state.2.dyadicChildReadout
                state.1.physical.nextContact.physicalState -
            state.2.dyadicChildReadout
              state.1.physical.contact.physicalState) := by
  rw [butterflyCoupledActionKineticCurrentDebit_iff_prefixMass stage]
  dsimp only
  let state := source.stateAfter stage
  have actual := actualDyadicWholeActionReadout_eq_core_add_complement state
  have endpoint := state.2.yCellEndpointResidualReadout_eq_action_add_euler
  have face := state.2.yCellFaceReadout_commutes
  have sourceClockEq : source.clockAt state =
      state.1.physical.nextContact.time.1 := rfl
  have actionEulerEq :
      source.clockAt state * actualDyadicWholeActionReadout state +
          state.2.yCellEulerErrorReadout =
        state.2.dyadicChildReadout
              state.1.physical.nextContact.physicalState -
          state.2.dyadicChildReadout
            state.1.physical.contact.physicalState := by
    calc
      source.clockAt state * actualDyadicWholeActionReadout state +
            state.2.yCellEulerErrorReadout =
          state.1.physical.nextContact.time.1 *
              (state.2.yCellCoreCharge +
                state.2.yCellComplementActionReadout) +
            state.2.yCellEulerErrorReadout := by
              rw [sourceClockEq, actual]
      _ = state.1.physical.nextContact.time.1 *
              state.2.yCellCoreCharge +
            state.2.yCellEndpointResidualReadout := by
              rw [endpoint]
              ring
      _ = _ := face.symm
  change
    (source.clockAt state * state.2.yCellCoreCharge ≤
      standingActionRootResidualFaceCapacityDrop state +
          state.2.yCellCoreCharge *
            wholePrefixVorticityMass
              state.1.physical.nextContact.time
              state.1.physical.nextReceipt.stateLimit +
        source.clockAt state * actualDyadicWholeActionReadout state +
          state.2.yCellEulerErrorReadout) ↔
      source.clockAt state * state.2.yCellCoreCharge ≤
        standingActionRootResidualFaceCapacityDrop state +
            state.2.yCellCoreCharge *
              wholePrefixVorticityMass
                state.1.physical.nextContact.time
                state.1.physical.nextReceipt.stateLimit +
          (state.2.dyadicChildReadout
                state.1.physical.nextContact.physicalState -
            state.2.dyadicChildReadout
              state.1.physical.contact.physicalState)
  constructor <;> intro payment <;> linarith [actionEulerEq]

/-- Whole fixed-output velocity convection is controlled by the current
kinetic mass, with no coefficient ceiling or Galerkin radius. -/
theorem wholeVelocityNonlinear_norm_le_kineticMass
    (state : ComplexVorticityHilbertState)
    (_stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    ‖wholeStateVelocityNonlinearCoefficientAt
        (wholeBiotSavartVelocityState state) output‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        puncturedWholeVorticityKineticMass state := by
  let modes : Nat → Finset IntegerWavevector :=
    puncturedIntegerWaveFrequencyCube
  let velocity := wholeBiotSavartVelocityState state
  have velocityZero : velocity 0 = 0 := by
    simp [velocity, wholeBiotSavartVelocityState_apply,
      finiteStateVelocityCoefficient, biotSavartVelocityCoefficient_zero]
  have projectedTendsto : Filter.Tendsto
      (fun radius => complexSharpSupportProjection (modes radius) velocity)
      Filter.atTop (nhds velocity) := by
    simpa only [modes] using
      complexSharpSupportProjection_puncturedCube_tendsto
        velocity velocityZero
  have projectedTransverse : ∀ radius,
      WholeStateTransverse
        (complexSharpSupportProjection (modes radius) velocity) :=
    fun radius => wholeStateTransverse_projection (modes radius) velocity
      (wholeBiotSavartVelocityState_transverse state)
  have coefficientTendsto : Filter.Tendsto
      (fun radius => finiteStateVelocityNonlinearCoefficientAt
        (modes radius) state output)
      Filter.atTop
      (nhds (wholeStateVelocityNonlinearCoefficientAt velocity output)) := by
    have generated := tendsto_wholeStateVelocityNonlinearCoefficientAt
      (fun radius => complexSharpSupportProjection (modes radius) velocity)
      velocity projectedTransverse
      (wholeBiotSavartVelocityState_transverse state)
      projectedTendsto output
    simpa only [← finiteStateWholeVelocity_eq_projection_wholeBiotSavart,
      wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity,
      velocity] using generated
  have finiteBound : ∀ radius,
      ‖finiteStateVelocityNonlinearCoefficientAt
          (modes radius) state output‖ ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          puncturedWholeVorticityKineticMass state := by
    intro radius
    have finite :=
      finiteStateVelocityNonlinearCoefficientAt_norm_le_kineticEnergy
        (modes radius) state output
    have kinetic :=
      two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
        (modes radius)
        (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
        state (fun wave _waveMem => stateTransverse wave)
    exact finite.trans
      (mul_le_mul_of_nonneg_left kinetic (by positivity))
  exact le_of_tendsto'
    ((continuous_norm.tendsto _).comp coefficientTendsto)
    finiteBound

/-- One fixed vorticity row has a source-only speed ceiling paid entirely
by the same current kinetic mass. -/
theorem wholeVorticityTangent_norm_le_kineticMass
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ‖wholeLatticeVorticityFourierTangentAt nu.coeff state output‖ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            puncturedWholeVorticityKineticMass state) +
        (nu.coeff * integerWaveViscousMultiplier output) *
          ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            Real.sqrt (puncturedWholeVorticityKineticMass state)) := by
  let kinetic := puncturedWholeVorticityKineticMass state
  let velocity := wholeBiotSavartVelocityState state
  have kineticNonneg : 0 ≤ kinetic :=
    puncturedWholeVorticityKineticMass_nonneg state
  have velocityRowAmplitudeLe :
      complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state output) ≤ kinetic := by
    have finiteKinetic :=
      two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
        ({output} : Finset IntegerWavevector)
        (by simpa using outputNe.symm)
        state (fun wave _waveMem => stateTransverse wave)
    have rowIdentity := velocityRowAmplitude_sq_sum_eq_two_kineticEnergy
      ({output} : Finset IntegerWavevector) state
    simp only [Finset.sum_singleton] at rowIdentity
    rw [← rowIdentity, velocityRowAmplitude_sq] at finiteKinetic
    exact finiteKinetic
  have velocityRowNormLe :
      ‖finiteStateVelocityCoefficient state output‖ ≤ Real.sqrt kinetic := by
    apply Real.le_sqrt_of_sq_le
    exact (complexCoordinateVector_norm_sq_le_amplitudeSq _).trans
      velocityRowAmplitudeLe
  have vorticityRowEq : state output =
      fourierCurlCoefficient output
        (finiteStateVelocityCoefficient state output) := by
    exact
      (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
        output (state output) outputNe (stateTransverse output)).symm
  have vorticityRowNormLe : ‖state output‖ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt kinetic := by
    rw [vorticityRowEq]
    exact (fourierCurlCoefficient_norm_le_six_pi_sqrt output _).trans
      (mul_le_mul_of_nonneg_left velocityRowNormLe (by positivity))
  have velocityNonlinearLe := wholeVelocityNonlinear_norm_le_kineticMass
    state stateZero stateTransverse output
  have nonlinearEq :=
    wholeStateVorticityNonlinearCoefficientAt_eq_fourierCurl_velocity
      state stateZero stateTransverse output
  have nonlinearLe :
      ‖wholeStateVorticityNonlinearCoefficientAt state output‖ ≤
        (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            kinetic) := by
    rw [nonlinearEq]
    exact (fourierCurlCoefficient_norm_le_six_pi_sqrt output _).trans
      (mul_le_mul_of_nonneg_left velocityNonlinearLe (by positivity))
  have dampingNonneg : 0 ≤ nu.coeff * integerWaveViscousMultiplier output :=
    mul_nonneg nu.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  unfold wholeLatticeVorticityFourierTangentAt
  calc
    ‖wholeStateVorticityNonlinearCoefficientAt state output -
        (nu.coeff * integerWaveViscousMultiplier output) • state output‖ ≤
      ‖wholeStateVorticityNonlinearCoefficientAt state output‖ +
        ‖(nu.coeff * integerWaveViscousMultiplier output) •
          state output‖ := norm_sub_le _ _
    _ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) * kinetic) +
        (nu.coeff * integerWaveViscousMultiplier output) *
          ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            Real.sqrt kinetic) := by
      apply add_le_add nonlinearLe
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg dampingNonneg]
      exact mul_le_mul_of_nonneg_left vorticityRowNormLe dampingNonneg
    _ = _ := rfl

/-- Current-side loss budget for one actual row at an arbitrary time of the
same generated replay.  It is the path-indexed form of the endpoint kinetic
face loss used by the standing material. -/
def fullReplayKineticSelfWorkLossUpperAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector) : Real :=
  let sourceTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let tangentDrift := fullReplayKineticTangentSourceUpper current wave
  3 * (time.1 * (‖sourceTangent‖ + tangentDrift)) *
      (‖sourceTangent‖ + tangentDrift) +
    3 * ‖current.contact.physicalState wave‖ * tangentDrift

theorem fullReplayKineticSelfWorkLossUpperAt_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector) :
    0 ≤ fullReplayKineticSelfWorkLossUpperAt current time wave := by
  unfold fullReplayKineticSelfWorkLossUpperAt
  have driftNonneg :=
    fullReplayKineticTangentSourceUpper_nonneg current wave
  have sumNonneg : 0 ≤
      ‖wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave‖ +
        fullReplayKineticTangentSourceUpper current wave :=
    add_nonneg (norm_nonneg _) driftNonneg
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg time.2.1 sumNonneg))
      sumNonneg)
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (norm_nonneg (current.contact.physicalState wave)))
      driftNonneg)

/-- Exact whole-replay transport of one self-work instruction.  No selected
endpoint, future branch, or recurrence appears in the statement. -/
theorem abs_fullReplay_selfTangentWork_sub_current_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    |complexCoordinateRealInner
          (current.nextReceipt.wholePath time wave)
          (wholeLatticeVorticityFourierTangentAt nu.coeff
            (current.nextReceipt.wholePath time) wave) -
        complexCoordinateRealInner
          (current.contact.physicalState wave)
          (wholeLatticeVorticityFourierTangentAt nu.coeff
            current.contact.physicalState wave)| ≤
      fullReplayKineticSelfWorkLossUpperAt current time wave := by
  let sourceState := current.contact.physicalState wave
  let targetState := current.nextReceipt.wholePath time wave
  let sourceTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let targetTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    (current.nextReceipt.wholePath time) wave
  let tangentDrift := fullReplayKineticTangentSourceUpper current wave
  have tangentDriftNonneg : 0 ≤ tangentDrift := by
    exact fullReplayKineticTangentSourceUpper_nonneg current wave
  have eulerError := fullReplay_row_sub_euler_norm_le_kineticSource
    current wave waveNe time
  have rowLe : ‖targetState - sourceState‖ ≤
      time.1 * (‖sourceTangent‖ + tangentDrift) := by
    have split : targetState - sourceState =
        time.1 • sourceTangent +
          (targetState - fullReplayEulerRow current time.1 wave) := by
      dsimp only [targetState, sourceState, sourceTangent]
      unfold fullReplayEulerRow
      module
    rw [split]
    calc
      ‖time.1 • sourceTangent +
          (targetState - fullReplayEulerRow current time.1 wave)‖ ≤
          ‖time.1 • sourceTangent‖ +
            ‖targetState - fullReplayEulerRow current time.1 wave‖ :=
        norm_add_le _ _
      _ ≤ time.1 * ‖sourceTangent‖ + time.1 * tangentDrift := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg time.2.1]
        exact add_le_add le_rfl eulerError
      _ = time.1 * (‖sourceTangent‖ + tangentDrift) := by ring
  have tangentLe : ‖targetTangent - sourceTangent‖ ≤ tangentDrift := by
    let zeroTime : Set.Icc (0 : Real)
        (wholeRestartDuration current.contact) :=
      ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
    have generated :=
      receipt_wholeLatticeVorticityTangent_sub_norm_le_kineticDrift
        current.nextReceipt wave waveNe zeroTime time time.2.1
    have driftLe :=
      receiptKineticVelocityDriftUpper_le_fullReplay current time
    have pathVelocityLe :=
      fullReplay_wholeBiotSavartVelocity_norm_le_radius current time
    have initialVelocityLe :=
      fullReplay_initialWholeBiotSavartVelocity_norm_le_radius current
    have zeroEq : current.nextReceipt.wholePath zeroTime =
        current.contact.physicalState :=
      current.nextReceipt.wholePath_initial
    rw [zeroEq] at generated
    have velocitySumLe :
        ‖wholeBiotSavartVelocityState
            (current.nextReceipt.wholePath time)‖ +
          ‖wholeBiotSavartVelocityState
            current.contact.physicalState‖ ≤
        2 * fullReplayKineticVelocityRadius current := by
      linarith
    have angularNonneg :
        0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) := by
      positivity
    have dampingNonneg :
        0 ≤ nu.coeff * integerWaveViscousMultiplier wave := by
      exact mul_nonneg nu.coeff_pos.le (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
    have coefficientLe :
        (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
              (‖wholeBiotSavartVelocityState
                  (current.nextReceipt.wholePath time)‖ +
                ‖wholeBiotSavartVelocityState
                  current.contact.physicalState‖) +
            nu.coeff * integerWaveViscousMultiplier wave ≤
          (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
              (2 * fullReplayKineticVelocityRadius current) +
            nu.coeff * integerWaveViscousMultiplier wave := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left velocitySumLe angularNonneg) le_rfl
    have productLe := mul_le_mul coefficientLe driftLe
      (receiptKineticVelocityDriftUpper_nonneg
        current.nextReceipt zeroTime time)
      (add_nonneg
        (mul_nonneg angularNonneg
          (mul_nonneg (by norm_num)
            (fullReplayKineticVelocityRadius_nonneg current)))
        dampingNonneg)
    have bounded := generated.trans
      (mul_le_mul_of_nonneg_left productLe angularNonneg)
    have boundedSource := bounded.trans
      (fullReplayKineticTangentDriftUpper_le_sourceUpper current wave)
    simpa only [targetTangent, sourceTangent, tangentDrift,
      fullReplayKineticTangentSourceUpper] using boundedSource
  have targetTangentLe : ‖targetTangent‖ ≤
      ‖sourceTangent‖ + tangentDrift := by
    calc
      ‖targetTangent‖ =
          ‖(targetTangent - sourceTangent) + sourceTangent‖ := by
        congr 1
        module
      _ ≤ ‖targetTangent - sourceTangent‖ + ‖sourceTangent‖ :=
        norm_add_le _ _
      _ ≤ tangentDrift + ‖sourceTangent‖ := by linarith
      _ = ‖sourceTangent‖ + tangentDrift := add_comm _ _
  have pairing := abs_complexCoordinateRealInner_pair_sub_le
    targetState sourceState targetTangent sourceTangent
  have firstLe :
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ ≤
        3 * (time.1 * (‖sourceTangent‖ + tangentDrift)) *
          (‖sourceTangent‖ + tangentDrift) := by
    have advanceNonneg : 0 ≤
        time.1 * (‖sourceTangent‖ + tangentDrift) :=
      mul_nonneg time.2.1
        (add_nonneg (norm_nonneg _) tangentDriftNonneg)
    calc
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ ≤
          3 * (time.1 * (‖sourceTangent‖ + tangentDrift)) *
            ‖targetTangent‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left rowLe (by norm_num))
          (norm_nonneg _)
      _ ≤ 3 * (time.1 * (‖sourceTangent‖ + tangentDrift)) *
          (‖sourceTangent‖ + tangentDrift) :=
        mul_le_mul_of_nonneg_left targetTangentLe
          (mul_nonneg (by norm_num) advanceNonneg)
  have secondLe :
      3 * ‖sourceState‖ * ‖targetTangent - sourceTangent‖ ≤
        3 * ‖sourceState‖ * tangentDrift := by
    gcongr
  unfold fullReplayKineticSelfWorkLossUpperAt
  dsimp only [targetState, sourceState, targetTangent, sourceTangent,
    tangentDrift] at pairing firstLe secondLe ⊢
  exact pairing.trans (add_le_add firstLe secondLe)

theorem stackedSeedKineticMass_lt_one :
    puncturedWholeVorticityKineticMass stackedSeedState < 1 := by
  rw [puncturedWholeVorticityKineticMass_eq_finite_of_supported
    butterflyFirstStackModes (by decide)
    stackedSeedState
    (butterflyFirstStackPhysicalState_supported (-1))]
  unfold stackedSeedState
  simp (config := { maxSteps := 3000000 })
    [butterflyFirstStackPhysicalState,
      finiteComplexVorticityState_apply, butterflyFirstStackModes,
      butterflyFirstStackRow, butterflyFirstYFaceModes,
      butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
      butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq,
      sidebandMinusY_eq, sidebandPlusZ_eq, sidebandMinusZ_eq,
      complexCoordinateAmplitudeSq, integerWaveViscousMultiplier,
      integerWaveNormSq, axisWave, pumpY, pumpZ,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
  all_goals norm_num [Complex.normSq_apply]
  all_goals ring_nf
  have piInvLt : Real.pi⁻¹ < (1 / 3 : Real) := by
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 3)
        Real.pi_gt_three)
  have piInvSqLt : Real.pi⁻¹ ^ 2 < (1 / 3 : Real) ^ 2 :=
    (sq_lt_sq₀ (inv_nonneg.mpr Real.pi_pos.le) (by norm_num)).2 piInvLt
  nlinarith

theorem stackedCurrentKineticMass_lt_one :
    puncturedWholeVorticityKineticMass
        stackedShortCurrent.contact.physicalState < 1 := by
  have kineticLe := wholeRestartWholePath_kineticMass_le
    (generatedWholeRestartCriticalClosure stackedReplay)
    stackedShortContactFullTime
  change puncturedWholeVorticityKineticMass
      (stackedReceipt.wholePath stackedShortContactFullTime) ≤
    puncturedWholeVorticityKineticMass stackedSeedState at kineticLe
  rw [← stackedShortContact_state_eq_full] at kineticLe
  exact kineticLe.trans_lt stackedSeedKineticMass_lt_one

theorem butterflyFirstStackModes_frequency_le_seventeen
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackModes) :
    integerWaveNormSq wave ≤ 17 := by
  simp only [butterflyFirstStackModes, butterflyFirstYFaceModes,
    butterflySeedModes, butterflyZTwoModes, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at waveMem
  rcases waveMem with
    ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl) |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [integerWaveNormSq, axisWave, pumpY, pumpZ,
      Fin.sum_univ_succ] <;> norm_num

theorem stackedShortCurrent_sourceRow_norm_lt_ten
    (wave : IntegerWavevector) :
    ‖stackedShortCurrent.contact.physicalState wave‖ < 10 := by
  have rowLe := lp.norm_apply_le_norm (by norm_num)
    stackedShortCurrent.contact.physicalState wave
  have normSqLe := wholeState_norm_sq_le_wholeVorticityEuclideanMass
    stackedShortCurrent.contact.physicalState
  have massLt := stackedShortContact_sourcePatch.2.1
  have normNonneg := norm_nonneg stackedShortCurrent.contact.physicalState
  nlinarith [sq_nonneg
    (‖stackedShortCurrent.contact.physicalState‖ + 10)]

theorem stackedShortCurrent_sourceTangent_norm_lt_hundredThousand
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackModes) :
    ‖wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        stackedShortCurrent.contact.physicalState wave‖ < 100000 := by
  have waveNe : wave ≠ 0 := fun waveZero => by
    subst wave
    exact butterflyFirstStackModes_zeroNotMem waveMem
  have frequencyLe :=
    butterflyFirstStackModes_frequency_le_seventeen wave waveMem
  have frequencyNonneg := integerWaveNormSq_nonneg wave
  have sqrtFrequencyLe : Real.sqrt (integerWaveNormSq wave) ≤ 17 := by
    exact (Real.sqrt_le_sqrt frequencyLe).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num)))
  have kineticLt := stackedCurrentKineticMass_lt_one
  have kineticNonneg := puncturedWholeVorticityKineticMass_nonneg
    stackedShortCurrent.contact.physicalState
  have sqrtKineticLe : Real.sqrt
      (puncturedWholeVorticityKineticMass
        stackedShortCurrent.contact.physicalState) ≤ 1 := by
    have squareEq := Real.sq_sqrt kineticNonneg
    nlinarith [Real.sqrt_nonneg
      (puncturedWholeVorticityKineticMass
        stackedShortCurrent.contact.physicalState)]
  have dampingLe : butterflyGainViscosity.coeff *
      integerWaveViscousMultiplier wave ≤ 1 := by
    unfold integerWaveViscousMultiplier
    calc
      butterflyGainViscosity.coeff *
            ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) =
          (butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) *
            integerWaveNormSq wave := by ring
      _ = (1 / 100 : Real) * integerWaveNormSq wave := by
        rw [butterflyGainViscosity_scaled]
        norm_num
      _ ≤ (1 / 100 : Real) * 17 := by gcongr
      _ ≤ 1 := by norm_num
  have generated := wholeVorticityTangent_norm_le_kineticMass
    butterflyGainViscosity stackedShortCurrent.contact.physicalState
    stackedShortCurrent.contact.physicalState_zero
    stackedShortCurrent.contact.transverse wave waveNe
  have piLe : Real.pi ≤ 4 := Real.pi_lt_four.le
  calc
    _ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
            puncturedWholeVorticityKineticMass
              stackedShortCurrent.contact.physicalState) +
        (butterflyGainViscosity.coeff *
            integerWaveViscousMultiplier wave) *
          ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
            Real.sqrt (puncturedWholeVorticityKineticMass
              stackedShortCurrent.contact.physicalState)) := generated
    _ ≤
      (6 * 4) * 17 * ((2 * 4) * 17 * 1) +
        1 * ((6 * 4) * 17 * 1) := by gcongr
    _ < 100000 := by norm_num

theorem stackedShortCurrent_tangentDrift_lt_inverse_trillion
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackModes) :
    fullReplayKineticTangentSourceUpper stackedShortCurrent wave <
      1 / (10 : Real) ^ 12 := by
  have frequencyLe :=
    butterflyFirstStackModes_frequency_le_seventeen wave waveMem
  have sqrtFrequencyLe : Real.sqrt (integerWaveNormSq wave) ≤ 17 := by
    exact (Real.sqrt_le_sqrt frequencyLe).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num)))
  have outerLe :
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) ≤ 408 := by
    calc
      _ ≤ (6 * 4 : Real) * 17 := by gcongr; exact Real.pi_lt_four.le
      _ = 408 := by norm_num
  have radiusLe : fullReplayKineticVelocityRadius
      stackedShortCurrent ≤ 17 := by
    unfold fullReplayKineticVelocityRadius
    rw [stackedShortCurrent_ceiling_eq_eighty_eight]
    have squareEq : (Real.sqrt (3 * (88 : Real))) ^ 2 = 3 * 88 := by
      rw [Real.sq_sqrt (by norm_num)]
    nlinarith [Real.sqrt_nonneg (3 * (88 : Real))]
  have dampingLe : butterflyGainViscosity.coeff *
      integerWaveViscousMultiplier wave ≤ 1 := by
    unfold integerWaveViscousMultiplier
    calc
      butterflyGainViscosity.coeff *
            ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) =
          (butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) *
            integerWaveNormSq wave := by ring
      _ = (1 / 100 : Real) * integerWaveNormSq wave := by
        rw [butterflyGainViscosity_scaled]
        norm_num
      _ ≤ (1 / 100 : Real) * 17 := by gcongr
      _ ≤ 1 := by norm_num
  have driftLt :=
    stackedShortCurrent_sourceKineticDrift_lt_inverse_ten_pow_nineteen
  have radiusNonneg := fullReplayKineticVelocityRadius_nonneg
    stackedShortCurrent
  have dampingNonneg : 0 ≤ butterflyGainViscosity.coeff *
      integerWaveViscousMultiplier wave := by
    exact mul_nonneg butterflyGainViscosity.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  unfold fullReplayKineticTangentSourceUpper
  calc
    _ ≤ 408 * ((408 * (2 * 17) + 1) *
          Real.sqrt
            (3 * wholeRestartDuration stackedShortCurrent.contact *
              fullReplayWholeTangentSquareSourceUpper
                stackedShortCurrent)) := by gcongr
    _ < 408 * ((408 * (2 * 17) + 1) *
          (1 / (10 : Real) ^ 19)) := by
      gcongr
    _ < 1 / (10 : Real) ^ 12 := by norm_num

theorem stackedShortCurrent_fullReplay_selfWorkLoss_lt_one_thousandth
    (time : Set.Icc (0 : Real)
      (wholeRestartDuration stackedShortCurrent.contact))
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackModes) :
    fullReplayKineticSelfWorkLossUpperAt stackedShortCurrent time wave <
      1 / 1000 := by
  have timeLt : time.1 < 1 / (10 : Real) ^ 40 :=
    time.2.2.trans_lt
      stackedShortCurrent_duration_lt_inverse_ten_pow_forty
  have rowLt := stackedShortCurrent_sourceRow_norm_lt_ten wave
  have tangentLt :=
    stackedShortCurrent_sourceTangent_norm_lt_hundredThousand wave waveMem
  have driftLt :=
    stackedShortCurrent_tangentDrift_lt_inverse_trillion wave waveMem
  have driftNonneg :=
    fullReplayKineticTangentSourceUpper_nonneg stackedShortCurrent wave
  have sumNonneg : 0 ≤
      ‖wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.contact.physicalState wave‖ +
        fullReplayKineticTangentSourceUpper stackedShortCurrent wave :=
    add_nonneg (norm_nonneg _) driftNonneg
  have sumLe :
      ‖wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.contact.physicalState wave‖ +
          fullReplayKineticTangentSourceUpper stackedShortCurrent wave ≤
        100000 + 1 / (10 : Real) ^ 12 :=
    add_le_add tangentLt.le driftLt.le
  have timeUpperNonneg : 0 ≤ (1 / (10 : Real) ^ 40) := by positivity
  have sumUpperNonneg :
      0 ≤ (100000 + 1 / (10 : Real) ^ 12) := by positivity
  have driftUpperNonneg : 0 ≤ (1 / (10 : Real) ^ 12) := by positivity
  have firstLe :
      3 * (time.1 *
          (‖wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              stackedShortCurrent.contact.physicalState wave‖ +
            fullReplayKineticTangentSourceUpper stackedShortCurrent wave)) *
          (‖wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              stackedShortCurrent.contact.physicalState wave‖ +
            fullReplayKineticTangentSourceUpper stackedShortCurrent wave) ≤
        3 * ((1 / (10 : Real) ^ 40) *
          (100000 + 1 / (10 : Real) ^ 12)) *
            (100000 + 1 / (10 : Real) ^ 12) := by
    have timeSumLe :
        time.1 *
            (‖wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                stackedShortCurrent.contact.physicalState wave‖ +
              fullReplayKineticTangentSourceUpper stackedShortCurrent wave) ≤
          (1 / (10 : Real) ^ 40) *
            (100000 + 1 / (10 : Real) ^ 12) :=
      mul_le_mul timeLt.le sumLe sumNonneg timeUpperNonneg
    have threeTimeSumNonneg : 0 ≤
        3 * (time.1 *
          (‖wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              stackedShortCurrent.contact.physicalState wave‖ +
            fullReplayKineticTangentSourceUpper stackedShortCurrent wave)) :=
      mul_nonneg (by norm_num)
        (mul_nonneg time.2.1 sumNonneg)
    have firstFactor :
        3 * (time.1 *
            (‖wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                stackedShortCurrent.contact.physicalState wave‖ +
              fullReplayKineticTangentSourceUpper stackedShortCurrent wave)) *
            (‖wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                stackedShortCurrent.contact.physicalState wave‖ +
              fullReplayKineticTangentSourceUpper stackedShortCurrent wave) ≤
          3 * (time.1 *
            (‖wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                stackedShortCurrent.contact.physicalState wave‖ +
              fullReplayKineticTangentSourceUpper stackedShortCurrent wave)) *
            (100000 + 1 / (10 : Real) ^ 12) :=
      mul_le_mul_of_nonneg_left sumLe threeTimeSumNonneg
    have scaledTimeSumLe := mul_le_mul_of_nonneg_left timeSumLe
      (by norm_num : (0 : Real) ≤ 3)
    have secondFactor := mul_le_mul_of_nonneg_right scaledTimeSumLe
      sumUpperNonneg
    exact firstFactor.trans secondFactor
  have secondLe :
      3 * ‖stackedShortCurrent.contact.physicalState wave‖ *
          fullReplayKineticTangentSourceUpper stackedShortCurrent wave ≤
        3 * 10 * (1 / (10 : Real) ^ 12) := by
    have productLe :
        ‖stackedShortCurrent.contact.physicalState wave‖ *
            fullReplayKineticTangentSourceUpper stackedShortCurrent wave ≤
          10 * (1 / (10 : Real) ^ 12) :=
      mul_le_mul rowLt.le driftLt.le driftNonneg (by norm_num)
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left productLe
        (by norm_num : (0 : Real) ≤ 3))
  unfold fullReplayKineticSelfWorkLossUpperAt
  calc
    _ ≤
      3 * ((1 / (10 : Real) ^ 40) *
          (100000 + 1 / (10 : Real) ^ 12)) *
            (100000 + 1 / (10 : Real) ^ 12) +
        3 * 10 * (1 / (10 : Real) ^ 12) := by
      exact add_le_add firstLe secondLe
    _ < 1 / 1000 := by norm_num

theorem finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork
    (nu : Viscosity)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteWholeNetEnstrophyPowerAt nu modes state =
      2 * ∑ wave ∈ modes, kineticSelfTangentWorkAt nu state wave := by
  unfold finiteWholeNetEnstrophyPowerAt kineticSelfTangentWorkAt
    wholeLatticeVorticityFourierTangentAt
  simp_rw [complexCoordinateRealInner_sub_right]
  rw [Finset.sum_sub_distrib]
  ring

/-- Finite physical power and complete action energy are two valuations of
the same current material.  Cauchy--Schwarz prevents a positive projected
power floor from being carried by a vanishing whole NS tangent. -/
theorem finiteWholeNetEnstrophyPowerAt_sq_le_mass_mul_actionSquare
    (nu : Viscosity)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (finiteWholeNetEnstrophyPowerAt nu modes state) ^ 2 ≤
      4 * finiteStateVorticityCoefficientEnstrophy modes state *
        (∑ wave ∈ modes,
          complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              nu.coeff state wave)) := by
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (r := fun wave => kineticSelfTangentWorkAt nu state wave)
    (f := fun wave => complexCoordinateAmplitudeSq (state wave))
    (g := fun wave => complexCoordinateAmplitudeSq
      (wholeLatticeVorticityFourierTangentAt nu.coeff state wave)) modes
    (fun wave _waveMem => complexCoordinateAmplitudeSq_nonneg _)
    (fun wave _waveMem => complexCoordinateAmplitudeSq_nonneg _)
    (fun wave _waveMem =>
      complexCoordinateRealInner_sq_le
        (state wave)
        (wholeLatticeVorticityFourierTangentAt nu.coeff state wave))
  rw [finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  unfold kineticSelfTangentWorkAt at cauchy ⊢
  unfold finiteStateVorticityCoefficientEnstrophy
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at cauchy ⊢
  nlinarith

/-- The complete sixteen-row source action remains strictly positive on the
entire canonical replay generated from the selected stacked current. -/
theorem stackedShortCurrent_fullReplay_sourcePower_gt_two
    (time : Set.Icc (0 : Real)
      (wholeRestartDuration stackedShortCurrent.contact)) :
    (2 : Real) < actualProjectedWholeNetEnstrophyPower
      stackedShortCurrent.nextReceipt butterflyFirstStackModes time.1 := by
  let sourceWork : IntegerWavevector → Real := fun wave =>
    kineticSelfTangentWorkAt butterflyGainViscosity
      stackedShortCurrent.contact.physicalState wave
  let targetWork : IntegerWavevector → Real := fun wave =>
    kineticSelfTangentWorkAt butterflyGainViscosity
      (stackedShortCurrent.nextReceipt.wholePath time) wave
  have rowLower : ∀ wave ∈ butterflyFirstStackModes,
      sourceWork wave - 1 / 1000 < targetWork wave := by
    intro wave waveMem
    have waveNe : wave ≠ 0 := fun waveZero => by
      subst wave
      exact butterflyFirstStackModes_zeroNotMem waveMem
    have absolute := abs_fullReplay_selfTangentWork_sub_current_le
      stackedShortCurrent time wave waveNe
    have loss :=
      stackedShortCurrent_fullReplay_selfWorkLoss_lt_one_thousandth
        time wave waveMem
    dsimp only [sourceWork, targetWork, kineticSelfTangentWorkAt]
      at absolute ⊢
    have negativeAbsolute := neg_abs_le
      (complexCoordinateRealInner
          (stackedShortCurrent.nextReceipt.wholePath time wave)
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            (stackedShortCurrent.nextReceipt.wholePath time) wave) -
        complexCoordinateRealInner
          (stackedShortCurrent.contact.physicalState wave)
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            stackedShortCurrent.contact.physicalState wave))
    linarith
  have modesNonempty : butterflyFirstStackModes.Nonempty :=
    ⟨axisWave 4, by simp [butterflyFirstStackModes,
      butterflyFirstYFaceModes]⟩
  have sumLower :
      (∑ wave ∈ butterflyFirstStackModes,
          (sourceWork wave - 1 / 1000)) <
        ∑ wave ∈ butterflyFirstStackModes, targetWork wave := by
    apply Finset.sum_lt_sum_of_nonempty modesNonempty
    intro wave waveMem
    exact rowLower wave waveMem
  have cardEq : butterflyFirstStackModes.card = 16 := by decide
  have sumLower' :
      (∑ wave ∈ butterflyFirstStackModes, sourceWork wave) -
          16 / 1000 <
        ∑ wave ∈ butterflyFirstStackModes, targetWork wave := by
    rw [Finset.sum_sub_distrib] at sumLower
    simp only [Finset.sum_const, nsmul_eq_mul, cardEq] at sumLower
    norm_num at sumLower ⊢
    exact sumLower
  have zeroPower :=
    stackedShortCurrent_nextReceipt_wholePower_zero_gt_three
  have stateAtTime :
      (actualWholeProjectedTransversePath
        stackedShortCurrent.nextReceipt time.1).1 =
          stackedShortCurrent.nextReceipt.wholePath time := by
    change stackedShortCurrent.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedShortCurrent.contact)
          stackedShortCurrent.nextReceipt.requestedTimePos.le time.1) = _
    rw [Set.projIcc_of_mem
      stackedShortCurrent.nextReceipt.requestedTimePos.le time.2]
  have stateAtZero :
      (actualWholeProjectedTransversePath
        stackedShortCurrent.nextReceipt 0).1 =
          stackedShortCurrent.contact.physicalState := by
    change stackedShortCurrent.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedShortCurrent.contact)
          stackedShortCurrent.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem
      stackedShortCurrent.nextReceipt.requestedTimePos.le
      ⟨le_rfl, stackedShortCurrent.nextReceipt.requestedTimePos.le⟩]
    exact stackedShortCurrent.nextReceipt.wholePath_initial
  have timePowerEq :
      actualProjectedWholeNetEnstrophyPower
          stackedShortCurrent.nextReceipt butterflyFirstStackModes time.1 =
        2 * ∑ wave ∈ butterflyFirstStackModes, targetWork wave := by
    rw [actualProjectedWholeNetEnstrophyPower_eq_static, stateAtTime,
      finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  have zeroPowerEq :
      actualProjectedWholeNetEnstrophyPower
          stackedShortCurrent.nextReceipt butterflyFirstStackModes 0 =
        2 * ∑ wave ∈ butterflyFirstStackModes, sourceWork wave := by
    rw [actualProjectedWholeNetEnstrophyPower_eq_static, stateAtZero,
      finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  rw [timePowerEq]
  rw [zeroPowerEq] at zeroPower
  linarith

theorem standingActionInitial_anchorLevel_eq_eightyEight :
    (source.stateAfter 0).1.standing.anchorLevel = 88 := by
  change (runCellStanding stackedShortCurrent 0).anchorLevel = 88
  exact stackedStageZeroStanding_anchorLevel_eq

theorem standingActionInitial_scalePowerThreshold_lt_two :
    standingActionMovingScalePowerCoefficient *
        (((source.stateAfter 0).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real) < 2 := by
  have upperOne : (1 : Real) ≤
      sourceOwnedWholeStateBarrierSeventhCoefficientUpper
        butterflyGainViscosity := by
    unfold sourceOwnedWholeStateBarrierSeventhCoefficientUpper
    linarith [
      ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption.sourceOwnedLocalQuadraticFifthCoefficientUpper_nonneg
        butterflyGainViscosity]
  have quarterPowerLeOne :
      (1 / 4 : Real) ^ (5 / 4 : Real) ≤ 1 := by
    have generated := Real.rpow_le_rpow
      (show (0 : Real) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : Real) ≤ 1 by norm_num)
      (show (0 : Real) ≤ 5 / 4 by norm_num)
    simpa using generated
  have denominatorPos : 0 <
      sourceOwnedWholeStateBarrierSeventhCoefficientUpper
          butterflyGainViscosity * 4 ^ (7 : Nat) := by
    positivity
  have chargeLe :
      fullReceiptRetainedCharge butterflyGainViscosity 1 ≤
        1 / (4 : Real) ^ (7 : Nat) := by
    have numeratorLe :
        (1 : Real) * (1 / 4 : Real) ^ (5 / 4 : Real) ≤ 1 := by
      simpa only [one_mul] using quarterPowerLeOne
    have first :
        fullReceiptRetainedCharge butterflyGainViscosity 1 ≤
          1 /
            (sourceOwnedWholeStateBarrierSeventhCoefficientUpper
              butterflyGainViscosity * 4 ^ (7 : Nat)) := by
      unfold fullReceiptRetainedCharge
      exact div_le_div_of_nonneg_right numeratorLe denominatorPos.le
    have denominatorLe : (4 : Real) ^ (7 : Nat) ≤
        sourceOwnedWholeStateBarrierSeventhCoefficientUpper
            butterflyGainViscosity * 4 ^ (7 : Nat) := by
      nlinarith [show (0 : Real) ≤ 4 ^ (7 : Nat) by positivity]
    exact first.trans
      (one_div_le_one_div_of_le (by positivity) denominatorLe)
  have coefficientLe : standingActionMovingScalePowerCoefficient ≤
      1 / (4 : Real) ^ (8 : Nat) := by
    unfold standingActionMovingScalePowerCoefficient
    have divided := div_le_div_of_nonneg_right chargeLe
      (by norm_num : (0 : Real) ≤ 4)
    norm_num at divided ⊢
    exact divided
  have powerLe : (89 : Real) ^ (5 / 4 : Real) ≤
      (89 : Real) ^ (2 : Nat) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : Real) ≤ 89)
        (by norm_num : (5 / 4 : Real) ≤ 2))
  have productLe := mul_le_mul coefficientLe powerLe
    (Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 89) _)
    (by positivity : (0 : Real) ≤ 1 / 4 ^ (8 : Nat))
  rw [standingActionInitial_anchorLevel_eq_eightyEight]
  norm_num at productLe ⊢
  exact productLe.trans_lt (by norm_num)

/-- The finite source side of the recursive moving-clock law is now closed
without a caller premise.  Stage zero reads the complete sixteen-row source
carrier; later stages remain compiler-capture inventories. -/
theorem butterflyMovingScalePowerAt_zero :
    ButterflyMovingScalePowerAt 0 := by
  intro actual actualMem
  have actualMem' : actual ∈ Set.Icc (0 : Real)
      stackedShortCurrent.nextContact.time.1 := by
    simpa only [run_succ, next_contact, run_zero] using actualMem
  let fullTime : Set.Icc (0 : Real)
      (wholeRestartDuration stackedShortCurrent.contact) :=
    ⟨actual, actualMem'.1,
      actualMem'.2.trans stackedShortCurrent.nextContact.time.2.2⟩
  have fullPower := stackedShortCurrent_fullReplay_sourcePower_gt_two fullTime
  have stateEq :
      (actualWholeProjectedTransversePath
          (run stackedShortCurrent 1).contact.prefixReceipt actual).1 =
        (actualWholeProjectedTransversePath
          stackedShortCurrent.nextReceipt actual).1 := by
    change stackedShortCurrent.nextContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) stackedShortCurrent.nextContact.time.1
          stackedShortCurrent.nextContact.time_pos.le actual) =
      stackedShortCurrent.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedShortCurrent.contact)
          stackedShortCurrent.nextReceipt.requestedTimePos.le actual)
    rw [Set.projIcc_of_mem
      stackedShortCurrent.nextContact.time_pos.le actualMem']
    rw [Set.projIcc_of_mem
      stackedShortCurrent.nextReceipt.requestedTimePos.le fullTime.2]
    rfl
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent 1).contact.prefixReceipt
          (standingActionRunInventory 0) actual =
        actualProjectedWholeNetEnstrophyPower
          stackedShortCurrent.nextReceipt butterflyFirstStackModes actual := by
    simp only [standingActionRunInventory]
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [stateEq]
  rw [powerEq]
  exact standingActionInitial_scalePowerThreshold_lt_two.le.trans
    fullPower.le

/-- Rowwise source-tangent transport summed without replacing the actual
current by a radius-only ball.  This is the finite prepaid correction read
from the same receipt and inventory as the moving action. -/
theorem abs_fullReplay_netPower_sub_zero_le_sum_selfWorkLoss
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    |actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 -
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0| ≤
      2 * ∑ wave ∈ modes,
        fullReplayKineticSelfWorkLossUpperAt current time wave := by
  let sourceWork : IntegerWavevector → Real := fun wave =>
    kineticSelfTangentWorkAt nu current.contact.physicalState wave
  let targetWork : IntegerWavevector → Real := fun wave =>
    kineticSelfTangentWorkAt nu (current.nextReceipt.wholePath time) wave
  have stateAtTime :
      (actualWholeProjectedTransversePath current.nextReceipt time.1).1 =
        current.nextReceipt.wholePath time := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le time.1) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  have rowBound : ∀ wave ∈ modes,
      |targetWork wave - sourceWork wave| ≤
        fullReplayKineticSelfWorkLossUpperAt current time wave := by
    intro wave waveMem
    have waveNe : wave ≠ 0 := fun waveZero =>
      zeroNotMem (waveZero ▸ waveMem)
    simpa only [targetWork, sourceWork, kineticSelfTangentWorkAt] using
      abs_fullReplay_selfTangentWork_sub_current_le
        current time wave waveNe
  rw [actualProjectedWholeNetEnstrophyPower_eq_static,
    actualProjectedWholeNetEnstrophyPower_eq_static,
    stateAtTime, stateAtZero,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  change
    |2 * ∑ wave ∈ modes, targetWork wave -
        2 * ∑ wave ∈ modes, sourceWork wave| ≤ _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  calc
    |2 * ∑ wave ∈ modes, (targetWork wave - sourceWork wave)| =
        2 * |∑ wave ∈ modes, (targetWork wave - sourceWork wave)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    _ ≤ 2 * ∑ wave ∈ modes,
        |targetWork wave - sourceWork wave| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ wave ∈ modes,
        fullReplayKineticSelfWorkLossUpperAt current time wave := by
      gcongr with wave waveMem
      exact rowBound wave waveMem

/-- Source-owned prepaid form of the moving scale-power invariant.  The
current occurrence retains enough time-zero power to pay both its scale
threshold and every rowwise transport correction on the same generated
receipt.  It contains no successor proposition or completed stage table. -/
def ButterflyMovingScalePowerReserveAt (stage : Nat) : Prop :=
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        2 * ∑ wave ∈ modes,
          fullReplayKineticSelfWorkLossUpperAt current time wave ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0

/-- The prepaid occurrence projects to the exact full-path power law used by
the frozen root clock consumer.  The projection spends only the correction
stored on that same receipt. -/
theorem ButterflyMovingScalePowerReserveAt.power
    {stage : Nat}
    (reserve : ButterflyMovingScalePowerReserveAt stage) :
    ButterflyMovingScalePowerAt stage := by
  intro actual actualMem
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  let time : Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨actual, actualMem.1,
      actualMem.2.trans current.nextContact.time.2.2⟩
  have drift := abs_fullReplay_netPower_sub_zero_le_sum_selfWorkLoss
    current modes (standingActionRunInventory_zeroNotMem stage) time
  have paid := reserve time
  have lowerDrift := neg_abs_le
    (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0)
  have timePowerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          modes actual =
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes time.1 := by
    change
      actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes actual =
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes time.1
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    have stateEq :
        (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 =
          (actualWholeProjectedTransversePath
            current.nextReceipt time.1).1 := by
      change current.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) current.nextContact.time.1
            current.nextContact.time_pos.le actual) =
        current.nextReceipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
            current.nextReceipt.requestedTimePos.le time.1)
      rw [Set.projIcc_of_mem current.nextContact.time_pos.le actualMem]
      rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
      rfl
    rw [stateEq]
  rw [timePowerEq]
  dsimp only [current, modes] at drift paid lowerDrift ⊢
  linarith

/-- The prepaid power row forces a quantitative complete-action row on the
same current inventory.  This is the vertical information retained by the
reserve and was unavailable from the weaker full-path floor alone. -/
theorem ButterflyMovingScalePowerReserveAt.actionSquare_lower
    {stage : Nat}
    (reserve : ButterflyMovingScalePowerReserveAt stage) :
    (standingActionMovingScalePowerCoefficient *
        (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real)) ^ 2 ≤
      4 * ((source.stateAfter stage).1.standing.anchorLevel : Real) *
        (∑ wave ∈ standingActionRunInventory stage,
          complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              (run stackedShortCurrent stage).contact.physicalState wave)) := by
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  let threshold := standingActionMovingScalePowerCoefficient *
    (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
      (5 / 4 : Real)
  let actionSquare := ∑ wave ∈ modes,
    complexCoordinateVectorNormSq
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff current.contact.physicalState wave)
  let zero : Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨0, le_rfl, (wholeRestartDuration_pos current.contact).le⟩
  have paid := reserve zero
  have correctionNonneg : 0 ≤
      2 * ∑ wave ∈ modes,
        fullReplayKineticSelfWorkLossUpperAt current zero wave := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun wave _waveMem =>
      fullReplayKineticSelfWorkLossUpperAt_nonneg current zero wave
  have thresholdLePower : threshold ≤
      actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes 0 := by
    dsimp only [current, modes, threshold, zero] at paid correctionNonneg ⊢
    linarith
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  have powerEq :
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 =
        finiteWholeNetEnstrophyPowerAt butterflyGainViscosity modes
          current.contact.physicalState := by
    rw [actualProjectedWholeNetEnstrophyPower_eq_static, stateAtZero]
  have thresholdPos : 0 < threshold := by
    dsimp only [threshold]
    exact mul_pos standingActionMovingScalePowerCoefficient_pos
      (Real.rpow_pos_of_pos (by positivity) _)
  have powerNonneg : 0 ≤
      finiteWholeNetEnstrophyPowerAt butterflyGainViscosity modes
        current.contact.physicalState := by
    rw [← powerEq]
    exact thresholdPos.le.trans thresholdLePower
  have thresholdSquareLe : threshold ^ 2 ≤
      (finiteWholeNetEnstrophyPowerAt butterflyGainViscosity modes
        current.contact.physicalState) ^ 2 := by
    rw [← powerEq]
    nlinarith [sq_nonneg
      (actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes 0 - threshold)]
  have cauchy := finiteWholeNetEnstrophyPowerAt_sq_le_mass_mul_actionSquare
    butterflyGainViscosity modes current.contact.physicalState
  have finiteMassLeWhole :=
    finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      modes current.contact.physicalState
  have rawLe := wholeRestartRawCoefficientCeiling_le current.contact
  rw [wholeRestartRawCoefficientCeiling_eq] at rawLe
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    at rawLe
  change
    wholeVorticityEuclideanMass current.contact.physicalState + 1 ≤
      (wholeRestartCoefficientLevel current.contact : Real) at rawLe
  have levelLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_currentLevel_le_anchorLevel
    (runCellStanding stackedShortCurrent stage)
  have levelLeReal :
      (wholeRestartCoefficientLevel current.contact : Real) ≤
        (runCellStanding stackedShortCurrent stage).anchorLevel := by
    exact_mod_cast levelLe
  have finiteMassLeAnchor :
      finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState ≤
        ((source.stateAfter stage).1.standing.anchorLevel : Real) := by
    have runtimeEq :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    have anchorEq := congrArg
      (fun runtime : GeneratedWholeRestartRuntimeCurrent
          butterflyGainViscosity => runtime.standing.anchorLevel)
      runtimeEq
    have anchorEq' :
        (source.stateAfter stage).1.standing.anchorLevel =
          (runCellStanding stackedShortCurrent stage).anchorLevel := by
      calc
        (source.stateAfter stage).1.standing.anchorLevel =
            (runRuntime stackedShortCurrent stage).standing.anchorLevel := by
          simpa only [source, stackedStandingActionMediumSource] using anchorEq
        _ = (runCellStanding stackedShortCurrent stage).anchorLevel := rfl
    dsimp only [current] at finiteMassLeWhole rawLe levelLeReal ⊢
    rw [anchorEq']
    linarith
  have actionSquareNonneg : 0 ≤ actionSquare := by
    dsimp only [actionSquare]
    exact Finset.sum_nonneg fun wave _waveMem =>
      complexCoordinateVectorNormSq_nonneg _
  dsimp only [current, modes, actionSquare] at cauchy finiteMassLeAnchor ⊢
  dsimp only [threshold] at thresholdSquareLe
  have massAction := mul_le_mul_of_nonneg_right finiteMassLeAnchor
    actionSquareNonneg
  have scaledMass := mul_le_mul_of_nonneg_left massAction
    (by norm_num : (0 : Real) ≤ 4)
  nlinarith

/-- The same lower row is already in the exact shape of the regeneration
term used by the local advance: it is scaled by this occurrence's generated
clock and transported into the compiler-owned successor inventory. -/
theorem ButterflyMovingScalePowerReserveAt.clock_mul_actionSquare_lower
    {stage : Nat}
    (reserve : ButterflyMovingScalePowerReserveAt stage) :
    (standingActionMovingScalePowerCoefficient *
        (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real)) ^ 2 *
        (run stackedShortCurrent stage).nextContact.time.1 ≤
      4 * ((source.stateAfter stage).1.standing.anchorLevel : Real) *
        (∑ wave ∈ standingActionRunInventory (stage + 1),
          (run stackedShortCurrent stage).nextContact.time.1 *
            complexCoordinateVectorNormSq
              (wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                (run stackedShortCurrent stage).contact.physicalState wave)) := by
  have lower := reserve.actionSquare_lower
  have clockNonneg :=
    (run stackedShortCurrent stage).nextContact.time_pos.le
  have scaledLower := mul_le_mul_of_nonneg_right lower clockNonneg
  have sumLe :
      (∑ wave ∈ standingActionRunInventory stage,
          complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              (run stackedShortCurrent stage).contact.physicalState wave)) ≤
        ∑ wave ∈ standingActionRunInventory (stage + 1),
          complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              (run stackedShortCurrent stage).contact.physicalState wave) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (standingActionRunInventory_nested stage)
      (fun wave _waveMem _waveNotMem =>
        complexCoordinateVectorNormSq_nonneg _)
  have clockedSum := mul_le_mul_of_nonneg_left sumLe clockNonneg
  have anchorNonneg : 0 ≤
      ((source.stateAfter stage).1.standing.anchorLevel : Real) := by positivity
  have scaledSum := mul_le_mul_of_nonneg_left clockedSum
    (mul_nonneg (by norm_num : (0 : Real) ≤ 4) anchorNonneg)
  simp_rw [← Finset.mul_sum] at scaledSum ⊢
  nlinarith

/-- Computable current-side credit extracted from the reserve's power/action
pairing.  It is finite because the live standing anchor is a positive natural
readout of the same root occurrence. -/
def butterflyMovingScaleActionCredit (stage : Nat) : Real :=
  ((standingActionMovingScalePowerCoefficient *
      (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
        (5 / 4 : Real)) ^ 2 *
      (run stackedShortCurrent stage).nextContact.time.1) /
    (2 * ((source.stateAfter stage).1.standing.anchorLevel : Real))

theorem butterflyMovingScaleActionCredit_nonneg (stage : Nat) :
    0 ≤ butterflyMovingScaleActionCredit stage := by
  unfold butterflyMovingScaleActionCredit
  exact div_nonneg
    (mul_nonneg (sq_nonneg _)
      (run stackedShortCurrent stage).nextContact.time_pos.le)
    (mul_nonneg (by norm_num) (by positivity))

/-- The credit is not a new scalar premise: the prepaid reserve itself
generates it below the complete action-energy term already present in the
successor ledger. -/
theorem ButterflyMovingScalePowerReserveAt.actionCredit_le_generatedAction
    {stage : Nat}
    (reserve : ButterflyMovingScalePowerReserveAt stage) :
    butterflyMovingScaleActionCredit stage ≤
      2 * ∑ wave ∈ standingActionRunInventory (stage + 1),
        (run stackedShortCurrent stage).nextContact.time.1 *
          complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              (run stackedShortCurrent stage).contact.physicalState wave) := by
  have lower := reserve.clock_mul_actionSquare_lower
  have anchorPos : 0 <
      ((source.stateAfter stage).1.standing.anchorLevel : Real) := by
    exact_mod_cast standingActionAnchorLevel_pos stage
  have denominatorPos : 0 <
      2 * ((source.stateAfter stage).1.standing.anchorLevel : Real) :=
    mul_pos (by norm_num) anchorPos
  unfold butterflyMovingScaleActionCredit
  apply (div_le_iff₀ denominatorPos).2
  calc
    (standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real)) ^ 2 *
        (run stackedShortCurrent stage).nextContact.time.1 ≤
      4 * ((source.stateAfter stage).1.standing.anchorLevel : Real) *
        (∑ wave ∈ standingActionRunInventory (stage + 1),
          (run stackedShortCurrent stage).nextContact.time.1 *
            complexCoordinateVectorNormSq
              (wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                (run stackedShortCurrent stage).contact.physicalState wave)) :=
      lower
    _ =
      (2 * ∑ wave ∈ standingActionRunInventory (stage + 1),
          (run stackedShortCurrent stage).nextContact.time.1 *
            complexCoordinateVectorNormSq
              (wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                (run stackedShortCurrent stage).contact.physicalState wave)) *
        (2 * ((source.stateAfter stage).1.standing.anchorLevel : Real)) := by
      ring

/-- The concrete sixteen-row source occurrence carries its first prepaid
reserve without a caller-supplied margin.  The exact source power is greater
than three, while the scale threshold and all sixteen row corrections use
strictly less than `2 + 32/1000`. -/
theorem butterflyMovingScalePowerReserveAt_zero :
    ButterflyMovingScalePowerReserveAt 0 := by
  dsimp only [ButterflyMovingScalePowerReserveAt, run_zero,
    standingActionRunInventory]
  intro time
  have modesNonempty : butterflyFirstStackModes.Nonempty :=
    ⟨axisWave 4, by simp [butterflyFirstStackModes,
      butterflyFirstYFaceModes]⟩
  have lossSumLt :
      (∑ wave ∈ butterflyFirstStackModes,
          fullReplayKineticSelfWorkLossUpperAt
            stackedShortCurrent time wave) <
        ∑ _wave ∈ butterflyFirstStackModes, (1 / 1000 : Real) := by
    apply Finset.sum_lt_sum_of_nonempty modesNonempty
    intro wave waveMem
    exact stackedShortCurrent_fullReplay_selfWorkLoss_lt_one_thousandth
      time wave waveMem
  have cardEq : butterflyFirstStackModes.card = 16 := by decide
  simp only [Finset.sum_const, nsmul_eq_mul, cardEq] at lossSumLt
  norm_num at lossSumLt
  have threshold := standingActionInitial_scalePowerThreshold_lt_two
  have sourcePower :=
    stackedShortCurrent_nextReceipt_wholePower_zero_gt_three
  have correctionLt :
      2 * (∑ wave ∈ butterflyFirstStackModes,
        fullReplayKineticSelfWorkLossUpperAt
          stackedShortCurrent time wave) < 1 := by
    nlinarith [lossSumLt]
  have totalLt :
      standingActionMovingScalePowerCoefficient *
            (((source.stateAfter 0).1.standing.anchorLevel : Real) + 1) ^
              (5 / 4 : Real) +
          2 * (∑ wave ∈ butterflyFirstStackModes,
            fullReplayKineticSelfWorkLossUpperAt
              stackedShortCurrent time wave) < 3 := by
    nlinarith [threshold, correctionLt]
  exact (totalLt.trans sourcePower).le

/-- The fresh-power side of the vertical law is literally the complete
action-material decomposition installed on the successor root occurrence.
No y-cell term is separated from its complement or whole-action residual. -/
theorem expandedNewRowsPower_eq_actionMaterial (stage : Nat) :
    let state := source.stateAfter (stage + 1)
    let current := run stackedShortCurrent (stage + 1)
    let newRows := standingActionRunInventory (stage + 1) \
      standingActionRunInventory stage
    actualProjectedWholeNetEnstrophyPower current.nextReceipt newRows 0 =
      2 * ∑ wave ∈ newRows,
        complexCoordinateRealInner
          (state.1.physical.contact.physicalState wave)
          (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              state.2.dyadicYCellState wave +
            state.2.yCellComplementCrossAction wave +
            state.2.actionResidual wave) := by
  dsimp only
  let state := source.stateAfter (stage + 1)
  let current := run stackedShortCurrent (stage + 1)
  let newRows := standingActionRunInventory (stage + 1) \
    standingActionRunInventory stage
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have currentEq : state.1.physical = current := by
    dsimp only [state, current]
    exact congrArg (fun runtime => runtime.physical)
      (standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction (stage + 1))
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  rw [actualProjectedWholeNetEnstrophyPower_eq_static, stateAtZero,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  change
    2 * ∑ wave ∈ newRows,
        complexCoordinateRealInner (current.contact.physicalState wave)
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff current.contact.physicalState wave) = _
  apply congrArg (fun value : Real => 2 * value)
  apply Finset.sum_congr rfl
  intro wave _waveMem
  have actionEq := material.wholeAction_commutes wave
  rw [material.actionInstruction_eq] at actionEq
  unfold classicalWholeNSVorticityTangent
    wholeLatticeVorticityFourierTangentAt at actionEq
  dsimp only [state, current] at currentEq actionEq ⊢
  rw [← currentEq]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [actionEq]

/-- Direct splice for the sole vertical source law.  The expanded action
rows pay both the next anchor increment and the complete same-receipt
rowwise transport loss.  The final clock law will generate this inequality
internally; it is not a public counterexample premise. -/
private theorem butterflyMovingScalePowerAt_succ_of_expandedAction
    (stage : Nat)
    (invariant : ButterflyMovingScalePowerAt stage)
    (expandedAction :
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          2 * ∑ wave ∈ modes,
            fullReplayKineticSelfWorkLossUpperAt current time wave ≤
          actualProjectedWholeNetEnstrophyPower current.nextReceipt
            newRows 0) :
    ButterflyMovingScalePowerAt (stage + 1) := by
  intro actual actualMem
  let current := run stackedShortCurrent (stage + 1)
  let modes := standingActionRunInventory (stage + 1)
  let newRows := modes \ standingActionRunInventory stage
  let time : Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨actual, actualMem.1,
      actualMem.2.trans
        (run stackedShortCurrent (stage + 1)).nextContact.time.2.2⟩
  have retained := invariant.endpoint_power_margin
  have split := actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    current.nextReceipt
    (standingActionRunInventory stage) modes
    (standingActionRunInventory_nested stage)
  have drift := abs_fullReplay_netPower_sub_zero_le_sum_selfWorkLoss
    current modes (standingActionRunInventory_zeroNotMem (stage + 1)) time
  have sourcePayment := expandedAction time
  have lowerDrift := neg_abs_le
    (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0)
  have timePowerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 2)).contact.prefixReceipt
          modes actual =
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 := by
    change
      actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes actual =
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    have stateEq :
        (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 =
          (actualWholeProjectedTransversePath
            current.nextReceipt time.1).1 := by
      change current.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) current.nextContact.time.1
            current.nextContact.time_pos.le actual) =
        current.nextReceipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
            current.nextReceipt.requestedTimePos.le time.1)
      rw [Set.projIcc_of_mem current.nextContact.time_pos.le actualMem]
      rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
      rfl
    rw [stateEq]
  rw [timePowerEq]
  dsimp only [current, modes, newRows]
    at sourcePayment drift lowerDrift retained ⊢
  dsimp only [current, modes] at split
  linarith

private theorem complexCoordinateRealInner_add_left_clock
    (left₁ left₂ right : ComplexCoordinateVector) :
    complexCoordinateRealInner (left₁ + left₂) right =
      complexCoordinateRealInner left₁ right +
        complexCoordinateRealInner left₂ right := by
  unfold complexCoordinateRealInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
  ring

private theorem complexCoordinateRealInner_real_smul_left_clock
    (left right : ComplexCoordinateVector) (scalar : Real) :
    complexCoordinateRealInner (scalar • left) right =
      scalar * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_im]
  ring

/-- Current-side loss retained after the positive Euler-generated tangent
square is separated from one endpoint self-work row. -/
def fullReplayGeneratedSelfWorkLossUpperAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector) : Real :=
  let source := current.contact.physicalState wave
  let tangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let drift := fullReplayKineticTangentSourceUpper current wave
  3 * ‖source‖ * drift +
    3 * time.1 * ‖tangent‖ * drift +
    3 * (time.1 * drift) * (‖tangent‖ + drift)

theorem fullReplayGeneratedSelfWorkLossUpperAt_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector) :
    0 ≤ fullReplayGeneratedSelfWorkLossUpperAt current time wave := by
  unfold fullReplayGeneratedSelfWorkLossUpperAt
  have driftNonneg := fullReplayKineticTangentSourceUpper_nonneg current wave
  exact add_nonneg
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _)) driftNonneg)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) time.2.1) (norm_nonneg _))
        driftNonneg))
    (mul_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg time.2.1 driftNonneg))
      (add_nonneg (norm_nonneg _) driftNonneg))

/-- Exact audit of the two transport corrections.  The earlier absolute
drift reserve overcharges one row by precisely three copies of the positive
Euler-generated action square; the one-sided endpoint ledger does not. -/
theorem fullReplayKineticSelfWorkLossUpperAt_eq_generated_add_tangentNormSq
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector) :
    fullReplayKineticSelfWorkLossUpperAt current time wave =
      fullReplayGeneratedSelfWorkLossUpperAt current time wave +
        3 * time.1 *
          ‖wholeLatticeVorticityFourierTangentAt nu.coeff
            current.contact.physicalState wave‖ ^ 2 := by
  unfold fullReplayKineticSelfWorkLossUpperAt
    fullReplayGeneratedSelfWorkLossUpperAt
  ring

theorem fullReplayGeneratedSelfWorkLossUpperAt_le_kineticLoss
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector) :
    fullReplayGeneratedSelfWorkLossUpperAt current time wave ≤
      fullReplayKineticSelfWorkLossUpperAt current time wave := by
  rw [fullReplayKineticSelfWorkLossUpperAt_eq_generated_add_tangentNormSq]
  exact le_add_of_nonneg_right
    (mul_nonneg
      (mul_nonneg (by norm_num) time.2.1)
      (sq_nonneg _))

/-- The endpoint work retains the positive tangent-square incidence emitted
by the source row.  Only current-receipt Euler and tangent drift are debited. -/
theorem fullReplay_sourceWork_add_generatedTangentSquare_sub_loss_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    kineticSelfTangentWorkAt nu current.contact.physicalState wave +
          time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave) -
        fullReplayGeneratedSelfWorkLossUpperAt current time wave ≤
      kineticSelfTangentWorkAt nu
        (current.nextReceipt.wholePath time) wave := by
  let source := current.contact.physicalState wave
  let target := current.nextReceipt.wholePath time wave
  let sourceTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let targetTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    (current.nextReceipt.wholePath time) wave
  let drift := targetTangent - sourceTangent
  let driftUpper := fullReplayKineticTangentSourceUpper current wave
  let eulerError := target - (source + time.1 • sourceTangent)
  have driftUpperNonneg : 0 ≤ driftUpper := by
    exact fullReplayKineticTangentSourceUpper_nonneg current wave
  have driftLe : ‖drift‖ ≤ driftUpper := by
    let zeroTime : Set.Icc (0 : Real)
        (wholeRestartDuration current.contact) :=
      ⟨0, le_rfl, (wholeRestartDuration_pos current.contact).le⟩
    have generated :=
      receipt_wholeLatticeVorticityTangent_sub_norm_le_kineticDrift
        current.nextReceipt wave waveNe zeroTime time time.2.1
    have velocityDriftLe :=
      receiptKineticVelocityDriftUpper_le_fullReplay current time
    have pathVelocityLe :=
      fullReplay_wholeBiotSavartVelocity_norm_le_radius current time
    have initialVelocityLe :=
      fullReplay_initialWholeBiotSavartVelocity_norm_le_radius current
    have sourceEq : current.nextReceipt.wholePath zeroTime =
        current.contact.physicalState := current.nextReceipt.wholePath_initial
    rw [sourceEq] at generated
    have velocitySumLe :
        ‖wholeBiotSavartVelocityState
            (current.nextReceipt.wholePath time)‖ +
          ‖wholeBiotSavartVelocityState
            current.contact.physicalState‖ ≤
        2 * fullReplayKineticVelocityRadius current := by
      linarith
    have angularNonneg :
        0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) := by
      positivity
    have dampingNonneg :
        0 ≤ nu.coeff * integerWaveViscousMultiplier wave := by
      exact mul_nonneg nu.coeff_pos.le (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
    have coefficientLe :
        (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
              (‖wholeBiotSavartVelocityState
                  (current.nextReceipt.wholePath time)‖ +
                ‖wholeBiotSavartVelocityState
                  current.contact.physicalState‖) +
            nu.coeff * integerWaveViscousMultiplier wave ≤
          (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
              (2 * fullReplayKineticVelocityRadius current) +
            nu.coeff * integerWaveViscousMultiplier wave := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left velocitySumLe angularNonneg) le_rfl
    have productLe := mul_le_mul coefficientLe velocityDriftLe
      (receiptKineticVelocityDriftUpper_nonneg
        current.nextReceipt zeroTime time)
      (add_nonneg
        (mul_nonneg angularNonneg
          (mul_nonneg (by norm_num)
            (fullReplayKineticVelocityRadius_nonneg current)))
        dampingNonneg)
    have bounded := generated.trans
      (mul_le_mul_of_nonneg_left productLe angularNonneg)
    have boundedSource := bounded.trans
      (fullReplayKineticTangentDriftUpper_le_sourceUpper current wave)
    simpa only [drift, targetTangent, sourceTangent, driftUpper,
      fullReplayKineticTangentSourceUpper] using boundedSource
  have errorLe : ‖eulerError‖ ≤ time.1 * driftUpper := by
    have generated := fullReplay_row_sub_euler_norm_le_kineticSource
      current wave waveNe time
    unfold fullReplayEulerRow at generated
    simpa only [eulerError, target, source, sourceTangent,
      sub_eq_add_neg, add_assoc] using generated
  have targetTangentLe : ‖targetTangent‖ ≤
      ‖sourceTangent‖ + driftUpper := by
    calc
      ‖targetTangent‖ = ‖drift + sourceTangent‖ := by
        congr 1
        dsimp only [drift]
        module
      _ ≤ ‖drift‖ + ‖sourceTangent‖ := norm_add_le _ _
      _ ≤ driftUpper + ‖sourceTangent‖ := by linarith
      _ = _ := add_comm _ _
  have sourceDriftLower :
      -(3 * ‖source‖ * driftUpper) ≤
        complexCoordinateRealInner source drift := by
    have absolute := abs_complexCoordinateRealInner_le_three_mul_norm
      source drift
    have scaled :
        |complexCoordinateRealInner source drift| ≤
          3 * ‖source‖ * driftUpper :=
      absolute.trans
        (mul_le_mul_of_nonneg_left driftLe
          (mul_nonneg (by norm_num) (norm_nonneg source)))
    linarith [neg_abs_le (complexCoordinateRealInner source drift)]
  have tangentDriftLower :
      -(3 * time.1 * ‖sourceTangent‖ * driftUpper) ≤
        time.1 * complexCoordinateRealInner sourceTangent drift := by
    have absolute := abs_complexCoordinateRealInner_le_three_mul_norm
      sourceTangent drift
    have scaled :
        time.1 * |complexCoordinateRealInner sourceTangent drift| ≤
          3 * time.1 * ‖sourceTangent‖ * driftUpper := by
      have sourceDriftLe :
          |complexCoordinateRealInner sourceTangent drift| ≤
            3 * ‖sourceTangent‖ * driftUpper :=
        absolute.trans
          (mul_le_mul_of_nonneg_left driftLe
            (mul_nonneg (by norm_num) (norm_nonneg sourceTangent)))
      nlinarith [time.2.1]
    have negative := neg_abs_le
      (complexCoordinateRealInner sourceTangent drift)
    nlinarith [time.2.1]
  have errorTargetLower :
      -(3 * (time.1 * driftUpper) *
          (‖sourceTangent‖ + driftUpper)) ≤
        complexCoordinateRealInner eulerError targetTangent := by
    have absolute := abs_complexCoordinateRealInner_le_three_mul_norm
      eulerError targetTangent
    have first := mul_le_mul errorLe targetTangentLe
      (norm_nonneg targetTangent)
      (mul_nonneg time.2.1 driftUpperNonneg)
    have scaled := mul_le_mul_of_nonneg_left first
      (by norm_num : (0 : Real) ≤ 3)
    have total :
        |complexCoordinateRealInner eulerError targetTangent| ≤
          3 * (time.1 * driftUpper) *
            (‖sourceTangent‖ + driftUpper) :=
      absolute.trans (by simpa only [mul_assoc] using scaled)
    linarith [neg_abs_le
      (complexCoordinateRealInner eulerError targetTangent)]
  have targetEq : target =
      source + time.1 • sourceTangent + eulerError := by
    dsimp only [eulerError]
    module
  have tangentEq : targetTangent = sourceTangent + drift := by
    dsimp only [drift]
    module
  have workEq :
      complexCoordinateRealInner target targetTangent =
        complexCoordinateRealInner source sourceTangent +
          time.1 * complexCoordinateVectorNormSq sourceTangent +
          complexCoordinateRealInner source drift +
          time.1 * complexCoordinateRealInner sourceTangent drift +
          complexCoordinateRealInner eulerError targetTangent := by
    rw [targetEq, tangentEq,
      complexCoordinateRealInner_add_left_clock,
      complexCoordinateRealInner_add_left_clock,
      complexCoordinateRealInner_add_right source sourceTangent drift,
      complexCoordinateRealInner_real_smul_left_clock,
      complexCoordinateRealInner_add_right sourceTangent sourceTangent drift,
      complexCoordinateRealInner_self]
    ring
  unfold kineticSelfTangentWorkAt
  dsimp only [target, source, sourceTangent, targetTangent] at workEq ⊢
  unfold fullReplayGeneratedSelfWorkLossUpperAt
  dsimp only [source, sourceTangent, driftUpper] at sourceDriftLower
  dsimp only [source, sourceTangent, driftUpper] at tangentDriftLower
  dsimp only [source, sourceTangent, driftUpper] at errorTargetLower ⊢
  rw [workEq]
  linarith

/-- Aggregate one-sided regeneration on an arbitrary finite inventory of the
same generated receipt.  Unlike the absolute drift bound, the positive
`time * ‖F‖²` row remains available to finance the next occurrence. -/
theorem fullReplay_netPower_zero_add_generatedAction_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
        2 * ∑ wave ∈ modes,
          (time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave) -
            fullReplayGeneratedSelfWorkLossUpperAt current time wave) ≤
      actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1 := by
  have stateAtTime :
      (actualWholeProjectedTransversePath current.nextReceipt time.1).1 =
        current.nextReceipt.wholePath time := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le time.1) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  rw [actualProjectedWholeNetEnstrophyPower_eq_static,
    actualProjectedWholeNetEnstrophyPower_eq_static,
    stateAtZero, stateAtTime,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ wave ∈ modes,
          kineticSelfTangentWorkAt nu
            current.contact.physicalState wave) +
        ∑ wave ∈ modes,
          (time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave) -
            fullReplayGeneratedSelfWorkLossUpperAt current time wave) =
      ∑ wave ∈ modes,
        (kineticSelfTangentWorkAt nu
              current.contact.physicalState wave +
          time.1 * complexCoordinateVectorNormSq
              (wholeLatticeVorticityFourierTangentAt nu.coeff
                current.contact.physicalState wave) -
          fullReplayGeneratedSelfWorkLossUpperAt current time wave) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    _ ≤ ∑ wave ∈ modes,
        kineticSelfTangentWorkAt nu
          (current.nextReceipt.wholePath time) wave := by
      apply Finset.sum_le_sum
      intro wave waveMem
      have waveNe : wave ≠ 0 := fun waveZero =>
        zeroNotMem (waveZero ▸ waveMem)
      exact fullReplay_sourceWork_add_generatedTangentSquare_sub_loss_le
        current time wave waveNe

/-- Exact aggregate action-write debit of one finite inventory.  It is the
positive part of the actual shortfall after retaining the complete generated
action square; no rowwise modulus or foreign estimate enters its definition. -/
def fullReplayGeneratedPowerDefectAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) : Real :=
  max 0
    (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
      2 * ∑ wave ∈ modes,
        time.1 * complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt nu.coeff
            current.contact.physicalState wave) -
      actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1)

theorem fullReplayGeneratedPowerDefectAt_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    0 ≤ fullReplayGeneratedPowerDefectAt current modes time := by
  unfold fullReplayGeneratedPowerDefectAt
  exact le_max_left _ _

/-- Complementary exact write surplus retained by the positive-part
normalizer.  `defect` and `surplus` are the two source-generated projections
of one signed action shortfall. -/
def fullReplayGeneratedPowerSurplusAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) : Real :=
  fullReplayGeneratedPowerDefectAt current modes time -
    (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
      2 * ∑ wave ∈ modes,
        time.1 * complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt nu.coeff
            current.contact.physicalState wave) -
      actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1)

theorem fullReplayGeneratedPowerSurplusAt_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    0 ≤ fullReplayGeneratedPowerSurplusAt current modes time := by
  unfold fullReplayGeneratedPowerSurplusAt
    fullReplayGeneratedPowerDefectAt
  have shortfallLe :
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
            2 * ∑ wave ∈ modes,
              time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave) -
          actualProjectedWholeNetEnstrophyPower
              current.nextReceipt modes time.1 ≤
        max 0
          (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
            2 * ∑ wave ∈ modes,
              time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave) -
            actualProjectedWholeNetEnstrophyPower
              current.nextReceipt modes time.1) :=
    le_max_right _ _
  linarith

/-- Exact aggregate action write-back; no inequality remains after retaining
both normal-form projections. -/
theorem fullReplay_netPower_eq_zero_add_action_sub_defect_add_surplus
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1 =
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
        2 * ∑ wave ∈ modes,
          time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave) -
        fullReplayGeneratedPowerDefectAt current modes time +
        fullReplayGeneratedPowerSurplusAt current modes time := by
  unfold fullReplayGeneratedPowerSurplusAt
  ring

/-- Exact one-sided write-back carried by the aggregate debit. -/
theorem fullReplay_netPower_zero_add_action_sub_defect_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
        2 * ∑ wave ∈ modes,
          time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave) -
        fullReplayGeneratedPowerDefectAt current modes time ≤
      actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1 := by
  unfold fullReplayGeneratedPowerDefectAt
  have shortfallLe :
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
            2 * ∑ wave ∈ modes,
              time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave) -
          actualProjectedWholeNetEnstrophyPower
              current.nextReceipt modes time.1 ≤
        max 0
          (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
            2 * ∑ wave ∈ modes,
              time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave) -
            actualProjectedWholeNetEnstrophyPower
              current.nextReceipt modes time.1) :=
    le_max_right _ _
  linarith

/-- The exact aggregate debit is bounded by the earlier one-sided row
ledger.  Hence every generated-loss reserve is a source proof of the exact
reserve, while the converse is intentionally not required. -/
theorem fullReplayGeneratedPowerDefectAt_le_generatedLoss
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    fullReplayGeneratedPowerDefectAt current modes time ≤
      2 * ∑ wave ∈ modes,
        fullReplayGeneratedSelfWorkLossUpperAt current time wave := by
  have generated := fullReplay_netPower_zero_add_generatedAction_le
    current modes zeroNotMem time
  rw [Finset.sum_sub_distrib] at generated
  have lossNonneg : 0 ≤
      2 * ∑ wave ∈ modes,
        fullReplayGeneratedSelfWorkLossUpperAt current time wave := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun wave _waveMem =>
      fullReplayGeneratedSelfWorkLossUpperAt_nonneg current time wave
  unfold fullReplayGeneratedPowerDefectAt
  apply max_le
  · exact lossNonneg
  · linarith

def selectedFullReplayTime
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) :
    Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
  ⟨time.1, time.2.1,
    time.2.2.trans current.nextContact.time.2.2⟩

/-- Exact aggregate debit restricted to the already selected actual contact
interval.  This is the largest interval consumed by the clock law. -/
def fullReplaySelectedGeneratedPowerDefectAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) : Real :=
  fullReplayGeneratedPowerDefectAt current modes
    (selectedFullReplayTime current time)

def fullReplaySelectedGeneratedPowerSurplusAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) : Real :=
  fullReplayGeneratedPowerSurplusAt current modes
    (selectedFullReplayTime current time)

theorem fullReplaySelectedGeneratedPowerDefectAt_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) :
    0 ≤ fullReplaySelectedGeneratedPowerDefectAt current modes time :=
  fullReplayGeneratedPowerDefectAt_nonneg current modes
    (selectedFullReplayTime current time)

theorem fullReplaySelectedGeneratedPowerSurplusAt_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) :
    0 ≤ fullReplaySelectedGeneratedPowerSurplusAt current modes time :=
  fullReplayGeneratedPowerSurplusAt_nonneg current modes
    (selectedFullReplayTime current time)

theorem fullReplay_selected_netPower_eq_zero_add_action_sub_defect_add_surplus
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) :
    actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1 =
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
        2 * ∑ wave ∈ modes,
          time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave) -
        fullReplaySelectedGeneratedPowerDefectAt current modes time +
        fullReplaySelectedGeneratedPowerSurplusAt current modes time := by
  simpa only [fullReplaySelectedGeneratedPowerDefectAt,
    fullReplaySelectedGeneratedPowerSurplusAt, selectedFullReplayTime] using
      fullReplay_netPower_eq_zero_add_action_sub_defect_add_surplus
        current modes (selectedFullReplayTime current time)

theorem fullReplay_selected_netPower_zero_add_action_sub_defect_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Set.Icc (0 : Real) current.nextContact.time.1) :
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 +
        2 * ∑ wave ∈ modes,
          time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave) -
        fullReplaySelectedGeneratedPowerDefectAt current modes time ≤
      actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes time.1 := by
  simpa only [fullReplaySelectedGeneratedPowerDefectAt,
    selectedFullReplayTime] using
      fullReplay_netPower_zero_add_action_sub_defect_le current modes
        (selectedFullReplayTime current time)

/-- Faithful prepaid carrier for the one-sided endpoint ledger.  In contrast
to `ButterflyMovingScalePowerReserveAt`, it does not debit the positive
generated action square a second time. -/
def ButterflyMovingScaleGeneratedReserveAt (stage : Nat) : Prop :=
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        2 * ∑ wave ∈ modes,
          fullReplayGeneratedSelfWorkLossUpperAt current time wave ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0

/-- Minimal exact prepaid carrier on the complete current inventory.  Its
debit is computed from the actual receipt and action write-back itself. -/
def ButterflyMovingScaleExactReserveAt (stage : Nat) : Prop :=
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        fullReplayGeneratedPowerDefectAt current modes time ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0

/-- Minimal reserve on the exact source-selected contact interval.  No
unselected portion of the canonical replay is prepaid. -/
def ButterflyMovingScaleSelectedExactReserveAt (stage : Nat) : Prop :=
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  ∀ time : Set.Icc (0 : Real) current.nextContact.time.1,
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        fullReplaySelectedGeneratedPowerDefectAt current modes time ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0

def butterflyMovingScaleSelectedExactHeadroomAt
    (stage : Nat)
    (time : Set.Icc (0 : Real)
      (run stackedShortCurrent stage).nextContact.time.1) : Real :=
  actualProjectedWholeNetEnstrophyPower
      (run stackedShortCurrent stage).nextReceipt
      (standingActionRunInventory stage) 0 -
    standingActionMovingScalePowerCoefficient *
      (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
        (5 / 4 : Real) -
    fullReplaySelectedGeneratedPowerDefectAt
      (run stackedShortCurrent stage)
      (standingActionRunInventory stage) time

theorem ButterflyMovingScaleSelectedExactReserveAt.headroom_nonneg
    {stage : Nat}
    (reserve : ButterflyMovingScaleSelectedExactReserveAt stage)
    (time : Set.Icc (0 : Real)
      (run stackedShortCurrent stage).nextContact.time.1) :
    0 ≤ butterflyMovingScaleSelectedExactHeadroomAt stage time := by
  have paid := reserve time
  unfold butterflyMovingScaleSelectedExactHeadroomAt
  linarith

theorem butterflyMovingScaleSelectedExactReserveAt_iff_headroom_nonneg
    (stage : Nat) :
    ButterflyMovingScaleSelectedExactReserveAt stage ↔
      ∀ time : Set.Icc (0 : Real)
          (run stackedShortCurrent stage).nextContact.time.1,
        0 ≤ butterflyMovingScaleSelectedExactHeadroomAt stage time := by
  constructor
  · intro reserve time
    exact reserve.headroom_nonneg time
  · intro headroom time
    have nonneg := headroom time
    unfold butterflyMovingScaleSelectedExactHeadroomAt at nonneg
    linarith

theorem ButterflyMovingScalePowerReserveAt.toGenerated
    {stage : Nat}
    (reserve : ButterflyMovingScalePowerReserveAt stage) :
    ButterflyMovingScaleGeneratedReserveAt stage := by
  intro time
  have paid := reserve time
  have lossLe :
      (∑ wave ∈ standingActionRunInventory stage,
          fullReplayGeneratedSelfWorkLossUpperAt
            (run stackedShortCurrent stage) time wave) ≤
        ∑ wave ∈ standingActionRunInventory stage,
          fullReplayKineticSelfWorkLossUpperAt
            (run stackedShortCurrent stage) time wave := by
    apply Finset.sum_le_sum
    intro wave _waveMem
    exact fullReplayGeneratedSelfWorkLossUpperAt_le_kineticLoss
      (run stackedShortCurrent stage) time wave
  linarith

theorem ButterflyMovingScaleGeneratedReserveAt.toExact
    {stage : Nat}
    (reserve : ButterflyMovingScaleGeneratedReserveAt stage) :
    ButterflyMovingScaleExactReserveAt stage := by
  intro time
  have paid := reserve time
  have defectLe := fullReplayGeneratedPowerDefectAt_le_generatedLoss
    (run stackedShortCurrent stage) (standingActionRunInventory stage)
    (standingActionRunInventory_zeroNotMem stage) time
  linarith

theorem ButterflyMovingScaleExactReserveAt.toSelected
    {stage : Nat}
    (reserve : ButterflyMovingScaleExactReserveAt stage) :
    ButterflyMovingScaleSelectedExactReserveAt stage := by
  intro time
  exact reserve (selectedFullReplayTime (run stackedShortCurrent stage) time)

/-- The one-sided reserve projects to the unchanged frozen clock consumer;
the retained positive action square is discarded only at this final readout,
not while generating the successor reserve. -/
theorem ButterflyMovingScaleGeneratedReserveAt.power
    {stage : Nat}
    (reserve : ButterflyMovingScaleGeneratedReserveAt stage) :
    ButterflyMovingScalePowerAt stage := by
  intro actual actualMem
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  let time : Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨actual, actualMem.1,
      actualMem.2.trans current.nextContact.time.2.2⟩
  have generated := fullReplay_netPower_zero_add_generatedAction_le
    current modes (standingActionRunInventory_zeroNotMem stage) time
  have paid := reserve time
  have actionNonneg : 0 ≤
      2 * ∑ wave ∈ modes,
        time.1 * complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            current.contact.physicalState wave) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun wave _waveMem =>
      mul_nonneg time.2.1 (complexCoordinateVectorNormSq_nonneg _)
  have timePowerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          modes actual =
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes time.1 := by
    change
      actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes actual =
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes time.1
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    have stateEq :
        (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 =
          (actualWholeProjectedTransversePath
            current.nextReceipt time.1).1 := by
      change current.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) current.nextContact.time.1
            current.nextContact.time_pos.le actual) =
        current.nextReceipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
            current.nextReceipt.requestedTimePos.le time.1)
      rw [Set.projIcc_of_mem current.nextContact.time_pos.le actualMem]
      rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
      rfl
    rw [stateEq]
  rw [Finset.sum_sub_distrib] at generated
  rw [timePowerEq]
  dsimp only [current, modes] at generated paid actionNonneg ⊢
  linarith

theorem ButterflyMovingScaleExactReserveAt.power
    {stage : Nat}
    (reserve : ButterflyMovingScaleExactReserveAt stage) :
    ButterflyMovingScalePowerAt stage := by
  intro actual actualMem
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  let time : Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨actual, actualMem.1,
      actualMem.2.trans current.nextContact.time.2.2⟩
  have generated := fullReplay_netPower_zero_add_action_sub_defect_le
    current modes time
  have paid := reserve time
  have actionNonneg : 0 ≤
      2 * ∑ wave ∈ modes,
        time.1 * complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            current.contact.physicalState wave) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun wave _waveMem =>
      mul_nonneg time.2.1 (complexCoordinateVectorNormSq_nonneg _)
  have timePowerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          modes actual =
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes time.1 := by
    change
      actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes actual =
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes time.1
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    have stateEq :
        (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 =
          (actualWholeProjectedTransversePath
            current.nextReceipt time.1).1 := by
      change current.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) current.nextContact.time.1
            current.nextContact.time_pos.le actual) =
        current.nextReceipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
            current.nextReceipt.requestedTimePos.le time.1)
      rw [Set.projIcc_of_mem current.nextContact.time_pos.le actualMem]
      rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
      rfl
    rw [stateEq]
  rw [timePowerEq]
  dsimp only [current, modes] at generated paid actionNonneg ⊢
  linarith

theorem nextReceipt_netPower_eq_nextContactPrefix
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real) current.nextContact.time.1) :
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes actual =
      actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes actual := by
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  have replayState :
      (actualWholeProjectedTransversePath current.nextReceipt actual).1 =
        current.nextReceipt.wholePath
          (selectedFullReplayTime current ⟨actual, actualMem⟩) := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le actual) = _
    have actualFullMem : actual ∈
        Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
      (selectedFullReplayTime current ⟨actual, actualMem⟩).2
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      actualFullMem]
    rfl
  have prefixState :
      (actualWholeProjectedTransversePath
        current.nextContact.prefixReceipt actual).1 =
        current.nextReceipt.wholePath
          (selectedFullReplayTime current ⟨actual, actualMem⟩) := by
    change current.nextContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) current.nextContact.time.1
          current.nextContact.time_pos.le actual) = _
    rw [Set.projIcc_of_mem current.nextContact.time_pos.le actualMem]
    rfl
  rw [replayState, prefixState]

theorem nextReceipt_netPower_selected_eq_nextContactPrefix
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes
        current.nextContact.time.1 =
      actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes current.nextContact.time.1 := by
  exact nextReceipt_netPower_eq_nextContactPrefix current modes
    current.nextContact.time.1
    ⟨current.nextContact.time_pos.le, le_rfl⟩

theorem ButterflyMovingScaleSelectedExactReserveAt.power
    {stage : Nat}
    (reserve : ButterflyMovingScaleSelectedExactReserveAt stage) :
    ButterflyMovingScalePowerAt stage := by
  intro actual actualMem
  let current := run stackedShortCurrent stage
  let modes := standingActionRunInventory stage
  let time : Set.Icc (0 : Real) current.nextContact.time.1 :=
    ⟨actual, actualMem⟩
  have generated :=
    fullReplay_selected_netPower_zero_add_action_sub_defect_le
      current modes time
  have paid := reserve time
  have actionNonneg : 0 ≤
      2 * ∑ wave ∈ modes,
        time.1 * complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            current.contact.physicalState wave) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun wave _waveMem =>
      mul_nonneg time.2.1 (complexCoordinateVectorNormSq_nonneg _)
  have seam := nextReceipt_netPower_eq_nextContactPrefix
    current modes actual actualMem
  change
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes actual
  rw [← seam]
  dsimp only [current, modes, time] at generated paid actionNonneg ⊢
  linarith

/-- Exact retained/fresh splice for the next time-zero inventory.  The
current reserve's aggregate debit cancels on retained rows; only the fresh
submaterial's exact debit remains. -/
theorem successorInventoryPower_zero_ge_exactReserveAction
    (stage : Nat)
    (reserve : ButterflyMovingScaleExactReserveAt stage) :
    let previous := run stackedShortCurrent stage
    let current := run stackedShortCurrent (stage + 1)
    let oldModes := standingActionRunInventory stage
    let modes := standingActionRunInventory (stage + 1)
    let newRows := modes \ oldModes
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt
          newRows 0 +
        2 * ∑ wave ∈ modes,
          previous.nextContact.time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              previous.contact.physicalState wave) -
        fullReplayGeneratedPowerDefectAt previous newRows
          previous.nextContact.time ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 := by
  dsimp only
  let previous := run stackedShortCurrent stage
  let current := run stackedShortCurrent (stage + 1)
  let oldModes := standingActionRunInventory stage
  let modes := standingActionRunInventory (stage + 1)
  let newRows := modes \ oldModes
  let time := previous.nextContact.time
  have paid := reserve time
  have oldWrite := fullReplay_netPower_zero_add_action_sub_defect_le
    previous oldModes time
  have newWrite := fullReplay_netPower_zero_add_action_sub_defect_le
    previous newRows time
  have oldSelected := nextReceipt_netPower_selected_eq_nextContactPrefix
    previous oldModes
  have newSelected := nextReceipt_netPower_selected_eq_nextContactPrefix
    previous newRows
  have oldSeam := next_netPower_zero_eq_current_selectedEndpoint
    previous oldModes
  have newSeam := next_netPower_zero_eq_current_selectedEndpoint
    previous newRows
  have split := actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    current.nextReceipt oldModes modes
    (standingActionRunInventory_nested stage)
  have actionSplit := Finset.sum_sdiff
    (f := fun wave => previous.nextContact.time.1 *
      complexCoordinateVectorNormSq
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          previous.contact.physicalState wave))
    (standingActionRunInventory_nested stage)
  dsimp only [previous, current, oldModes, modes, newRows, time]
    at paid oldWrite newWrite oldSelected newSelected oldSeam newSeam split
      actionSplit ⊢
  rw [oldSelected, ← oldSeam] at oldWrite
  rw [newSelected, ← newSeam] at newWrite
  have oldTargetEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).next.nextReceipt
          (standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory stage) 0 := by rfl
  have newTargetEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).next.nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0 := by rfl
  rw [oldTargetEq] at oldWrite
  rw [newTargetEq] at newWrite
  rw [split]
  linarith

/-- Selected-interval version of the retained/fresh exact splice.  Its only
incoming debit is evaluated at the actual selected endpoint. -/
theorem successorInventoryPower_zero_ge_selectedExactReserveAction
    (stage : Nat)
    (reserve : ButterflyMovingScaleSelectedExactReserveAt stage) :
    let previous := run stackedShortCurrent stage
    let current := run stackedShortCurrent (stage + 1)
    let oldModes := standingActionRunInventory stage
    let modes := standingActionRunInventory (stage + 1)
    let newRows := modes \ oldModes
    let selected : Set.Icc (0 : Real) previous.nextContact.time.1 :=
      ⟨previous.nextContact.time.1,
        previous.nextContact.time_pos.le, le_rfl⟩
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt
          newRows 0 +
        2 * ∑ wave ∈ modes,
          previous.nextContact.time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              previous.contact.physicalState wave) -
        fullReplaySelectedGeneratedPowerDefectAt previous newRows selected ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 := by
  dsimp only
  let previous := run stackedShortCurrent stage
  let current := run stackedShortCurrent (stage + 1)
  let oldModes := standingActionRunInventory stage
  let modes := standingActionRunInventory (stage + 1)
  let newRows := modes \ oldModes
  let selected : Set.Icc (0 : Real) previous.nextContact.time.1 :=
    ⟨previous.nextContact.time.1,
      previous.nextContact.time_pos.le, le_rfl⟩
  have paid := reserve selected
  have oldWrite :=
    fullReplay_selected_netPower_zero_add_action_sub_defect_le
      previous oldModes selected
  have newWrite :=
    fullReplay_selected_netPower_zero_add_action_sub_defect_le
      previous newRows selected
  have oldSelected := nextReceipt_netPower_selected_eq_nextContactPrefix
    previous oldModes
  have newSelected := nextReceipt_netPower_selected_eq_nextContactPrefix
    previous newRows
  have oldSeam := next_netPower_zero_eq_current_selectedEndpoint
    previous oldModes
  have newSeam := next_netPower_zero_eq_current_selectedEndpoint
    previous newRows
  have split := actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    current.nextReceipt oldModes modes
    (standingActionRunInventory_nested stage)
  have actionSplit := Finset.sum_sdiff
    (f := fun wave => previous.nextContact.time.1 *
      complexCoordinateVectorNormSq
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          previous.contact.physicalState wave))
    (standingActionRunInventory_nested stage)
  dsimp only [previous, current, oldModes, modes, newRows, selected]
    at paid oldWrite newWrite oldSelected newSelected oldSeam newSeam split
      actionSplit ⊢
  rw [oldSelected, ← oldSeam] at oldWrite
  rw [newSelected, ← newSeam] at newWrite
  have oldTargetEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).next.nextReceipt
          (standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory stage) 0 := by rfl
  have newTargetEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).next.nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0 := by rfl
  rw [oldTargetEq] at oldWrite
  rw [newTargetEq] at newWrite
  rw [split]
  linarith

/-- Exact vertical ledger before any nonnegative projection is discarded.
The successor time-zero power is the current threshold, fresh source/action
write, retained headroom, and both selected write surpluses. -/
theorem successorInventoryPower_zero_eq_selectedExactLedger
    (stage : Nat) :
    let previous := run stackedShortCurrent stage
    let current := run stackedShortCurrent (stage + 1)
    let oldModes := standingActionRunInventory stage
    let modes := standingActionRunInventory (stage + 1)
    let newRows := modes \ oldModes
    let selected : Set.Icc (0 : Real) previous.nextContact.time.1 :=
      ⟨previous.nextContact.time.1,
        previous.nextContact.time_pos.le, le_rfl⟩
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 =
      standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt
          newRows 0 +
        2 * ∑ wave ∈ modes,
          previous.nextContact.time.1 * complexCoordinateVectorNormSq
            (wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              previous.contact.physicalState wave) -
        fullReplaySelectedGeneratedPowerDefectAt previous newRows selected +
        butterflyMovingScaleSelectedExactHeadroomAt stage selected +
        fullReplaySelectedGeneratedPowerSurplusAt previous oldModes selected +
        fullReplaySelectedGeneratedPowerSurplusAt previous newRows selected := by
  dsimp only
  let previous := run stackedShortCurrent stage
  let current := run stackedShortCurrent (stage + 1)
  let oldModes := standingActionRunInventory stage
  let modes := standingActionRunInventory (stage + 1)
  let newRows := modes \ oldModes
  let selected : Set.Icc (0 : Real) previous.nextContact.time.1 :=
    ⟨previous.nextContact.time.1,
      previous.nextContact.time_pos.le, le_rfl⟩
  have oldWrite :=
    fullReplay_selected_netPower_eq_zero_add_action_sub_defect_add_surplus
      previous oldModes selected
  have newWrite :=
    fullReplay_selected_netPower_eq_zero_add_action_sub_defect_add_surplus
      previous newRows selected
  have oldSelected := nextReceipt_netPower_selected_eq_nextContactPrefix
    previous oldModes
  have newSelected := nextReceipt_netPower_selected_eq_nextContactPrefix
    previous newRows
  have oldSeam := next_netPower_zero_eq_current_selectedEndpoint
    previous oldModes
  have newSeam := next_netPower_zero_eq_current_selectedEndpoint
    previous newRows
  have split := actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    current.nextReceipt oldModes modes
    (standingActionRunInventory_nested stage)
  have actionSplit := Finset.sum_sdiff
    (f := fun wave => previous.nextContact.time.1 *
      complexCoordinateVectorNormSq
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          previous.contact.physicalState wave))
    (standingActionRunInventory_nested stage)
  dsimp only [previous, current, oldModes, modes, newRows, selected]
    at oldWrite newWrite oldSelected newSelected oldSeam newSeam split
      actionSplit ⊢
  rw [oldSelected, ← oldSeam] at oldWrite
  rw [newSelected, ← newSeam] at newWrite
  have oldTargetEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).next.nextReceipt
          (standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory stage) 0 := by rfl
  have newTargetEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent stage).next.nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).nextReceipt
          (standingActionRunInventory (stage + 1) \
            standingActionRunInventory stage) 0 := by rfl
  rw [oldTargetEq] at oldWrite
  rw [newTargetEq] at newWrite
  rw [split]
  unfold butterflyMovingScaleSelectedExactHeadroomAt
  linarith

/-- Exact source-generated change of selected reserve headroom across one
compiler edge.  Every term is a projection of the two adjacent actual
materials; no proof or sign is stored in the value. -/
def butterflyMovingScaleSelectedExactHeadroomEdgeAt
    (stage : Nat)
    (time : Set.Icc (0 : Real)
      (run stackedShortCurrent (stage + 1)).nextContact.time.1) : Real :=
  let previous := run stackedShortCurrent stage
  let current := run stackedShortCurrent (stage + 1)
  let oldModes := standingActionRunInventory stage
  let modes := standingActionRunInventory (stage + 1)
  let newRows := modes \ oldModes
  let previousSelected : Set.Icc (0 : Real)
      previous.nextContact.time.1 :=
    ⟨previous.nextContact.time.1,
      previous.nextContact.time_pos.le, le_rfl⟩
  actualProjectedWholeNetEnstrophyPower previous.nextReceipt newRows 0 +
      2 * ∑ wave ∈ modes,
        previous.nextContact.time.1 * complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            previous.contact.physicalState wave) -
      fullReplaySelectedGeneratedPowerDefectAt
        previous newRows previousSelected -
      fullReplaySelectedGeneratedPowerDefectAt current modes time +
      fullReplaySelectedGeneratedPowerSurplusAt
        previous oldModes previousSelected +
      fullReplaySelectedGeneratedPowerSurplusAt
        previous newRows previousSelected -
      (standingActionMovingScalePowerCoefficient *
            (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
              (5 / 4 : Real) -
        standingActionMovingScalePowerCoefficient *
            (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
              (5 / 4 : Real))

/-- The vertical law is now a pure equality between generated headroom
states.  Any later nonnegativity proof consumes this exact edge readout. -/
theorem butterflyMovingScaleSelectedExactHeadroomAt_succ_eq
    (stage : Nat)
    (time : Set.Icc (0 : Real)
      (run stackedShortCurrent (stage + 1)).nextContact.time.1) :
    let previous := run stackedShortCurrent stage
    let previousSelected : Set.Icc (0 : Real)
        previous.nextContact.time.1 :=
      ⟨previous.nextContact.time.1,
        previous.nextContact.time_pos.le, le_rfl⟩
    butterflyMovingScaleSelectedExactHeadroomAt (stage + 1) time =
      butterflyMovingScaleSelectedExactHeadroomAt stage previousSelected +
        butterflyMovingScaleSelectedExactHeadroomEdgeAt stage time := by
  dsimp only
  have ledger := successorInventoryPower_zero_eq_selectedExactLedger stage
  unfold butterflyMovingScaleSelectedExactHeadroomAt at ledger ⊢
  unfold butterflyMovingScaleSelectedExactHeadroomEdgeAt
  dsimp only
  linarith

/-- Complete local-law normal form.  Successor reserve is equivalent to the
current selected headroom covering the exact generated edge debit at every
successor selected time. -/
theorem butterflyMovingScaleSelectedExactReserveAt_succ_iff
    (stage : Nat) :
    let previous := run stackedShortCurrent stage
    let previousSelected : Set.Icc (0 : Real)
        previous.nextContact.time.1 :=
      ⟨previous.nextContact.time.1,
        previous.nextContact.time_pos.le, le_rfl⟩
    ButterflyMovingScaleSelectedExactReserveAt (stage + 1) ↔
      ∀ time : Set.Icc (0 : Real)
          (run stackedShortCurrent (stage + 1)).nextContact.time.1,
        -butterflyMovingScaleSelectedExactHeadroomEdgeAt stage time ≤
          butterflyMovingScaleSelectedExactHeadroomAt stage previousSelected := by
  dsimp only
  rw [butterflyMovingScaleSelectedExactReserveAt_iff_headroom_nonneg]
  constructor
  · intro successorNonneg time
    have nextNonneg := successorNonneg time
    have edgeEq :=
      butterflyMovingScaleSelectedExactHeadroomAt_succ_eq stage time
    linarith
  · intro covered time
    have cover := covered time
    have edgeEq :=
      butterflyMovingScaleSelectedExactHeadroomAt_succ_eq stage time
    linarith

theorem butterflyMovingScaleGeneratedReserveAt_zero :
    ButterflyMovingScaleGeneratedReserveAt 0 :=
  butterflyMovingScalePowerReserveAt_zero.toGenerated

theorem butterflyMovingScaleExactReserveAt_zero :
    ButterflyMovingScaleExactReserveAt 0 :=
  butterflyMovingScaleGeneratedReserveAt_zero.toExact

theorem butterflyMovingScaleSelectedExactReserveAt_zero :
    ButterflyMovingScaleSelectedExactReserveAt 0 :=
  butterflyMovingScaleExactReserveAt_zero.toSelected

/-- The concrete source begins with a strict, uniformly quantified bankroll;
the reserve is not merely perched at zero. -/
theorem butterflyMovingScaleSelectedExactHeadroomAt_zero_gt_nineTenths
    (time : Set.Icc (0 : Real) stackedShortCurrent.nextContact.time.1) :
    (9 / 10 : Real) <
      butterflyMovingScaleSelectedExactHeadroomAt 0 time := by
  let fullTime := selectedFullReplayTime stackedShortCurrent time
  have defectLe := fullReplayGeneratedPowerDefectAt_le_generatedLoss
    stackedShortCurrent butterflyFirstStackModes
      butterflyFirstStackModes_zeroNotMem fullTime
  have generatedLeKinetic :
      (∑ wave ∈ butterflyFirstStackModes,
          fullReplayGeneratedSelfWorkLossUpperAt
            stackedShortCurrent fullTime wave) ≤
        ∑ wave ∈ butterflyFirstStackModes,
          fullReplayKineticSelfWorkLossUpperAt
            stackedShortCurrent fullTime wave := by
    apply Finset.sum_le_sum
    intro wave _waveMem
    exact fullReplayGeneratedSelfWorkLossUpperAt_le_kineticLoss
      stackedShortCurrent fullTime wave
  have modesNonempty : butterflyFirstStackModes.Nonempty :=
    ⟨axisWave 4, by simp [butterflyFirstStackModes,
      butterflyFirstYFaceModes]⟩
  have lossSumLt :
      (∑ wave ∈ butterflyFirstStackModes,
          fullReplayKineticSelfWorkLossUpperAt
            stackedShortCurrent fullTime wave) <
        ∑ _wave ∈ butterflyFirstStackModes, (1 / 1000 : Real) := by
    apply Finset.sum_lt_sum_of_nonempty modesNonempty
    intro wave waveMem
    exact stackedShortCurrent_fullReplay_selfWorkLoss_lt_one_thousandth
      fullTime wave waveMem
  have cardEq : butterflyFirstStackModes.card = 16 := by decide
  simp only [Finset.sum_const, nsmul_eq_mul, cardEq] at lossSumLt
  norm_num at lossSumLt
  have exactDefectLt :
      fullReplaySelectedGeneratedPowerDefectAt
          stackedShortCurrent butterflyFirstStackModes time < 4 / 125 := by
    dsimp only [fullReplaySelectedGeneratedPowerDefectAt, fullTime]
    linarith
  have threshold := standingActionInitial_scalePowerThreshold_lt_two
  have sourcePower :=
    stackedShortCurrent_nextReceipt_wholePower_zero_gt_three
  have combinedLt :
      standingActionMovingScalePowerCoefficient *
            (((source.stateAfter 0).1.standing.anchorLevel : Real) + 1) ^
              (5 / 4 : Real) +
          fullReplaySelectedGeneratedPowerDefectAt
            stackedShortCurrent butterflyFirstStackModes time < 21 / 10 := by
    nlinarith [threshold, exactDefectLt]
  unfold butterflyMovingScaleSelectedExactHeadroomAt
  simp only [run_zero, standingActionRunInventory]
  calc
    (9 / 10 : Real) = 3 - 21 / 10 := by norm_num
    _ < actualProjectedWholeNetEnstrophyPower
          stackedShortCurrent.nextReceipt butterflyFirstStackModes 0 -
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter 0).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) +
          fullReplaySelectedGeneratedPowerDefectAt
            stackedShortCurrent butterflyFirstStackModes time) :=
      sub_lt_sub sourcePower combinedLt
    _ = _ := by
      simp only [sub_eq_add_neg, neg_add_rev]
      ac_rfl

/-! ## Outcome-indexed current-debit clock law -/

/-- The exact current-side physical debit consumed by a retained-standing
clock edge.  It is the signed moving-inventory boundary already generated by
the root material, so retained rows, fresh capture and complementary-tail
transport cannot be split across different occurrences. -/
def ButterflyMovingScaleCurrentDebitAt (stage : Nat) : Prop :=
  standingActionMovingScalePowerCoefficient *
        (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
          (5 / 4 : Real) *
      (run stackedShortCurrent (stage + 1)).contact.time.1 ≤
    runMovingInventoryEdgePayment stackedShortCurrent
      shiftedStandingActionInventory (stage + 1)

theorem ButterflyMovingScalePowerAt.toCurrentDebit
    {stage : Nat}
    (power : ButterflyMovingScalePowerAt stage) :
    ButterflyMovingScaleCurrentDebitAt stage := by
  let current := run stackedShortCurrent (stage + 1)
  have integralLower := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume)
    current.contact.time_pos.le
    (continuous_const.intervalIntegrable 0 current.contact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      current.contact.prefixReceipt
      (standingActionRunInventory stage)).intervalIntegrable
        0 current.contact.time.1)
    power
  have integralDebit := integralLower.trans
    (standingActionProjectedPowerIntegral_le_movingEdgePayment stage)
  unfold ButterflyMovingScaleCurrentDebitAt
  simpa [current, intervalIntegral.integral_const, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using integralDebit

/-- The current moving debit has the exact scale needed by the retained-
standing clock.  The successor is still the root compiler's own successor;
no next receipt or future payment is reconstructed here. -/
noncomputable def
    standingActionMovingClockRootResidualAdvance_of_currentDebit
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (debit : ButterflyMovingScaleCurrentDebitAt stage) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1)) := by
  let anchorBase : Real :=
    ((source.stateAfter stage).1.standing.anchorLevel : Real) + 1
  have anchorBasePos : 0 < anchorBase := by
    dsimp only [anchorBase]
    positivity
  have anchorPowerPos : 0 <
      standingActionMovingScalePowerCoefficient *
        anchorBase ^ (5 / 4 : Real) :=
    mul_pos standingActionMovingScalePowerCoefficient_pos
      (Real.rpow_pos_of_pos anchorBasePos _)
  have sourceClockEq :
      source.clockAt (source.stateAfter stage) =
        (run stackedShortCurrent (stage + 1)).contact.time.1 := by
    have currentEq :
        (source.stateAfter stage).1.physical =
          run stackedShortCurrent stage := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction stage
      exact congrArg (fun current => current.physical) generated
    change
      (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [currentEq, run_succ, next_contact]
  have weightEq :
      standingActionMovingResidualWeight
          (source.stateAfter stage).1.standing.anchorLevel =
        (standingActionMovingScalePowerCoefficient *
          anchorBase ^ (5 / 4 : Real))⁻¹ := by
    unfold standingActionMovingResidualWeight
    dsimp only [anchorBase]
    rw [one_div]
  have payment : source.clockAt (source.stateAfter stage) ≤
      standingActionMovingResidualWeight
          (source.stateAfter stage).1.standing.anchorLevel *
        runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1) := by
    rw [sourceClockEq, weightEq]
    have scaled := mul_le_mul_of_nonneg_left debit
      (inv_nonneg.mpr anchorPowerPos.le)
    rw [← mul_assoc, inv_mul_cancel₀ anchorPowerPos.ne', one_mul] at scaled
    exact scaled
  exact standingActionMovingClockRootResidualAdvance stage residual payment

/-- Current residual debit on the prepaid face.  No extra debit is required:
the kinetic account is transported monotonically across the compiler-owned
successor. -/
noncomputable def
    standingActionMovingKineticClockRootResidualAdvance_of_currentDebit
    (stage : Nat)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (debit : ButterflyMovingScaleCurrentDebitAt stage) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingKineticClockState stage)
      (standingActionMovingKineticClockState (stage + 1)) :=
  standingActionMovingKineticClockAdvance_of_movingAdvance stage
    (standingActionMovingClockRootResidualAdvance_of_currentDebit
      stage residual debit)

/-- The instruction demand is computed by the root's already generated
outcome.  Exact payment is settled by the barrier/reset account; only a
residual or obstruction keeps the current physical moving debit. -/
noncomputable def ButterflyOutcomeCurrentDebitAt (stage : Nat) : Prop :=
  match nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) with
  | .exactPayment _effect _rooted _commutes => True
  | .generatedResidual _effect _residual _expansion _expansionEq _payment =>
      ButterflyMovingScaleCurrentDebitAt stage
  | .obstruction _obstruction _demand =>
      ButterflyMovingScaleCurrentDebitAt stage

theorem butterflyOutcomeCurrentDebitAt_zero :
    ButterflyOutcomeCurrentDebitAt 0 := by
  have debit : ButterflyMovingScaleCurrentDebitAt 0 :=
    ButterflyMovingScalePowerAt.toCurrentDebit
      butterflyMovingScaleSelectedExactReserveAt_zero.power
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter 0) = outcome
  cases outcome with
  | exactPayment =>
      unfold ButterflyOutcomeCurrentDebitAt
      rw [outcomeEq]
      trivial
  | generatedResidual =>
      unfold ButterflyOutcomeCurrentDebitAt
      rw [outcomeEq]
      exact debit
  | obstruction =>
      unfold ButterflyOutcomeCurrentDebitAt
      rw [outcomeEq]
      exact debit

noncomputable def
    standingActionMovingClockRootSettlement_of_outcomeDebit
    (stage : Nat)
    (instruction : ButterflyOutcomeCurrentDebitAt stage) :
    SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact .exactPayment
        (standingActionMovingClockRootExactAdvance stage effect commutes)
  | generatedResidual effect residual expansion expansionEq payment =>
      have debit : ButterflyMovingScaleCurrentDebitAt stage := by
        unfold ButterflyOutcomeCurrentDebitAt at instruction
        rw [outcomeEq] at instruction
        exact instruction
      have canonicalResidual : GeneratedParallelResidualAt
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage))
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial := by
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at residual
        rw [effect.effect_eq] at residual
        exact residual
      exact .generatedResidual
        (standingActionMovingClockRootResidualAdvance_of_currentDebit
          stage canonicalResidual debit)
  | obstruction obstruction demand =>
      have debit : ButterflyMovingScaleCurrentDebitAt stage := by
        unfold ButterflyOutcomeCurrentDebitAt at instruction
        rw [outcomeEq] at instruction
        exact instruction
      have canonicalResidual : GeneratedParallelResidualAt
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage))
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial := by
        have residual := obstruction.residual
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at residual
        rw [obstruction.effect.effect_eq] at residual
        exact residual
      exact .obstructionAlternative
        (standingActionMovingClockRootResidualAdvance_of_currentDebit
          stage canonicalResidual debit)

/-- Lift an already outcome-indexed moving settlement to the causally
prepaid moving/kinetic face without reclassifying the root outcome. -/
def standingActionMovingKineticClockSettlement_of_movingSettlement
    (stage : Nat)
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (settlement : SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1)) outcome) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMovingKineticClockState stage)
      (standingActionMovingKineticClockState (stage + 1)) outcome := by
  cases settlement with
  | exactPayment advance =>
      exact .exactPayment
        (standingActionMovingKineticClockAdvance_of_movingAdvance
          stage advance)
  | generatedResidual advance =>
      exact .generatedResidual
        (standingActionMovingKineticClockAdvance_of_movingAdvance
          stage advance)
  | obstructionAlternative advance =>
      exact .obstructionAlternative
        (standingActionMovingKineticClockAdvance_of_movingAdvance
          stage advance)
  | obstructionIncompatible incompatible =>
      exact .obstructionIncompatible incompatible

noncomputable def
    standingActionMovingKineticClockRootSettlement_of_outcomeDebit
    (stage : Nat)
    (instruction : ButterflyOutcomeCurrentDebitAt stage) :
    SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      (standingActionMovingKineticClockState stage)
      (standingActionMovingKineticClockState (stage + 1))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) :=
  standingActionMovingKineticClockSettlement_of_movingSettlement stage
    (standingActionMovingClockRootSettlement_of_outcomeDebit
      stage instruction)

/-- Finite-prefix form of the total root clock fold.  Exact occurrences use
their already-generated barrier/reset settlement; only an actual residual or
obstruction occurrence consumes its current physical moving debit.  The
hypothesis is restricted to the generated finite prefix, so this lemma does
not install a future recurrence table. -/
theorem butterflyMovingClockPrefix_add_potential_le_initial
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    (∑ stage ∈ Finset.range length,
        source.clockAt (source.stateAfter stage)) +
        standingActionMovingClockPotential length ≤
      standingActionMovingClockPotential 0 := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      have prior := inductionHypothesis fun stage stageLt =>
        currentDebit stage (stageLt.trans (Nat.lt_succ_self length))
      have edge :=
        (standingActionMovingClockRootSettlement_of_outcomeDebit
          length (currentDebit length (Nat.lt_succ_self length))).resolved
      have settlement := edge.settlement
      have wasteNonneg := edge.waste_nonneg
      change
        standingActionMovingClockPotential length =
          source.clockAt (source.stateAfter length) +
            standingActionMovingClockPotential (length + 1) + edge.waste
        at settlement
      rw [Finset.sum_range_succ]
      linarith

/-- The same finite-prefix fold with the kinetic account prepaid from the
initial occurrence.  This is the incoming face used at the first actual
residual not covered by the moving debit. -/
theorem butterflyMovingKineticClockPrefix_add_potential_le_initial
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    (∑ stage ∈ Finset.range length,
        source.clockAt (source.stateAfter stage)) +
        standingActionMovingKineticClockPotential length ≤
      standingActionMovingKineticClockPotential 0 := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      have prior := inductionHypothesis fun stage stageLt =>
        currentDebit stage (stageLt.trans (Nat.lt_succ_self length))
      have edge :=
        (standingActionMovingKineticClockRootSettlement_of_outcomeDebit
          length (currentDebit length (Nat.lt_succ_self length))).resolved
      have settlement := edge.settlement
      have wasteNonneg := edge.waste_nonneg
      change
        standingActionMovingKineticClockPotential length =
          source.clockAt (source.stateAfter length) +
            standingActionMovingKineticClockPotential (length + 1) + edge.waste
        at settlement
      rw [Finset.sum_range_succ]
      linarith

/-- In particular, every prefix before the first unpaid actual occurrence
has a source-generated clock bound.  This is the causal bootstrap used to
attack that occurrence; no payment at `length` is assumed. -/
theorem butterflyMovingClockPrefix_le_initial_of_priorOutcomeDebit
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    (∑ stage ∈ Finset.range length,
        source.clockAt (source.stateAfter stage)) ≤
      standingActionMovingClockPotential 0 := by
  have folded := butterflyMovingClockPrefix_add_potential_le_initial
    length currentDebit
  have terminalNonneg := standingActionMovingClockPotential_nonneg length
  linarith

/-- Failure of the current moving debit is witnessed inside the same actual
selected prefix by a strict loss of the source scale-power floor.  This is
the contrapositive of the exact integral-to-moving-edge commuting row, not a
new persistence or future-path assumption. -/
theorem butterflyMovingScaleCurrentDebit_failure_witness
    (stage : Nat)
    (failure : ¬ ButterflyMovingScaleCurrentDebitAt stage) :
    ∃ actual ∈ Set.Icc (0 : Real)
        (run stackedShortCurrent (stage + 1)).contact.time.1,
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          (standingActionRunInventory stage) actual <
        standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) := by
  by_contra noWitness
  push Not at noWitness
  let current := run stackedShortCurrent (stage + 1)
  let threshold := standingActionMovingScalePowerCoefficient *
    (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
      (5 / 4 : Real)
  have integralLower := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume)
    current.contact.time_pos.le
    (continuous_const.intervalIntegrable 0 current.contact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      current.contact.prefixReceipt
      (standingActionRunInventory stage)).intervalIntegrable
        0 current.contact.time.1)
    (fun actual actualMem => noWitness actual actualMem)
  have integralDebit :=
    standingActionProjectedPowerIntegral_le_movingEdgePayment stage
  have edgeLt :
      runMovingInventoryEdgePayment stackedShortCurrent
          shiftedStandingActionInventory (stage + 1) <
        threshold * current.contact.time.1 := by
    apply lt_of_not_ge
    intro paid
    apply failure
    unfold ButterflyMovingScaleCurrentDebitAt
    simpa only [current, threshold, mul_assoc] using paid
  have constantIntegral :
      (∫ _actual in (0 : Real)..current.contact.time.1, threshold) =
        threshold * current.contact.time.1 := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [constantIntegral] at integralLower
  dsimp only [current] at integralLower integralDebit edgeLt
  linarith

/-- A failure of the outcome-indexed instruction cannot occur on the exact
constructor.  It therefore exposes the same-prefix physical power witness
on the actual generated residual/obstruction constructor. -/
theorem butterflyOutcomeCurrentDebit_failure_witness
    (stage : Nat)
    (failure : ¬ ButterflyOutcomeCurrentDebitAt stage) :
    ∃ actual ∈ Set.Icc (0 : Real)
        (run stackedShortCurrent (stage + 1)).contact.time.1,
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          (standingActionRunInventory stage) actual <
        standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment =>
      exfalso
      apply failure
      unfold ButterflyOutcomeCurrentDebitAt
      rw [outcomeEq]
      trivial
  | generatedResidual =>
      apply butterflyMovingScaleCurrentDebit_failure_witness stage
      intro debit
      apply failure
      unfold ButterflyOutcomeCurrentDebitAt
      rw [outcomeEq]
      exact debit
  | obstruction =>
      apply butterflyMovingScaleCurrentDebit_failure_witness stage
      intro debit
      apply failure
      unfold ButterflyOutcomeCurrentDebitAt
      rw [outcomeEq]
      exact debit

/-- The complete sixteen-row source power remains above three on every
point of the selected initial prefix.  Both restrictions read the same
physical state of the original source receipt. -/
theorem stackedShortContact_prefix_netPower_gt_three
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      stackedShortContact.time.1) :
    (3 : Real) < actualProjectedWholeNetEnstrophyPower
      stackedShortContact.prefixReceipt butterflyFirstStackModes actual := by
  have actualLeShort : actual ≤ stackedShortDuration :=
    actualMem.2.trans stackedShortContact.time.2.2
  have actualMemOriginal : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) :=
    ⟨actualMem.1, actualLeShort.trans stackedShortDuration_le_full⟩
  have actualLtPower : actual < stackedReceiptWholePowerTime :=
    actualLeShort.trans_lt stackedShortDuration_lt_wholePowerTime
  have sourcePositive : (3 : Real) < stackedReceiptWholePowerAt actual := by
    by_cases actualZero : actual = 0
    · subst actual
      rw [stackedReceiptWholePowerAt_zero_eq]
      norm_num
    · exact stackedReceiptWholePowerTime_spec actual
        (lt_of_le_of_ne actualMem.1 (Ne.symm actualZero)) actualLtPower
  have stateEq :
      (actualWholeProjectedTransversePath
        stackedShortContact.prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath stackedReceipt actual).1 := by
    change stackedShortContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) stackedShortContact.time.1
          stackedShortContact.time_pos.le actual) =
      stackedReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedPhysicalSeed)
          stackedReceipt.requestedTimePos.le actual)
    rw [Set.projIcc_of_mem stackedShortContact.time_pos.le actualMem]
    rw [Set.projIcc_of_mem stackedReceipt.requestedTimePos.le
      actualMemOriginal]
    rfl
  unfold stackedReceiptWholePowerAt at sourcePositive
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [stateEq]
  exact sourcePositive

theorem stackedShortContact_prefix_netPower_integral_pos :
    0 < ∫ actual in (0 : Real)..stackedShortContact.time.1,
      actualProjectedWholeNetEnstrophyPower
        stackedShortContact.prefixReceipt butterflyFirstStackModes actual := by
  have lower := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume)
    stackedShortContact.time_pos.le
    (continuous_const.intervalIntegrable 0 stackedShortContact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      stackedShortContact.prefixReceipt
      butterflyFirstStackModes).intervalIntegrable
        0 stackedShortContact.time.1)
    (fun actual actualMem =>
      (stackedShortContact_prefix_netPower_gt_three
        actual actualMem).le)
  have normalized :
      (3 : Real) * stackedShortContact.time.1 ≤
        ∫ actual in (0 : Real)..stackedShortContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            stackedShortContact.prefixReceipt
            butterflyFirstStackModes actual := by
    simpa [intervalIntegral.integral_const, smul_eq_mul,
      mul_comm] using lower
  exact (mul_pos (by norm_num) stackedShortContact.time_pos).trans_le
    normalized

theorem stackedShortContact_sourceInventoryMass_gt_seed :
    (173 / 2 : Real) <
      finiteStateVorticityCoefficientEnstrophy butterflyFirstStackModes
        stackedShortContact.physicalState := by
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      stackedShortContact.prefixReceipt butterflyFirstStackModes
      butterflyFirstStackModes_zeroNotMem
  rw [stackedShortContact.prefixReceipt_terminal] at ledger
  have seedFiniteMass :
      finiteStateVorticityCoefficientEnstrophy butterflyFirstStackModes
          stackedSeedState = 173 / 2 := by
    calc
      finiteStateVorticityCoefficientEnstrophy butterflyFirstStackModes
          stackedSeedState = wholeVorticityEuclideanMass stackedSeedState :=
        (ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget.wholeVorticityEuclideanMass_eq_finite_of_supported
          butterflyFirstStackModes stackedSeedState
          (butterflyFirstStackPhysicalState_supported (-1))).symm
      _ = 173 / 2 := stackedSeedState_mass_eq
  rw [seedFiniteMass] at ledger
  linarith [stackedShortContact_prefix_netPower_integral_pos]

/-- The concrete root therefore starts with strictly less than one half unit
of moving bankroll: its anchor is `88`, while the same actual source carrier
already owns more than `173/2` units of finite coefficient mass. -/
theorem standingActionMovingResidualPotential_zero_lt_half :
    standingActionMovingResidualPotential 0 < 1 / 2 := by
  have anchorEq :
      (source.stateAfter 0).1.standing.anchorLevel = 88 := by
    change (runCellStanding stackedShortCurrent 0).anchorLevel = 88
    exact stackedShortCurrent_level_eq_eighty_eight
  rw [standingActionMovingResidualPotential_eq_anchor_sub_inventory,
    anchorEq]
  simp only [standingActionRunInventory, run_zero]
  have massGt := stackedShortContact_sourceInventoryMass_gt_seed
  change (173 / 2 : Real) <
    finiteStateVorticityCoefficientEnstrophy butterflyFirstStackModes
      stackedShortCurrent.contact.physicalState at massGt
  linarith

theorem standingActionMovingResidualPotential_zero_lt_two :
    standingActionMovingResidualPotential 0 < 2 :=
  standingActionMovingResidualPotential_zero_lt_half.trans (by norm_num)

/-- One total root transition preserves the strict two-unit bankroll bound.
Exact payment uses the existing reset theorem.  A residual/obstruction uses
only its current debit: the positive clock charge makes the signed moving
edge positive, and the exact residual coboundary then strictly lowers the
bankroll. -/
theorem standingActionMovingResidualPotential_succ_lt_two_of_outcomeDebit
    (stage : Nat)
    (currentLt : standingActionMovingResidualPotential stage < 2)
    (instruction : ButterflyOutcomeCurrentDebitAt stage) :
    standingActionMovingResidualPotential (stage + 1) < 2 := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      have materialCommutes :
          (nativeRestartStandingActionValuedArithmeticMaterial
              (source.stateAfter stage)).arithmeticMaterial.whole =
            (nativeRestartStandingActionValuedArithmeticMaterial
              (source.stateAfter stage)).arithmeticMaterial.left.parallel
              (nativeRestartStandingActionValuedArithmeticMaterial
                (source.stateAfter stage)).arithmeticMaterial.right := by
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at commutes
        rw [effect.effect_eq] at commutes
        exact commutes
      exact standingActionMovingResidualPotential_next_lt_two_of_exact
        stage materialCommutes
  | generatedResidual effect residual expansion expansionEq payment =>
      have debit : ButterflyMovingScaleCurrentDebitAt stage := by
        unfold ButterflyOutcomeCurrentDebitAt at instruction
        rw [outcomeEq] at instruction
        exact instruction
      have canonicalResidual : GeneratedParallelResidualAt
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage))
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial := by
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at residual
        rw [effect.effect_eq] at residual
        exact residual
      have chargePos : 0 <
          standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) *
            (run stackedShortCurrent (stage + 1)).contact.time.1 := by
        exact mul_pos
          (mul_pos standingActionMovingScalePowerCoefficient_pos
            (Real.rpow_pos_of_pos (by positivity) _))
          (run stackedShortCurrent (stage + 1)).contact.time_pos
      have edgePos : 0 <
          runMovingInventoryEdgePayment stackedShortCurrent
            shiftedStandingActionInventory (stage + 1) :=
        chargePos.trans_le debit
      have coboundary :=
        standingActionMovingResidualPotential_coboundary
          stage canonicalResidual
      linarith
  | obstruction obstruction demand =>
      have debit : ButterflyMovingScaleCurrentDebitAt stage := by
        unfold ButterflyOutcomeCurrentDebitAt at instruction
        rw [outcomeEq] at instruction
        exact instruction
      have canonicalResidual : GeneratedParallelResidualAt
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage))
          (nativeRestartStandingActionValuedArithmeticMaterial
            (source.stateAfter stage)).arithmeticMaterial := by
        have residual := obstruction.residual
        unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
          at residual
        rw [obstruction.effect.effect_eq] at residual
        exact residual
      have chargePos : 0 <
          standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) *
            (run stackedShortCurrent (stage + 1)).contact.time.1 := by
        exact mul_pos
          (mul_pos standingActionMovingScalePowerCoefficient_pos
            (Real.rpow_pos_of_pos (by positivity) _))
          (run stackedShortCurrent (stage + 1)).contact.time_pos
      have edgePos : 0 <
          runMovingInventoryEdgePayment stackedShortCurrent
            shiftedStandingActionInventory (stage + 1) :=
        chargePos.trans_le debit
      have coboundary :=
        standingActionMovingResidualPotential_coboundary
          stage canonicalResidual
      linarith

/-- Framework recursion of the bankroll bound over exactly the already-paid
finite prefix.  No all-future law is stored or requested. -/
theorem standingActionMovingResidualPotential_lt_two_of_priorOutcomeDebit
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    standingActionMovingResidualPotential length < 2 := by
  induction length with
  | zero => exact standingActionMovingResidualPotential_zero_lt_two
  | succ length inductionHypothesis =>
      exact
        standingActionMovingResidualPotential_succ_lt_two_of_outcomeDebit
          length
          (inductionHypothesis fun stage stageLt =>
            currentDebit stage
              (stageLt.trans (Nat.lt_succ_self length)))
          (currentDebit length (Nat.lt_succ_self length))

theorem standingActionAnchorLevel_ge_eightyEight (stage : Nat) :
    88 ≤ (source.stateAfter stage).1.standing.anchorLevel := by
  have folded :=
    runCellStanding_anchorLevel_eq_initial_add_paymentCount
      stackedShortCurrent stage
  rw [stackedShortCurrent_level_eq_eighty_eight] at folded
  have runLower : 88 ≤
      (runCellStanding stackedShortCurrent stage).anchorLevel := by
    omega
  have runtimeEq :=
    standingActionWholeRestartMediumSource_stateAfter_current
      stackedInitialActionMaterialInstruction stage
  have anchorEq := congrArg
    (fun runtime : GeneratedWholeRestartRuntimeCurrent
        butterflyGainViscosity => runtime.standing.anchorLevel)
    runtimeEq
  calc
    88 ≤ (runCellStanding stackedShortCurrent stage).anchorLevel := runLower
    _ = (source.stateAfter stage).1.standing.anchorLevel := by
      rw [show (runCellStanding stackedShortCurrent stage).anchorLevel =
          (runRuntime stackedShortCurrent stage).standing.anchorLevel by rfl]
      simpa only [source, stackedStandingActionMediumSource] using anchorEq.symm

/-- Every current before the first unpaid occurrence occupies all but less
than three units below its live standing anchor.  This is an exact readout
of the recursively bounded bankroll, not a new mass-retention premise. -/
theorem standingActionRunInventoryMass_gt_anchor_sub_three
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    ((source.stateAfter length).1.standing.anchorLevel : Real) - 3 <
      finiteStateVorticityCoefficientEnstrophy
        (standingActionRunInventory length)
        (run stackedShortCurrent length).contact.physicalState := by
  have bankroll :=
    standingActionMovingResidualPotential_lt_two_of_priorOutcomeDebit
      length currentDebit
  rw [standingActionMovingResidualPotential_eq_anchor_sub_inventory]
    at bankroll
  linarith

theorem butterflyRun_currentMass_gt_eightyFive_of_priorOutcomeDebit
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    (85 : Real) < wholeVorticityEuclideanMass
      (run stackedShortCurrent length).contact.physicalState := by
  have finiteLower := standingActionRunInventoryMass_gt_anchor_sub_three
    length currentDebit
  have anchorLowerNat := standingActionAnchorLevel_ge_eightyEight length
  have anchorLower : (88 : Real) ≤
      ((source.stateAfter length).1.standing.anchorLevel : Real) := by
    exact_mod_cast anchorLowerNat
  have finiteLeWhole := finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    (standingActionRunInventory length)
    (run stackedShortCurrent length).contact.physicalState
  linarith

/-- The same bounded bankroll makes the physical coefficient level a
faithful one-cell-neighbour of the live standing anchor.  This is the exact
discrete consequence of the current finite-mass lower bound. -/
theorem butterflyRun_currentLevel_eq_anchor_or_one_below
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    wholeRestartCoefficientLevel (run stackedShortCurrent length).contact =
        (source.stateAfter length).1.standing.anchorLevel ∨
      wholeRestartCoefficientLevel (run stackedShortCurrent length).contact + 1 =
        (source.stateAfter length).1.standing.anchorLevel := by
  let level := wholeRestartCoefficientLevel
    (run stackedShortCurrent length).contact
  let anchor := (source.stateAfter length).1.standing.anchorLevel
  have finiteLower := standingActionRunInventoryMass_gt_anchor_sub_three
    length currentDebit
  have finiteLeWhole := finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    (standingActionRunInventory length)
    (run stackedShortCurrent length).contact.physicalState
  have rawLe := wholeRestartRawCoefficientCeiling_le
    (run stackedShortCurrent length).contact
  rw [wholeRestartRawCoefficientCeiling_eq] at rawLe
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    at rawLe
  unfold wholeRestartCoefficientCeiling at rawLe
  have castGap : (anchor : Real) - 2 < (level : Real) := by
    dsimp only [anchor, level]
    linarith
  have anchorLeSucc : anchor ≤ level + 1 := by
    by_contra notLe
    have twoLeGap : level + 2 ≤ anchor := by omega
    have castTwoLeGap : (level : Real) + 2 ≤ (anchor : Real) := by
      exact_mod_cast twoLeGap
    linarith
  have levelLeAnchor : level ≤ anchor := by
    have generated :=
      NativeRestartStandingValuedArithmeticMaterialAt.standing_currentLevel_le_anchorLevel
        (runCellStanding stackedShortCurrent length)
    have runtimeEq :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction length
    have anchorEq := congrArg
      (fun runtime : GeneratedWholeRestartRuntimeCurrent
        butterflyGainViscosity => runtime.standing.anchorLevel)
      runtimeEq
    dsimp only [level, anchor]
    calc
      wholeRestartCoefficientLevel
          (run stackedShortCurrent length).contact ≤
        (runCellStanding stackedShortCurrent length).anchorLevel := generated
      _ = (source.stateAfter length).1.standing.anchorLevel := by
        rw [show (runCellStanding stackedShortCurrent length).anchorLevel =
            (runRuntime stackedShortCurrent length).standing.anchorLevel by rfl]
        simpa only [source, stackedStandingActionMediumSource] using
          anchorEq.symm
  dsimp only [level, anchor] at anchorLeSucc levelLeAnchor ⊢
  omega

theorem wholeRestartDuration_lt_one
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeRestartDuration current.contact < 1 := by
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let slope := sourceOwnedWholeStateBarrierSlope nu ceiling
  have slopePos : 0 < slope := by
    exact sourceOwnedWholeStateBarrierSlope_pos nu ceiling
  have coefficientNonneg :=
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption.sourceOwnedLocalQuadraticCoefficient_nonneg
      nu ceiling
  have slopeOne : (1 : Real) ≤ slope := by
    dsimp only [slope, sourceOwnedWholeStateBarrierSlope]
    exact le_add_of_nonneg_left
      (mul_nonneg coefficientNonneg (sq_nonneg ceiling))
  unfold wholeRestartDuration sourceOwnedWholeStateDuration
  apply (div_lt_iff₀ (mul_pos (by norm_num) slopePos)).2
  nlinarith

/-- Every actual next-contact clock is bounded by the seventh-order model at
its own physical coefficient level.  Unlike the exact-root specialization,
this statement needs no arithmetic branch. -/
theorem nextContact_time_le_standingActionBarrierModel
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    current.nextContact.time.1 ≤
      standingActionBarrierModel nu
        (wholeRestartCoefficientLevel current.contact) := by
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let coefficient := sourceOwnedWholeStateBarrierSeventhCoefficient nu
  have ceilingPos : 0 < ceiling :=
    wholeRestartCoefficientCeiling_pos current.contact
  have coefficientPos : 0 < coefficient :=
    sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu
  have modelBasePos : 0 < coefficient * ceiling ^ 7 := by positivity
  have durationLe := wholeRestartDuration_le_inverse_seventhBarrier current
  have denominatorLe :
      coefficient * ceiling ^ 7 ≤
        2 * (coefficient * ceiling ^ 7 + 1) := by
    nlinarith
  have reciprocalLe :
      1 / (2 * (coefficient * ceiling ^ 7 + 1)) ≤
        1 / (coefficient * ceiling ^ 7) :=
    one_div_le_one_div_of_le modelBasePos denominatorLe
  calc
    current.nextContact.time.1 ≤ wholeRestartDuration current.contact :=
      current.nextContact.time.2.2
    _ ≤ 1 / (2 * (coefficient * ceiling ^ 7 + 1)) := by
      simpa only [coefficient, ceiling] using durationLe
    _ ≤ 1 / (coefficient * ceiling ^ 7) := reciprocalLe
    _ = standingActionBarrierModel nu
        (wholeRestartCoefficientLevel current.contact) := by
      simp [standingActionBarrierModel, coefficient, ceiling,
        wholeRestartCoefficientCeiling, one_div]

/-- Before the first actual outcome not covered by the moving debit, the
preinstalled reset account contains at least two copies of the current
physical clock.  The proof uses only the generated near-standing level and
the source's own seventh-order clock bound. -/
theorem two_mul_sourceClock_le_movingResetReserve_of_priorOutcomeDebit
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    2 * source.clockAt (source.stateAfter length) ≤
      standingActionMovingResetReserve
        (source.stateAfter length).1.standing.anchorLevel := by
  let level := wholeRestartCoefficientLevel
    (run stackedShortCurrent length).contact
  let anchor := (source.stateAfter length).1.standing.anchorLevel
  have neighbour := butterflyRun_currentLevel_eq_anchor_or_one_below
    length currentDebit
  have anchorLower := standingActionAnchorLevel_ge_eightyEight length
  have clockLeModel := nextContact_time_le_standingActionBarrierModel
    (run stackedShortCurrent length)
  have sourceClockEq :
      source.clockAt (source.stateAfter length) =
        (run stackedShortCurrent length).nextContact.time.1 := by
    have currentEq :
        (source.stateAfter length).1.physical =
          run stackedShortCurrent length := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction length
      exact congrArg (fun current => current.physical) generated
    change (source.stateAfter length).1.physical.nextContact.time.1 = _
    rw [currentEq]
  have modelLeReserve := two_mul_barrierModel_le_movingResetReserve
    anchor level anchorLower neighbour
  have scaledClock :
      2 * (run stackedShortCurrent length).nextContact.time.1 ≤
        2 * standingActionBarrierModel butterflyGainViscosity level :=
    mul_le_mul_of_nonneg_left clockLeModel (by norm_num)
  dsimp only [level, anchor] at modelLeReserve scaledClock ⊢
  rw [sourceClockEq]
  exact scaledClock.trans modelLeReserve

/-- At any first unpaid occurrence the high current mass leaves only two
current-side physical possibilities.  A target above two activates the
existing kinetic clock settlement.  Otherwise the same edge loses more
than eighty-three units of whole coefficient mass, which dominates its
strictly subunit contact clock. -/
theorem butterflyRun_targetMassTwo_or_clock_lt_wholeMassDrop
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    2 ≤ wholeVorticityEuclideanMass
          (source.stateAfter length).1.physical.nextContact.physicalState ∨
      source.clockAt (source.stateAfter length) <
        wholeVorticityEuclideanMass
            (run stackedShortCurrent length).contact.physicalState -
          wholeVorticityEuclideanMass
            (run stackedShortCurrent length).nextContact.physicalState := by
  by_cases targetMass : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter length).1.physical.nextContact.physicalState
  · exact Or.inl targetMass
  · right
    have currentMass :=
      butterflyRun_currentMass_gt_eightyFive_of_priorOutcomeDebit
        length currentDebit
    have targetMassLt : wholeVorticityEuclideanMass
        (run stackedShortCurrent length).nextContact.physicalState < 2 := by
      apply lt_of_not_ge
      intro targetTwo
      apply targetMass
      have currentEq :
          (source.stateAfter length).1.physical =
            run stackedShortCurrent length := by
        have generated :=
          standingActionWholeRestartMediumSource_stateAfter_current
            stackedInitialActionMaterialInstruction length
        exact congrArg (fun current => current.physical) generated
      rw [currentEq]
      exact targetTwo
    have clockLt :
        (run stackedShortCurrent length).nextContact.time.1 < 1 :=
      (run stackedShortCurrent length).nextContact.time.2.2.trans_lt
        (wholeRestartDuration_lt_one (run stackedShortCurrent length))
    have sourceClockEq :
        source.clockAt (source.stateAfter length) =
          (run stackedShortCurrent length).nextContact.time.1 := by
      have currentEq :
          (source.stateAfter length).1.physical =
            run stackedShortCurrent length := by
        have generated :=
          standingActionWholeRestartMediumSource_stateAfter_current
            stackedInitialActionMaterialInstruction length
        exact congrArg (fun current => current.physical) generated
      change
        (source.stateAfter length).1.physical.nextContact.time.1 = _
      rw [currentEq]
    rw [sourceClockEq]
    linarith

def wholeMassClockPotential (state : source.State) : Real :=
  wholeVorticityEuclideanMass state.1.physical.contact.physicalState

theorem wholeMassClockPotential_nonneg (state : source.State) :
    0 ≤ wholeMassClockPotential state :=
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
    _

def wholeMassClockState (state : source.State) :
    SourceGeneratedRootClockStateAt source state where
  potential := wholeMassClockPotential state
  potential_nonneg := wholeMassClockPotential_nonneg state

def scaledWholeMassClockPotential
    (rate : Real) (state : source.State) : Real :=
  rate * wholeMassClockPotential state

theorem scaledWholeMassClockPotential_nonneg
    (rate : Real) (rateNonneg : 0 ≤ rate) (state : source.State) :
    0 ≤ scaledWholeMassClockPotential rate state :=
  mul_nonneg rateNonneg (wholeMassClockPotential_nonneg state)

def scaledWholeMassClockState
    (rate : Real) (rateNonneg : 0 ≤ rate) (state : source.State) :
    SourceGeneratedRootClockStateAt source state where
  potential := scaledWholeMassClockPotential rate state
  potential_nonneg :=
    scaledWholeMassClockPotential_nonneg rate rateNonneg state

/-- The collapse side of the first-unpaid dichotomy is itself an exact
current-side clock advance.  It spends the physical whole-mass drop on this
edge and carries no successor payment assertion. -/
def wholeMassRootClockAdvance_of_collapse
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage)
    (notTargetMassTwo : ¬ 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter length).1.physical.nextContact.physicalState) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter length)
      (wholeMassClockState (source.stateAfter length))
      (wholeMassClockState (source.stateAfter (length + 1))) := by
  have clockDrop := (butterflyRun_targetMassTwo_or_clock_lt_wholeMassDrop
    length currentDebit).resolve_left notTargetMassTwo
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt (source.stateAfter length) +
        wholeMassClockPotential (source.stateAfter (length + 1)) ≤
      wholeMassClockPotential (source.stateAfter length)
  unfold wholeMassClockPotential
  have nextEq :
      (source.stateAfter (length + 1)).1.physical.contact.physicalState =
        (run stackedShortCurrent length).nextContact.physicalState := by
    have nextCurrentEq :
        (source.stateAfter (length + 1)).1.physical =
          run stackedShortCurrent (length + 1) := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction (length + 1)
      exact congrArg (fun current => current.physical) generated
    rw [nextCurrentEq, run_succ, next_contact]
    rfl
  have currentEq :
      (source.stateAfter length).1.physical.contact.physicalState =
        (run stackedShortCurrent length).contact.physicalState := by
    have generated :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction length
    exact congrArg
      (fun current => current.physical.contact.physicalState) generated
  rw [nextEq, currentEq]
  linarith

/-- Causal low-target switch from the incoming prepaid face.  The rate is
computed from this exact edge as `clock / wholeMassDrop`; the reset reserve
already present before outcome resolution funds the entire scaled current
mass, and the remaining scaled target mass becomes the successor account.
No future clock or recurrence is read. -/
noncomputable def
    standingActionMovingKinetic_to_scaledWholeMass_collapseAdvance
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage)
    (notTargetMassTwo : ¬ 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter length).1.physical.nextContact.physicalState) :
    Σ nextClock : SourceGeneratedRootClockStateAt source
        (source.successor (source.stateAfter length)),
      SourceGeneratedRootClockAdvanceAt source (source.stateAfter length)
        (standingActionMovingKineticClockState length) nextClock := by
  let state := source.stateAfter length
  let currentMass := wholeVorticityEuclideanMass
    state.1.physical.contact.physicalState
  let targetMass := wholeVorticityEuclideanMass
    state.1.physical.nextContact.physicalState
  let massDrop := currentMass - targetMass
  let rate := source.clockAt state / massDrop
  have currentEq : state.1.physical = run stackedShortCurrent length := by
    dsimp only [state]
    have generated :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction length
    exact congrArg (fun current => current.physical) generated
  have currentMassGt : (85 : Real) < currentMass := by
    dsimp only [currentMass]
    rw [currentEq]
    exact butterflyRun_currentMass_gt_eightyFive_of_priorOutcomeDebit
      length currentDebit
  have targetMassLt : targetMass < 2 := by
    dsimp only [targetMass, state]
    exact lt_of_not_ge notTargetMassTwo
  have targetMassNonneg : 0 ≤ targetMass := by
    dsimp only [targetMass]
    exact
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
        _
  have massDropPos : 0 < massDrop := by
    dsimp only [massDrop]
    linarith
  have targetMassLeDrop : targetMass ≤ massDrop := by
    dsimp only [massDrop]
    linarith
  have rateNonneg : 0 ≤ rate := by
    dsimp only [rate]
    exact div_nonneg (source.clock_pos state).le massDropPos.le
  have rateMulDrop : rate * massDrop = source.clockAt state := by
    dsimp only [rate]
    exact div_mul_cancel₀ _ massDropPos.ne'
  have rateTargetLeClock : rate * targetMass ≤ source.clockAt state := by
    have scaled := mul_le_mul_of_nonneg_left targetMassLeDrop rateNonneg
    rwa [rateMulDrop] at scaled
  have scaledCurrentLeTwoClock :
      rate * currentMass ≤ 2 * source.clockAt state := by
    have massSplit : currentMass = massDrop + targetMass := by
      dsimp only [massDrop]
      ring
    rw [massSplit, mul_add, rateMulDrop]
    linarith
  have resetPays :=
    two_mul_sourceClock_le_movingResetReserve_of_priorOutcomeDebit
      length currentDebit
  have resetLePrepaid :
      standingActionMovingResetReserve state.1.standing.anchorLevel ≤
        standingActionMovingKineticClockPotential length := by
    unfold standingActionMovingKineticClockPotential
      standingActionMovingClockPotential
    have barrierNonneg := standingActionBarrierTail_nonneg
      butterflyGainViscosity state.1.standing.anchorLevel
    have weightedNonneg : 0 ≤
        standingActionMovingResidualWeight state.1.standing.anchorLevel *
          standingActionMovingResidualPotential length :=
      mul_nonneg (standingActionMovingResidualWeight_pos _).le
        (standingActionMovingResidualPotential_nonneg length)
    have kineticNonneg : 0 ≤
        puncturedWholeVorticityKineticMass
              state.1.physical.contact.physicalState /
            (2 * butterflyGainViscosity.coeff) :=
      div_nonneg (puncturedWholeVorticityKineticMass_nonneg _)
        (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le)
    dsimp only [state]
    linarith
  have scaledCurrentLePrepaid :
      rate * currentMass ≤
        standingActionMovingKineticClockPotential length := by
    exact scaledCurrentLeTwoClock.trans
      (resetPays.trans resetLePrepaid)
  let nextClock := scaledWholeMassClockState rate rateNonneg
    (source.stateAfter (length + 1))
  refine ⟨nextClock, ?_⟩
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt state +
        scaledWholeMassClockPotential rate
          (source.stateAfter (length + 1)) ≤
      standingActionMovingKineticClockPotential length
  have nextMassEq : wholeMassClockPotential
      (source.stateAfter (length + 1)) = targetMass := by
    unfold wholeMassClockPotential
    have nextCurrentEq :
        (source.stateAfter (length + 1)).1.physical =
          run stackedShortCurrent (length + 1) := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction (length + 1)
      exact congrArg (fun current => current.physical) generated
    rw [nextCurrentEq, run_succ, next_contact]
    dsimp only [targetMass, state]
    rw [currentEq]
    rfl
  unfold scaledWholeMassClockPotential
  rw [nextMassEq]
  have paidIdentity :
      source.clockAt state + rate * targetMass = rate * currentMass := by
    have massSplit : currentMass = massDrop + targetMass := by
      dsimp only [massDrop]
      ring
    rw [massSplit, mul_add, rateMulDrop]
  rw [paidIdentity]
  exact scaledCurrentLePrepaid

/-- Summed regeneration on exactly the inventory rows installed by the
previous root action.  The positive tangent-square term is retained before
the successor action material reads its time-zero power. -/
theorem expandedNewRowsPower_ge_previousGeneratedAction (stage : Nat) :
    let previous := run stackedShortCurrent stage
    let current := run stackedShortCurrent (stage + 1)
    let newRows := standingActionRunInventory (stage + 1) \
      standingActionRunInventory stage
    2 * ∑ wave ∈ newRows,
          (kineticSelfTangentWorkAt butterflyGainViscosity
                previous.contact.physicalState wave +
            previous.nextContact.time.1 * complexCoordinateVectorNormSq
              (wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                previous.contact.physicalState wave) -
            fullReplayGeneratedSelfWorkLossUpperAt previous
              previous.nextContact.time wave) ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt newRows 0 := by
  dsimp only
  let previous := run stackedShortCurrent stage
  let current := run stackedShortCurrent (stage + 1)
  let newRows := standingActionRunInventory (stage + 1) \
    standingActionRunInventory stage
  have currentEq : current = previous.next := by
    dsimp only [current, previous]
    rw [run_succ]
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  rw [actualProjectedWholeNetEnstrophyPower_eq_static, stateAtZero,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro wave waveMem
  have waveNe : wave ≠ 0 := fun waveZero =>
    standingActionRunInventory_zeroNotMem (stage + 1)
      (waveZero ▸ (Finset.mem_sdiff.mp waveMem).1)
  have generated :=
    fullReplay_sourceWork_add_generatedTangentSquare_sub_loss_le
      previous previous.nextContact.time wave waveNe
  have targetEq : previous.nextReceipt.wholePath
      previous.nextContact.time = current.contact.physicalState := by
    rw [currentEq, next_contact]
    rfl
  rw [targetEq] at generated
  exact generated

/-- Generic whole-inventory version of the same regeneration row.  It is
the actual source current, not a stage table: every retained and newly
installed output keeps its positive tangent-square contribution. -/
theorem nextInventoryPower_zero_ge_generatedAction
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    2 * ∑ wave ∈ modes,
          (kineticSelfTangentWorkAt nu
                current.contact.physicalState wave +
            current.nextContact.time.1 * complexCoordinateVectorNormSq
              (wholeLatticeVorticityFourierTangentAt nu.coeff
                current.contact.physicalState wave) -
            fullReplayGeneratedSelfWorkLossUpperAt current
              current.nextContact.time wave) ≤
      actualProjectedWholeNetEnstrophyPower
        current.next.nextReceipt modes 0 := by
  have stateAtZero :
      (actualWholeProjectedTransversePath current.next.nextReceipt 0).1 =
        current.next.contact.physicalState := by
    change current.next.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration current.next.contact)
          current.next.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem current.next.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.next.nextReceipt.requestedTimePos.le⟩]
    exact current.next.nextReceipt.wholePath_initial
  rw [actualProjectedWholeNetEnstrophyPower_eq_static, stateAtZero,
    finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro wave waveMem
  have waveNe : wave ≠ 0 := fun waveZero =>
    zeroNotMem (waveZero ▸ waveMem)
  have generated :=
    fullReplay_sourceWork_add_generatedTangentSquare_sub_loss_le
      current current.nextContact.time wave waveNe
  have targetEq : current.nextReceipt.wholePath
      current.nextContact.time =
        current.next.contact.physicalState := by
    rw [next_contact]
    rfl
  rw [targetEq] at generated
  exact generated

/-- The current invariant's retained time-zero power plus the previous
occurrence's complete generated action energy gives a lower instruction for
the whole successor inventory.  This is the strongest premise-free side of
the local advance before the concrete action inequality is discharged. -/
theorem successorInventoryPower_zero_ge_previousThreshold_add_actionBudget
    (stage : Nat)
    (invariant : ButterflyMovingScalePowerAt stage) :
    let previous := run stackedShortCurrent stage
    let current := run stackedShortCurrent (stage + 1)
    let modes := standingActionRunInventory (stage + 1)
    let newRows := modes \ standingActionRunInventory stage
    standingActionMovingScalePowerCoefficient *
          (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
            (5 / 4 : Real) +
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt
          newRows 0 +
        2 * ∑ wave ∈ modes,
          (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
            fullReplayGeneratedSelfWorkLossUpperAt previous
              previous.nextContact.time wave) ≤
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 := by
  dsimp only
  let previous := run stackedShortCurrent stage
  let current := run stackedShortCurrent (stage + 1)
  let modes := standingActionRunInventory (stage + 1)
  let newRows := modes \ standingActionRunInventory stage
  have generated := nextInventoryPower_zero_ge_generatedAction previous modes
    (standingActionRunInventory_zeroNotMem (stage + 1))
  have retainedAtZero := invariant 0
    ⟨le_rfl, (run stackedShortCurrent (stage + 1)).contact.time_pos.le⟩
  have retainedEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 1)).contact.prefixReceipt
          (standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt
          (standingActionRunInventory stage) 0 := by
    change
      actualProjectedWholeNetEnstrophyPower
          previous.nextContact.prefixReceipt
          (standingActionRunInventory stage) 0 =
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt
          (standingActionRunInventory stage) 0
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    have stateEq :
        (actualWholeProjectedTransversePath
            previous.nextContact.prefixReceipt 0).1 =
          (actualWholeProjectedTransversePath
            previous.nextReceipt 0).1 := by
      change previous.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) previous.nextContact.time.1
            previous.nextContact.time_pos.le 0) =
        previous.nextReceipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration previous.contact)
            previous.nextReceipt.requestedTimePos.le 0)
      rw [Set.projIcc_of_mem previous.nextContact.time_pos.le
        ⟨le_rfl, previous.nextContact.time_pos.le⟩]
      rw [Set.projIcc_of_mem previous.nextReceipt.requestedTimePos.le
        ⟨le_rfl, previous.nextReceipt.requestedTimePos.le⟩]
      rfl
    rw [stateEq]
  rw [retainedEq] at retainedAtZero
  have previousStateAtZero :
      (actualWholeProjectedTransversePath previous.nextReceipt 0).1 =
        previous.contact.physicalState := by
    change previous.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration previous.contact)
          previous.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem previous.nextReceipt.requestedTimePos.le
      ⟨le_rfl, previous.nextReceipt.requestedTimePos.le⟩]
    exact previous.nextReceipt.wholePath_initial
  have sourcePowerEq :
      2 * ∑ wave ∈ modes,
          kineticSelfTangentWorkAt butterflyGainViscosity
            previous.contact.physicalState wave =
        actualProjectedWholeNetEnstrophyPower previous.nextReceipt modes 0 := by
    rw [actualProjectedWholeNetEnstrophyPower_eq_static,
      previousStateAtZero,
      finiteWholeNetEnstrophyPowerAt_eq_two_mul_selfWork]
  have generated' :
      actualProjectedWholeNetEnstrophyPower previous.nextReceipt modes 0 +
          2 * ∑ wave ∈ modes,
            (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                  (wholeLatticeVorticityFourierTangentAt
                    butterflyGainViscosity.coeff
                    previous.contact.physicalState wave) -
              fullReplayGeneratedSelfWorkLossUpperAt previous
                previous.nextContact.time wave) ≤
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 := by
    rw [← sourcePowerEq]
    change
      2 * ∑ wave ∈ modes,
            (kineticSelfTangentWorkAt butterflyGainViscosity
                  previous.contact.physicalState wave +
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
              fullReplayGeneratedSelfWorkLossUpperAt previous
                previous.nextContact.time wave) ≤
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0
      at generated
    calc
      2 * ∑ wave ∈ modes,
            kineticSelfTangentWorkAt butterflyGainViscosity
              previous.contact.physicalState wave +
          2 * ∑ wave ∈ modes,
            (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                  (wholeLatticeVorticityFourierTangentAt
                    butterflyGainViscosity.coeff
                    previous.contact.physicalState wave) -
              fullReplayGeneratedSelfWorkLossUpperAt previous
                previous.nextContact.time wave) =
        2 * ∑ wave ∈ modes,
            (kineticSelfTangentWorkAt butterflyGainViscosity
                  previous.contact.physicalState wave +
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
              fullReplayGeneratedSelfWorkLossUpperAt previous
                previous.nextContact.time wave) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring
      _ ≤ _ := generated
  have split := actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    previous.nextReceipt (standingActionRunInventory stage) modes
      (standingActionRunInventory_nested stage)
  dsimp only [previous, current, modes, newRows] at retainedAtZero generated' ⊢
  dsimp only [previous, modes] at split
  rw [split] at generated'
  linarith

/-- Once the complete successor inventory owns its time-zero threshold plus
the rowwise outgoing correction, the same receipt generates the full next
power invariant.  No positivity is demanded separately from fresh rows. -/
private theorem butterflyMovingScalePowerAt_succ_of_zeroPowerTransport
    (stage : Nat)
    (zeroPower :
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) +
            2 * ∑ wave ∈ modes,
              fullReplayKineticSelfWorkLossUpperAt current time wave ≤
          actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0) :
    ButterflyMovingScalePowerAt (stage + 1) := by
  intro actual actualMem
  let current := run stackedShortCurrent (stage + 1)
  let modes := standingActionRunInventory (stage + 1)
  let time : Set.Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨actual, actualMem.1,
      actualMem.2.trans current.nextContact.time.2.2⟩
  have drift := abs_fullReplay_netPower_sub_zero_le_sum_selfWorkLoss
    current modes (standingActionRunInventory_zeroNotMem (stage + 1)) time
  have paid := zeroPower time
  have lowerDrift := neg_abs_le
    (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0)
  have timePowerEq :
      actualProjectedWholeNetEnstrophyPower
          (run stackedShortCurrent (stage + 2)).contact.prefixReceipt
          modes actual =
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 := by
    change
      actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes actual =
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    have stateEq :
        (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 =
          (actualWholeProjectedTransversePath
            current.nextReceipt time.1).1 := by
      change current.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) current.nextContact.time.1
            current.nextContact.time_pos.le actual) =
        current.nextReceipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
            current.nextReceipt.requestedTimePos.le time.1)
      rw [Set.projIcc_of_mem current.nextContact.time_pos.le actualMem]
      rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
      rfl
    rw [stateEq]
  rw [timePowerEq]
  dsimp only [current, modes] at drift paid lowerDrift ⊢
  linarith

/-- The positive regeneration term is a dependent projection of the
previous root's complete action material; the formal y-cell action cannot be
read without its complement/cross and whole-action residual. -/
theorem previousNewRowsTangentSquare_eq_actionMaterial (stage : Nat) :
    let state := source.stateAfter stage
    let newRows := standingActionRunInventory (stage + 1) \
      standingActionRunInventory stage
    (∑ wave ∈ newRows,
        complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            state.1.physical.contact.physicalState wave)) =
      ∑ wave ∈ newRows,
        complexCoordinateVectorNormSq
          (wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                state.2.dyadicYCellState wave +
              state.2.yCellComplementCrossAction wave +
              state.2.actionResidual wave) := by
  dsimp only
  let state := source.stateAfter stage
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  apply Finset.sum_congr rfl
  intro wave _waveMem
  have actionEq := material.wholeAction_commutes wave
  rw [material.actionInstruction_eq] at actionEq
  unfold classicalWholeNSVorticityTangent
    wholeLatticeVorticityFourierTangentAt at actionEq
  dsimp only [state] at actionEq ⊢
  unfold wholeLatticeVorticityFourierTangentAt
  rw [actionEq]

/-- Final internal shape of the vertical step.  The previous occurrence's
complete generated action energy pays the next anchor increment together
with both its incoming and successor-receipt transport corrections. -/
private theorem butterflyMovingScalePowerAt_succ_of_generatedActionBudget
    (stage : Nat)
    (invariant : ButterflyMovingScalePowerAt stage)
    (generatedAction :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          2 * ∑ wave ∈ modes,
            fullReplayKineticSelfWorkLossUpperAt current time wave ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
                fullReplayGeneratedSelfWorkLossUpperAt previous
                  previous.nextContact.time wave)) :
    ButterflyMovingScalePowerAt (stage + 1) := by
  apply butterflyMovingScalePowerAt_succ_of_zeroPowerTransport stage
  dsimp only
  intro time
  have lower :=
    successorInventoryPower_zero_ge_previousThreshold_add_actionBudget
      stage invariant
  have budget := generatedAction time
  linarith

/-- Exact vertical form for the stronger prepaid carrier.  The incoming
reserve supplies the retained threshold; the previous complete action row
must pay precisely the next threshold increment and the successor receipt's
outgoing correction.  Nothing about a future branch appears in the mouth. -/
private theorem butterflyMovingScalePowerReserveAt_succ_of_generatedActionBudget
    (stage : Nat)
    (reserve : ButterflyMovingScalePowerReserveAt stage)
    (generatedAction :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          2 * ∑ wave ∈ modes,
            fullReplayKineticSelfWorkLossUpperAt current time wave ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
                fullReplayGeneratedSelfWorkLossUpperAt previous
                  previous.nextContact.time wave)) :
    ButterflyMovingScalePowerReserveAt (stage + 1) := by
  dsimp only [ButterflyMovingScalePowerReserveAt]
  intro time
  have lower :=
    successorInventoryPower_zero_ge_previousThreshold_add_actionBudget
      stage reserve.power
  have budget := generatedAction time
  linarith

/-- Final scalar mouth for the prepaid local advance.  The complete action
sum has been consumed internally into `butterflyMovingScaleActionCredit`;
the remaining source equation contains only the fresh physical work and the
two corrections attached to the adjacent actual receipts. -/
private theorem butterflyMovingScalePowerReserveAt_succ_of_actionCreditBudget
    (stage : Nat)
    (reserve : ButterflyMovingScalePowerReserveAt stage)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          2 * ∑ wave ∈ modes,
            fullReplayKineticSelfWorkLossUpperAt current time wave +
          2 * ∑ wave ∈ modes,
            fullReplayGeneratedSelfWorkLossUpperAt previous
              previous.nextContact.time wave ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            butterflyMovingScaleActionCredit stage) :
    ButterflyMovingScalePowerReserveAt (stage + 1) := by
  apply butterflyMovingScalePowerReserveAt_succ_of_generatedActionBudget
    stage reserve
  dsimp only
  intro time
  have budget := sourceBudget time
  have credit := reserve.actionCredit_le_generatedAction
  rw [Finset.sum_sub_distrib]
  linarith

/-- Coupled residual specialization of the scalar mouth.  Root totality has
already proved that the anchor is retained, so only adjacent-receipt
corrections remain to be paid by fresh physical work plus current credit. -/
private theorem butterflyMovingScalePowerReserveAt_succ_of_coupledCreditBudget
    (stage : Nat)
    (reserve : ButterflyMovingScalePowerReserveAt stage)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        2 * ∑ wave ∈ modes,
              fullReplayKineticSelfWorkLossUpperAt current time wave +
            2 * ∑ wave ∈ modes,
              fullReplayGeneratedSelfWorkLossUpperAt previous
                previous.nextContact.time wave ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            butterflyMovingScaleActionCredit stage) :
    ButterflyMovingScalePowerReserveAt (stage + 1) := by
  apply butterflyMovingScalePowerReserveAt_succ_of_actionCreditBudget
    stage reserve
  dsimp only
  intro time
  have anchorEq := standingActionAnchorLevel_succ_eq_of_residual
    stage residual
  have budget := sourceBudget time
  rw [anchorEq]
  linarith

/-- Corrected vertical step for the faithful one-sided reserve.  The positive
action square retained by the endpoint ledger now appears once on the right,
while both adjacent corrections are the smaller generated losses. -/
private theorem butterflyMovingScaleGeneratedReserveAt_succ_of_actionBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleGeneratedReserveAt stage)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          2 * ∑ wave ∈ modes,
            fullReplayGeneratedSelfWorkLossUpperAt current time wave ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
                fullReplayGeneratedSelfWorkLossUpperAt previous
                  previous.nextContact.time wave)) :
    ButterflyMovingScaleGeneratedReserveAt (stage + 1) := by
  dsimp only [ButterflyMovingScaleGeneratedReserveAt]
  intro time
  have lower :=
    successorInventoryPower_zero_ge_previousThreshold_add_actionBudget
      stage reserve.power
  have budget := sourceBudget time
  linarith

/-- On coupled constructors the corrected local source law has no threshold
increment.  This is the exact live mouth after consuming root totality. -/
private theorem butterflyMovingScaleGeneratedReserveAt_succ_of_coupledBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleGeneratedReserveAt stage)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ standingActionRunInventory stage
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        2 * ∑ wave ∈ modes,
              fullReplayGeneratedSelfWorkLossUpperAt current time wave ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              (previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) -
                fullReplayGeneratedSelfWorkLossUpperAt previous
                  previous.nextContact.time wave)) :
    ButterflyMovingScaleGeneratedReserveAt (stage + 1) := by
  apply butterflyMovingScaleGeneratedReserveAt_succ_of_actionBudget
    stage reserve
  dsimp only
  intro time
  have anchorEq := standingActionAnchorLevel_succ_eq_of_residual
    stage residual
  have budget := sourceBudget time
  rw [anchorEq]
  linarith

/-- Final exact aggregate mouth.  Retained-row incoming debit has already
cancelled against the current reserve.  Only the fresh incoming debit and
the successor's exact outgoing debit remain. -/
private theorem butterflyMovingScaleExactReserveAt_succ_of_actionBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleExactReserveAt stage)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let oldModes := standingActionRunInventory stage
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ oldModes
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          fullReplayGeneratedPowerDefectAt current modes time +
          fullReplayGeneratedPowerDefectAt previous newRows
            previous.nextContact.time ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave)) :
    ButterflyMovingScaleExactReserveAt (stage + 1) := by
  dsimp only [ButterflyMovingScaleExactReserveAt]
  intro time
  have lower := successorInventoryPower_zero_ge_exactReserveAction
    stage reserve
  have budget := sourceBudget time
  linarith

/-- Coupled exact specialization: root residual totality removes the scale
increment, leaving a pure fresh-action settlement of two actual aggregate
defects. -/
private theorem butterflyMovingScaleExactReserveAt_succ_of_coupledBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleExactReserveAt stage)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let oldModes := standingActionRunInventory stage
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ oldModes
      ∀ time : Set.Icc (0 : Real) (wholeRestartDuration current.contact),
        fullReplayGeneratedPowerDefectAt current modes time +
            fullReplayGeneratedPowerDefectAt previous newRows
              previous.nextContact.time ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave)) :
    ButterflyMovingScaleExactReserveAt (stage + 1) := by
  apply butterflyMovingScaleExactReserveAt_succ_of_actionBudget stage reserve
  dsimp only
  intro time
  have anchorEq := standingActionAnchorLevel_succ_eq_of_residual
    stage residual
  have budget := sourceBudget time
  rw [anchorEq]
  linarith

/-- Authoritative selected-interval local advance.  Both exact defects now
belong to source-selected actual intervals; no unselected replay time remains
in the recurrence mouth. -/
private theorem
    butterflyMovingScaleSelectedExactReserveAt_succ_of_actionBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleSelectedExactReserveAt stage)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let oldModes := standingActionRunInventory stage
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ oldModes
      let previousSelected : Set.Icc (0 : Real)
          previous.nextContact.time.1 :=
        ⟨previous.nextContact.time.1,
          previous.nextContact.time_pos.le, le_rfl⟩
      ∀ time : Set.Icc (0 : Real) current.nextContact.time.1,
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          fullReplaySelectedGeneratedPowerDefectAt current modes time +
          fullReplaySelectedGeneratedPowerDefectAt previous newRows
            previousSelected ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave)) :
    ButterflyMovingScaleSelectedExactReserveAt (stage + 1) := by
  dsimp only [ButterflyMovingScaleSelectedExactReserveAt]
  intro time
  have lower := successorInventoryPower_zero_ge_selectedExactReserveAction
    stage reserve
  have budget := sourceBudget time
  linarith

private theorem
    butterflyMovingScaleSelectedExactReserveAt_succ_of_coupledBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleSelectedExactReserveAt stage)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let oldModes := standingActionRunInventory stage
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ oldModes
      let previousSelected : Set.Icc (0 : Real)
          previous.nextContact.time.1 :=
        ⟨previous.nextContact.time.1,
          previous.nextContact.time_pos.le, le_rfl⟩
      ∀ time : Set.Icc (0 : Real) current.nextContact.time.1,
        fullReplaySelectedGeneratedPowerDefectAt current modes time +
            fullReplaySelectedGeneratedPowerDefectAt previous newRows
              previousSelected ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave)) :
    ButterflyMovingScaleSelectedExactReserveAt (stage + 1) := by
  apply
    butterflyMovingScaleSelectedExactReserveAt_succ_of_actionBudget
      stage reserve
  dsimp only
  intro time
  have anchorEq := standingActionAnchorLevel_succ_eq_of_residual
    stage residual
  have budget := sourceBudget time
  rw [anchorEq]
  linarith

/-- Lossless selected-interval advance.  All current-side nonnegative assets
generated by the positive-part normal form remain available to the source
budget instead of being discarded by a lower-bound projection. -/
private theorem
    butterflyMovingScaleSelectedExactReserveAt_succ_of_fullLedgerBudget
    (stage : Nat)
    (_reserve : ButterflyMovingScaleSelectedExactReserveAt stage)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let oldModes := standingActionRunInventory stage
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ oldModes
      let previousSelected : Set.Icc (0 : Real)
          previous.nextContact.time.1 :=
        ⟨previous.nextContact.time.1,
          previous.nextContact.time_pos.le, le_rfl⟩
      ∀ time : Set.Icc (0 : Real) current.nextContact.time.1,
        (standingActionMovingScalePowerCoefficient *
              (((source.stateAfter (stage + 1)).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real) -
            standingActionMovingScalePowerCoefficient *
              (((source.stateAfter stage).1.standing.anchorLevel : Real) + 1) ^
                (5 / 4 : Real)) +
          fullReplaySelectedGeneratedPowerDefectAt current modes time +
          fullReplaySelectedGeneratedPowerDefectAt previous newRows
            previousSelected ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) +
            butterflyMovingScaleSelectedExactHeadroomAt
              stage previousSelected +
            fullReplaySelectedGeneratedPowerSurplusAt
              previous oldModes previousSelected +
            fullReplaySelectedGeneratedPowerSurplusAt
              previous newRows previousSelected) :
    ButterflyMovingScaleSelectedExactReserveAt (stage + 1) := by
  dsimp only [ButterflyMovingScaleSelectedExactReserveAt]
  intro time
  have ledger := successorInventoryPower_zero_eq_selectedExactLedger stage
  have budget := sourceBudget time
  linarith

private theorem
    butterflyMovingScaleSelectedExactReserveAt_succ_of_coupledFullLedgerBudget
    (stage : Nat)
    (reserve : ButterflyMovingScaleSelectedExactReserveAt stage)
    (residual : GeneratedParallelResidualAt
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage))
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).arithmeticMaterial)
    (sourceBudget :
      let previous := run stackedShortCurrent stage
      let current := run stackedShortCurrent (stage + 1)
      let oldModes := standingActionRunInventory stage
      let modes := standingActionRunInventory (stage + 1)
      let newRows := modes \ oldModes
      let previousSelected : Set.Icc (0 : Real)
          previous.nextContact.time.1 :=
        ⟨previous.nextContact.time.1,
          previous.nextContact.time_pos.le, le_rfl⟩
      ∀ time : Set.Icc (0 : Real) current.nextContact.time.1,
        fullReplaySelectedGeneratedPowerDefectAt current modes time +
            fullReplaySelectedGeneratedPowerDefectAt previous newRows
              previousSelected ≤
          actualProjectedWholeNetEnstrophyPower previous.nextReceipt
              newRows 0 +
            2 * ∑ wave ∈ modes,
              previous.nextContact.time.1 * complexCoordinateVectorNormSq
                (wholeLatticeVorticityFourierTangentAt
                  butterflyGainViscosity.coeff
                  previous.contact.physicalState wave) +
            butterflyMovingScaleSelectedExactHeadroomAt
              stage previousSelected +
            fullReplaySelectedGeneratedPowerSurplusAt
              previous oldModes previousSelected +
            fullReplaySelectedGeneratedPowerSurplusAt
              previous newRows previousSelected) :
    ButterflyMovingScaleSelectedExactReserveAt (stage + 1) := by
  apply
    butterflyMovingScaleSelectedExactReserveAt_succ_of_fullLedgerBudget
      stage reserve
  dsimp only
  intro time
  have anchorEq := standingActionAnchorLevel_succ_eq_of_residual
    stage residual
  have budget := sourceBudget time
  rw [anchorEq]
  linarith

def fixedRowKineticSpeed
    (nu : Viscosity)
    (kinetic : Real)
    (output : IntegerWavevector) : Real :=
  (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
      ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) * kinetic) +
    (nu.coeff * integerWaveViscousMultiplier output) *
      ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt kinetic)

theorem fixedRowKineticSpeed_nonneg
    (nu : Viscosity)
    (kinetic : Real)
    (kineticNonneg : 0 ≤ kinetic)
    (output : IntegerWavevector) :
    0 ≤ fixedRowKineticSpeed nu kinetic output := by
  unfold fixedRowKineticSpeed
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.sqrt_nonneg _))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)
          (Real.sqrt_nonneg _))
        kineticNonneg)
  · exact mul_nonneg
      (mul_nonneg nu.coeff_pos.le
        (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output)))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)
          (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))

theorem nextContact_row_sub_current_norm_le_kineticSpeed
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ‖current.nextContact.physicalState output -
        current.contact.physicalState output‖ ≤
      current.nextContact.time.1 *
        fixedRowKineticSpeed nu
          (puncturedWholeVorticityKineticMass
            current.contact.physicalState) output := by
  let receipt := current.nextReceipt
  let replay := generatedWholeRestartCanonicalReplay current.contact
  let closure := generatedWholeRestartCriticalClosure replay
  let kinetic := puncturedWholeVorticityKineticMass
    current.contact.physicalState
  let path := actualWholeContinuousHeatDuhamelPath receipt output
  let tangent : Real → ComplexCoordinateVector := fun actual =>
    actualWholeContinuousNonlinearRow receipt output actual -
      (nu.coeff * integerWaveViscousMultiplier output) • path actual
  let interval := Set.Icc (0 : Real) current.nextContact.time.1
  have kineticNonneg : 0 ≤ kinetic :=
    puncturedWholeVorticityKineticMass_nonneg _
  have pathDerivative : ∀ actual ∈ interval,
      HasDerivWithinAt path (tangent actual) interval actual := by
    intro actual _actualMem
    exact
      (heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
        (current.contact.physicalState output)
        (actualWholeContinuousNonlinearRow receipt output)
        (nu.coeff * integerWaveViscousMultiplier output)
        0 actual
        (actualWholeContinuousNonlinearRow_continuous receipt output)
      ).hasDerivWithinAt
  have tangentBound : ∀ actual ∈ interval,
      ‖tangent actual‖ ≤ fixedRowKineticSpeed nu kinetic output := by
    intro actual actualMem
    let physicalTime : Set.Icc (0 : Real)
        (wholeRestartDuration current.contact) :=
      ⟨actual, actualMem.1,
        actualMem.2.trans current.nextContact.time.2.2⟩
    let state := (actualWholeProjectedTransversePath receipt actual).1
    have stateEq : state = receipt.wholePath physicalTime := by
      change receipt.wholePath
          (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
            (wholeRestartDuration_pos current.contact).le actual) = _
      rw [Set.projIcc_of_mem
        (wholeRestartDuration_pos current.contact).le physicalTime.2]
    have stateZero : state 0 = 0 := by
      rw [stateEq]
      exact receipt.wholePath_zero_row physicalTime
    have stateTransverse : WholeStateTransverse state :=
      (actualWholeProjectedTransversePath receipt actual).2
    have stateKineticLe :
        puncturedWholeVorticityKineticMass state ≤ kinetic := by
      rw [stateEq]
      exact wholeRestartWholePath_kineticMass_le closure physicalTime
    have tangentAt := wholeVorticityTangent_norm_le_kineticMass
      nu state stateZero stateTransverse output outputNe
    have sqrtLe := Real.sqrt_le_sqrt stateKineticLe
    have rateLe :
        fixedRowKineticSpeed nu
            (puncturedWholeVorticityKineticMass state) output ≤
          fixedRowKineticSpeed nu kinetic output := by
      unfold fixedRowKineticSpeed
      apply add_le_add
      · gcongr
      · have multiplierNonneg : 0 ≤ integerWaveViscousMultiplier output :=
          mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left sqrtLe (by positivity))
          (mul_nonneg nu.coeff_pos.le multiplierNonneg)
    have pathEq : path actual = state output := by
      calc
        path actual = receipt.wholePath physicalTime output :=
          (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
            receipt output outputNe physicalTime).symm
        _ = state output :=
          (congrArg (fun value : ComplexVorticityHilbertState =>
            value output) stateEq).symm
    dsimp only [tangent]
    rw [pathEq]
    change
      ‖wholeLatticeVorticityFourierTangentAt nu.coeff state output‖ ≤ _
    exact tangentAt.trans rateLe
  let first : Set.Icc (0 : Real) current.nextContact.time.1 :=
    ⟨0, le_rfl, current.nextContact.time_pos.le⟩
  let second : Set.Icc (0 : Real) current.nextContact.time.1 :=
    ⟨current.nextContact.time.1,
      current.nextContact.time_pos.le, le_rfl⟩
  have increment := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    pathDerivative tangentBound
    (convex_Icc (0 : Real) current.nextContact.time.1)
    first.2 second.2
  have pathZero : path 0 = current.contact.physicalState output := by
    unfold path actualWholeContinuousHeatDuhamelPath
      heatDuhamelComplexCoordinatePath intervalIntegralComplexCoordinatePath
    simp
  have pathTerminal : path current.nextContact.time.1 =
      current.nextContact.physicalState output := by
    change actualWholeContinuousHeatDuhamelPath receipt output
        current.nextContact.time.1 = _
    let physicalTime : Set.Icc (0 : Real)
        (wholeRestartDuration current.contact) := current.nextContact.time
    exact (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      receipt output outputNe physicalTime).symm
  simpa only [pathZero, pathTerminal, second, first,
    sub_zero, Real.norm_eq_abs,
    abs_of_pos current.nextContact.time_pos, mul_comm] using increment

theorem fixedRowKineticSpeed_mono
    (nu : Viscosity)
    (output : IntegerWavevector)
    {left right : Real}
    (_leftNonneg : 0 ≤ left)
    (leftLe : left ≤ right) :
    fixedRowKineticSpeed nu left output ≤
      fixedRowKineticSpeed nu right output := by
  have sqrtLe := Real.sqrt_le_sqrt leftLe
  unfold fixedRowKineticSpeed
  apply add_le_add
  · gcongr
  · have multiplierNonneg : 0 ≤ integerWaveViscousMultiplier output :=
      mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left sqrtLe (by positivity))
      (mul_nonneg nu.coeff_pos.le multiplierNonneg)

theorem run_fixedRow_displacement_le_clockPrefix
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (length : Nat) :
    ‖(run initial length).contact.physicalState output -
        initial.contact.physicalState output‖ ≤
      fixedRowKineticSpeed nu
          (puncturedWholeVorticityKineticMass
            initial.contact.physicalState) output *
        (∑ stage ∈ Finset.range length,
          (run initial stage).nextContact.time.1) := by
  let row : Nat → ComplexCoordinateVector := fun stage =>
    (run initial stage).contact.physicalState output
  have telescope :
      (∑ stage ∈ Finset.range length,
          (row (stage + 1) - row stage)) = row length - row 0 := by
    simpa using Finset.sum_range_sub row length
  have edgeBound : ∀ stage,
      ‖row (stage + 1) - row stage‖ ≤
        (run initial stage).nextContact.time.1 *
          fixedRowKineticSpeed nu
            (puncturedWholeVorticityKineticMass
              initial.contact.physicalState) output := by
    intro stage
    have generated := nextContact_row_sub_current_norm_le_kineticSpeed
      (run initial stage) output outputNe
    have kineticLe :=
      (run_contact_kineticMass_antitone initial) (Nat.zero_le stage)
    have rateLe := fixedRowKineticSpeed_mono nu output
      (puncturedWholeVorticityKineticMass_nonneg _)
      (by simpa only [run_zero] using kineticLe)
    have scaled := mul_le_mul_of_nonneg_left rateLe
      (run initial stage).nextContact.time_pos.le
    change
      ‖(run initial (stage + 1)).contact.physicalState output -
          (run initial stage).contact.physicalState output‖ ≤ _
    rw [run_succ, next_contact]
    exact generated.trans scaled
  change ‖row length - row 0‖ ≤ _
  rw [← telescope]
  calc
    ‖∑ stage ∈ Finset.range length, (row (stage + 1) - row stage)‖ ≤
        ∑ stage ∈ Finset.range length,
          ‖row (stage + 1) - row stage‖ := norm_sum_le _ _
    _ ≤ ∑ stage ∈ Finset.range length,
        ((run initial stage).nextContact.time.1 *
          fixedRowKineticSpeed nu
            (puncturedWholeVorticityKineticMass
              initial.contact.physicalState) output) := by
      apply Finset.sum_le_sum
      intro stage _stageMem
      exact edgeBound stage
    _ = fixedRowKineticSpeed nu
          (puncturedWholeVorticityKineticMass
            initial.contact.physicalState) output *
        (∑ stage ∈ Finset.range length,
          (run initial stage).nextContact.time.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro stage _stageMem
      ring

/-- Before a first unpaid total-root occurrence, every fixed physical row
stays in the explicit ball funded by the initial moving clock potential.
This combines the framework's finite total-disposition fold with the actual
Duhamel row transport and assumes no payment on the terminal occurrence. -/
theorem butterflyRun_fixedRow_displacement_le_initialMovingPotential
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    ‖(run stackedShortCurrent length).contact.physicalState output -
        stackedShortCurrent.contact.physicalState output‖ ≤
      fixedRowKineticSpeed butterflyGainViscosity
          (puncturedWholeVorticityKineticMass
            stackedShortCurrent.contact.physicalState) output *
        standingActionMovingClockPotential 0 := by
  have clockPrefix :=
    butterflyMovingClockPrefix_le_initial_of_priorOutcomeDebit
      length currentDebit
  have sourceClockEq : ∀ stage : Nat,
      source.clockAt (source.stateAfter stage) =
        (run stackedShortCurrent stage).nextContact.time.1 := by
    intro stage
    have currentEq :
        (source.stateAfter stage).1.physical =
          run stackedShortCurrent stage := by
      have generated :=
        standingActionWholeRestartMediumSource_stateAfter_current
          stackedInitialActionMaterialInstruction stage
      exact congrArg (fun current => current.physical) generated
    change
      (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [currentEq]
  simp_rw [sourceClockEq] at clockPrefix
  have displacement := run_fixedRow_displacement_le_clockPrefix
    stackedShortCurrent output outputNe length
  have speedNonneg := fixedRowKineticSpeed_nonneg butterflyGainViscosity
    (puncturedWholeVorticityKineticMass
      stackedShortCurrent.contact.physicalState)
    (puncturedWholeVorticityKineticMass_nonneg _) output
  exact displacement.trans
    (mul_le_mul_of_nonneg_left clockPrefix speedNonneg)

def kineticBarrierPotential (state : source.State) : Real :=
  standingActionBarrierTail butterflyGainViscosity
      state.1.standing.anchorLevel +
    puncturedWholeVorticityKineticMass
        state.1.physical.contact.physicalState /
      (2 * butterflyGainViscosity.coeff)

theorem kineticBarrierPotential_nonneg (state : source.State) :
    0 ≤ kineticBarrierPotential state := by
  unfold kineticBarrierPotential
  exact add_nonneg
    (standingActionBarrierTail_nonneg _ _)
    (div_nonneg
      (puncturedWholeVorticityKineticMass_nonneg _)
      (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le))

def kineticBarrierClockState (state : source.State) :
    SourceGeneratedRootClockStateAt source state where
  potential := kineticBarrierPotential state
  potential_nonneg := kineticBarrierPotential_nonneg state

/-- Whole-mass/kinetic account with a hard physical cap at two.  Above the
cap, kinetic dissipation pays the clock.  Crossing below the cap releases
exactly the missing mass currency, so no branch selector enters the value. -/
def cappedMassKineticClockPotential (state : source.State) : Real :=
  min
      (wholeVorticityEuclideanMass
        state.1.physical.contact.physicalState)
      2 +
    puncturedWholeVorticityKineticMass
        state.1.physical.contact.physicalState /
      (2 * butterflyGainViscosity.coeff)

theorem cappedMassKineticClockPotential_nonneg (state : source.State) :
    0 ≤ cappedMassKineticClockPotential state := by
  unfold cappedMassKineticClockPotential
  have massNonneg : 0 ≤ wholeVorticityEuclideanMass
      state.1.physical.contact.physicalState :=
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
      _
  exact add_nonneg
    (le_min massNonneg (by norm_num))
    (div_nonneg
      (puncturedWholeVorticityKineticMass_nonneg _)
      (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le))

def cappedMassKineticClockState (state : source.State) :
    SourceGeneratedRootClockStateAt source state where
  potential := cappedMassKineticClockPotential state
  potential_nonneg := cappedMassKineticClockPotential_nonneg state

/-- Universal current-edge settlement while the incoming whole mass is at
least two.  It is independent of the root arithmetic outcome. -/
def cappedMassKineticRootClockAdvance
    (stage : Nat)
    (currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  let currentMass := wholeVorticityEuclideanMass
    state.1.physical.contact.physicalState
  let targetMass := wholeVorticityEuclideanMass
    state.1.physical.nextContact.physicalState
  let currentKinetic := puncturedWholeVorticityKineticMass
    state.1.physical.contact.physicalState
  let targetKinetic := puncturedWholeVorticityKineticMass
    state.1.physical.nextContact.physicalState
  let kineticDrop :=
    (currentKinetic - targetKinetic) /
      (2 * butterflyGainViscosity.coeff)
  let massPrefix : Real := wholePrefixVorticityMass
    state.1.physical.nextContact.time
    state.1.physical.nextReceipt.stateLimit
  have targetMassNonneg : 0 ≤ targetMass := by
    dsimp only [targetMass]
    exact
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing.wholeVorticityEuclideanMass_nonneg
        _
  have clockPos : 0 < source.clockAt state := source.clock_pos state
  have clockLtOne : source.clockAt state < 1 := by
    change state.1.physical.nextContact.time.1 < 1
    exact state.1.physical.nextContact.time.2.2.trans_lt
      (wholeRestartDuration_lt_one state.1.physical)
  have kineticLe := nextContact_kineticMass_le state.1.physical
  have kineticDropNonneg : 0 ≤ kineticDrop := by
    dsimp only [kineticDrop, currentKinetic, targetKinetic]
    exact div_nonneg (sub_nonneg.mpr kineticLe)
      (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le)
  have rectangle :=
    state.1.physical.nextContact_terminalMass_sub_one_mul_time_le_prefix
  have kineticDissipation := nextContact_kineticDissipation_le
    state.1.physical
  have coefficientPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have prefixLeKineticDrop : massPrefix ≤ kineticDrop := by
    apply (le_div_iff₀ coefficientPos).2
    dsimp only [massPrefix, kineticDrop, currentKinetic, targetKinetic]
    linarith
  have terminalRectangle :
      source.clockAt state * (targetMass - 1) ≤ kineticDrop := by
    change state.1.physical.nextContact.time.1 * (targetMass - 1) ≤ _
    exact rectangle.trans prefixLeKineticDrop
  have nextMassEq : wholeVorticityEuclideanMass
      nextState.1.physical.contact.physicalState = targetMass := by
    rfl
  have nextKineticEq : puncturedWholeVorticityKineticMass
      nextState.1.physical.contact.physicalState = targetKinetic := by
    rfl
  have currentMassEq : wholeVorticityEuclideanMass
      state.1.physical.contact.physicalState = currentMass := rfl
  have currentKineticEq : puncturedWholeVorticityKineticMass
      state.1.physical.contact.physicalState = currentKinetic := rfl
  have currentCap : min currentMass 2 = 2 := by
    exact min_eq_right (by simpa only [state, currentMass] using currentMassTwo)
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change source.clockAt state + cappedMassKineticClockPotential nextState ≤
    cappedMassKineticClockPotential state
  unfold cappedMassKineticClockPotential
  rw [nextMassEq, nextKineticEq, currentMassEq, currentKineticEq, currentCap]
  have kineticSplit :
      currentKinetic / (2 * butterflyGainViscosity.coeff) -
          targetKinetic / (2 * butterflyGainViscosity.coeff) =
        kineticDrop := by
    dsimp only [kineticDrop]
    ring
  by_cases targetTwo : 2 ≤ targetMass
  · rw [min_eq_right targetTwo]
    rw [← kineticSplit] at terminalRectangle
    have factorOne : 1 ≤ targetMass - 1 := by linarith
    have clockLeScaled : source.clockAt state ≤
        source.clockAt state * (targetMass - 1) := by
      calc
        source.clockAt state = source.clockAt state * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left factorOne clockPos.le
    linarith
  · have targetLtTwo : targetMass < 2 := lt_of_not_ge targetTwo
    rw [min_eq_left targetLtTwo.le]
    by_cases targetOne : 1 ≤ targetMass
    · rw [← kineticSplit] at terminalRectangle
      have complementNonneg : 0 ≤ 2 - targetMass := by linarith
      have scaledComplement :
          source.clockAt state * (2 - targetMass) ≤ 2 - targetMass := by
        have clockLeOne := clockLtOne.le
        nlinarith
      linarith
    · have targetLtOne : targetMass < 1 := lt_of_not_ge targetOne
      have massPays : source.clockAt state + targetMass ≤ 2 := by
        linarith
      linarith [kineticSplit, kineticDropNonneg]

def standingActionMovingCappedClockPotential (stage : Nat) : Real :=
  standingActionMovingClockPotential stage +
    cappedMassKineticClockPotential (source.stateAfter stage)

theorem standingActionMovingCappedClockPotential_nonneg (stage : Nat) :
    0 ≤ standingActionMovingCappedClockPotential stage :=
  add_nonneg (standingActionMovingClockPotential_nonneg stage)
    (cappedMassKineticClockPotential_nonneg (source.stateAfter stage))

def standingActionMovingCappedClockState (stage : Nat) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) where
  potential := standingActionMovingCappedClockPotential stage
  potential_nonneg := standingActionMovingCappedClockPotential_nonneg stage

/-- While the physical mass is above the cap, an already-paid moving edge
and the capped physical ledger advance together.  Both are generated from
the same root edge; their sum has one full clock of nonnegative slack. -/
def standingActionMovingCappedClockAdvance_of_movingAdvance
    (stage : Nat)
    (currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState)
    (movingAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1))) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingCappedClockState stage)
      (standingActionMovingCappedClockState (stage + 1)) := by
  have movingDomination :
      source.clockAt (source.stateAfter stage) +
          standingActionMovingClockPotential (stage + 1) ≤
        standingActionMovingClockPotential stage := by
    have settlement := movingAdvance.settlement
    have wasteNonneg := movingAdvance.waste_nonneg
    change
      standingActionMovingClockPotential stage =
        source.clockAt (source.stateAfter stage) +
          standingActionMovingClockPotential (stage + 1) +
            movingAdvance.waste at settlement
    linarith
  have cappedAdvance := cappedMassKineticRootClockAdvance
    stage currentMassTwo
  have cappedDomination :
      source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
        cappedMassKineticClockPotential (source.stateAfter stage) := by
    have settlement := cappedAdvance.settlement
    have wasteNonneg := cappedAdvance.waste_nonneg
    change
      cappedMassKineticClockPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) +
            cappedAdvance.waste at settlement
    linarith
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt (source.stateAfter stage) +
        standingActionMovingCappedClockPotential (stage + 1) ≤
      standingActionMovingCappedClockPotential stage
  unfold standingActionMovingCappedClockPotential
  have clockNonneg := (source.clock_pos (source.stateAfter stage)).le
  linarith

/-- At the first edge not covered by the moving debit, the incoming moving
account can be discarded: the capped physical account alone pays the entire
current edge and becomes the compiler-owned successor face. -/
def standingActionMovingCapped_to_cappedMassKineticAdvance
    (stage : Nat)
    (currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingCappedClockState stage)
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) := by
  have cappedAdvance := cappedMassKineticRootClockAdvance
    stage currentMassTwo
  have cappedDomination :
      source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
        cappedMassKineticClockPotential (source.stateAfter stage) := by
    have settlement := cappedAdvance.settlement
    have wasteNonneg := cappedAdvance.waste_nonneg
    change
      cappedMassKineticClockPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) +
            cappedAdvance.waste at settlement
    linarith
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
      standingActionMovingCappedClockPotential stage
  unfold standingActionMovingCappedClockPotential
  exact cappedDomination.trans
    (le_add_of_nonneg_left (standingActionMovingClockPotential_nonneg stage))

/-- Below the physical mass cap the root exact constructor is impossible:
the physical coefficient level is at most three while the source-generated
standing anchor is at least eighty-eight.  Hence the remaining capped-mode
responsibility belongs only to an actual residual/obstruction occurrence. -/
theorem lowMass_rootExact_isEmpty
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) : False := by
  have levelEq := standingActionRootExact_currentLevel_eq_anchorLevel
    effect commutes
  have rawLeThree : wholeRestartRawCoefficientCeiling
      (source.stateAfter stage).1.physical.contact ≤ 3 := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    linarith
  have levelLeThree : wholeRestartCoefficientLevel
      (source.stateAfter stage).1.physical.contact ≤ 3 := by
    exact Nat.ceil_le.mpr rawLeThree
  have anchorLower := standingActionAnchorLevel_ge_eightyEight stage
  omega

/-- Sole remaining source-side debit after the total prepaid/capped
transition.  It reads only the current low-mass physical edge. -/
def ButterflyLowMassCappedCurrentDebitAt (stage : Nat) : Prop :=
  source.clockAt (source.stateAfter stage) +
      cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
    cappedMassKineticClockPotential (source.stateAfter stage)

/-- The same current debit indexed by the actual generated-residual
occurrence.  Its signed mass change is read from that effect's valued action
material; `residual` and `expansion` keep the arithmetic and physical
provenance inseparable from the scalar inequality. -/
def ButterflyActualGeneratedResidualCurrentDebitAt
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (_expansion : source.OperationalResidualExpansionAt
      effect.effect residual) : Prop :=
  source.clockAt (source.stateAfter stage) +
        min
          (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState +
            effect.netEnstrophyDebit)
          2 -
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState ≤
    wholePrefixVorticityMass
      (source.stateAfter stage).1.physical.nextContact.time
      (source.stateAfter stage).1.physical.nextReceipt.stateLimit

/-- Local resolution demanded only after the framework has reached a
low-mass current and read its actual root outcome.  A generated residual
must expose its same-material debit.  On obstruction the framework first
tests the already available capped debit; only its failure must be physically
incompatible. -/
noncomputable def ButterflyLowMassRootResolutionAt (stage : Nat) : Prop :=
  match nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) with
  | .exactPayment .. => True
  | .generatedResidual effect residual expansion .. =>
      ButterflyActualGeneratedResidualCurrentDebitAt
        stage effect residual expansion
  | .obstruction .. =>
      ¬ ButterflyLowMassCappedCurrentDebitAt stage → False

/-- Exact scalar normal form of the low-mass debit.  The two terms on the
right are precisely the capped whole-mass loss and the kinetic defect of the
same root edge. -/
theorem butterflyLowMassCappedCurrentDebit_iff_physicalDrop
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) ≤
        wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState -
          min
            (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState)
            2 +
          (puncturedWholeVorticityKineticMass
                (source.stateAfter stage).1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
                (source.stateAfter stage).1.physical.nextContact.physicalState) /
              (2 * butterflyGainViscosity.coeff) := by
  have nextMassEq : wholeVorticityEuclideanMass
      (source.stateAfter (stage + 1)).1.physical.contact.physicalState =
    wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.nextContact.physicalState := by rfl
  have nextKineticEq : puncturedWholeVorticityKineticMass
      (source.stateAfter (stage + 1)).1.physical.contact.physicalState =
    puncturedWholeVorticityKineticMass
      (source.stateAfter stage).1.physical.nextContact.physicalState := by rfl
  have currentCap : min
      (wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState) 2 =
      wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState :=
    min_eq_left lowMass.le
  unfold ButterflyLowMassCappedCurrentDebitAt
    cappedMassKineticClockPotential
  rw [nextMassEq, nextKineticEq, currentCap]
  have split :
      wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState +
          puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.contact.physicalState /
            (2 * butterflyGainViscosity.coeff) -
        (min
            (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState)
            2 +
          puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.nextContact.physicalState /
            (2 * butterflyGainViscosity.coeff)) =
      wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState -
          min
            (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState)
            2 +
        (puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.nextContact.physicalState) /
          (2 * butterflyGainViscosity.coeff) := by ring
  constructor <;> intro payment <;> linarith [split]

/-- Exact path-integral form of the low-mass debit.  The source-selected
prefix mass is the kinetic defect divided by `2ν`; no density lower bound or
endpoint estimate is introduced. -/
theorem butterflyLowMassCappedCurrentDebit_iff_prefixMass
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) +
          min
            (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState)
            2 -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ≤
        wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
  have exactLedger :=
    (source.stateAfter stage).1.physical.nextContact_kineticDissipation_eq
  have coefficientPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have kineticDropEq :
      (puncturedWholeVorticityKineticMass
            (source.stateAfter stage).1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            (source.stateAfter stage).1.physical.nextContact.physicalState) /
            (2 * butterflyGainViscosity.coeff) =
        wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
    apply (div_eq_iff coefficientPos.ne').2
    linarith
  rw [butterflyLowMassCappedCurrentDebit_iff_physicalDrop stage lowMass,
    kineticDropEq]
  constructor <;> intro payment <;> linarith

/-- The dependent generated-residual debit is the same physical edge as the
capped clock debit.  This transporter uses only the effect compiler
equality; it accepts no target state or scalar payment. -/
theorem butterflyActualGeneratedResidualCurrentDebit_iff_capped
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    ButterflyActualGeneratedResidualCurrentDebitAt
        stage effect residual expansion ↔
      ButterflyLowMassCappedCurrentDebitAt stage := by
  have effectDebitEq : effect.netEnstrophyDebit =
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.nextContact.physicalState -
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState := by
    unfold NativeFluidMediumExactOperationalEffectAt.netEnstrophyDebit
    rw [effect.effect_eq]
    change
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit = _
    rw [(nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
    rfl
  rw [butterflyLowMassCappedCurrentDebit_iff_prefixMass stage lowMass]
  unfold ButterflyActualGeneratedResidualCurrentDebitAt
  rw [effectDebitEq]
  have targetEq :
      wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState +
          (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState -
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState) =
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.nextContact.physicalState := by
    ring
  rw [targetEq]

/-- The same low-mass debit after consuming the exact temporal-action row.
The kinetic term is not an independent estimate: it is literally the
selected clock multiplied by the source-generated mean vorticity density on
this root edge. -/
theorem butterflyLowMassCappedCurrentDebit_iff_meanDensity
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) ≤
        wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState -
          min
            (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState)
            2 +
          source.clockAt (source.stateAfter stage) *
            successorMeanWholeVorticityDensity stackedShortCurrent stage := by
  have currentEq :
      (source.stateAfter stage).1.physical =
        run stackedShortCurrent stage := by
    have generated :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    exact congrArg (fun current => current.physical) generated
  have balance :=
    (sourceGeneratedWholeRestartKineticEntropyDefect
      stackedShortCurrent stage).balance
  have clockLaw :=
    kineticDefect_eq_clock_mul_nativeDensity stackedShortCurrent stage
  have coefficientNe :
      2 * butterflyGainViscosity.coeff ≠ 0 :=
    (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos).ne'
  have sourceClockEq : source.clockAt (source.stateAfter stage) =
      (run stackedShortCurrent stage).nextContact.time.1 := by
    change (source.stateAfter stage).1.physical.nextContact.time.1 = _
    rw [currentEq]
  have kineticDropEq :
      (puncturedWholeVorticityKineticMass
            (source.stateAfter stage).1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            (source.stateAfter stage).1.physical.nextContact.physicalState) /
            (2 * butterflyGainViscosity.coeff) =
        source.clockAt (source.stateAfter stage) *
          successorMeanWholeVorticityDensity stackedShortCurrent stage := by
    have defectEq :
        puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.contact.physicalState -
            puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.nextContact.physicalState =
          wholeRestartKineticDefect stackedShortCurrent stage := by
      rw [currentEq]
      change
        wholeRestartKineticEntropy stackedShortCurrent stage -
            wholeRestartKineticEntropy stackedShortCurrent (stage + 1) =
          wholeRestartKineticDefect stackedShortCurrent stage
      linarith
    rw [defectEq, clockLaw]
    change
      ((run stackedShortCurrent (stage + 1)).contact.time.1 *
          (2 * butterflyGainViscosity.coeff *
            successorMeanWholeVorticityDensity stackedShortCurrent stage)) /
            (2 * butterflyGainViscosity.coeff) = _
    rw [run_succ, next_contact, sourceClockEq]
    field_simp [coefficientNe, butterflyGainViscosity.coeff_pos.ne']
  rw [butterflyLowMassCappedCurrentDebit_iff_physicalDrop stage lowMass,
    kineticDropEq]

/-- On a low-to-low residual edge the complete source obligation is a single
commuting inequality between the temporal-action density and the signed Real
valuation already stored in the standing/action material. -/
theorem butterflyLowMassCappedCurrentDebit_iff_materialNetDebit
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (targetLow : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.nextContact.physicalState < 2) :
    let material := nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) +
          material.standingMaterial.rawValuedMaterial.netEnstrophyDebit ≤
        source.clockAt (source.stateAfter stage) *
          successorMeanWholeVorticityDensity stackedShortCurrent stage := by
  dsimp only
  have materialDebitEq :
      (nativeRestartStandingActionValuedArithmeticMaterial
          (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit =
        wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.nextContact.physicalState -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState := by
    rw [(nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq]
    rw [(nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
    rfl
  rw [butterflyLowMassCappedCurrentDebit_iff_meanDensity stage lowMass,
    min_eq_left targetLow.le, materialDebitEq]
  constructor <;> intro payment <;> linarith

/-- Complete action/path form on a low-to-low edge.  This is the direct
source mouth: the whole-row action of the selected receipt and its spacetime
vorticity mass are the two sides of the current clock payment. -/
theorem butterflyLowMassCappedCurrentDebit_iff_wholeAction_le_prefixMass
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (targetLow : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.nextContact.physicalState < 2) :
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) +
          (∑' wave : IntegerWavevector,
            ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.actualWholeRowNetWork
              (source.stateAfter stage).1.physical.nextContact.prefixReceipt
              wave) ≤
        wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
  let raw := (nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter stage)).standingMaterial.rawValuedMaterial
  have rawDebitEq : raw.netEnstrophyDebit =
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.nextContact.physicalState -
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState := by
    dsimp only [raw]
    rw [(nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
    rfl
  have actionEq : raw.netEnstrophyDebit =
      ∑' wave : IntegerWavevector,
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.actualWholeRowNetWork
          (source.stateAfter stage).1.physical.nextContact.prefixReceipt wave := by
    dsimp only [raw]
    exact GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action _
  rw [butterflyLowMassCappedCurrentDebit_iff_prefixMass stage lowMass,
    min_eq_left targetLow.le]
  have leftEq :
      source.clockAt (source.stateAfter stage) +
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState =
        source.clockAt (source.stateAfter stage) + raw.netEnstrophyDebit := by
    rw [rawDebitEq]
    ring
  rw [leftEq, actionEq]

/-- Branch-free material normal form.  The target mass is reconstructed from
the current mass and the valued material's signed debit before applying the
physical cap.  Thus the sole residual obligation contains no foreign target
certificate and no separately selected scalar. -/
theorem butterflyLowMassCappedCurrentDebit_iff_cappedMaterialDebit
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    let material := nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) +
          min
            (wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState +
              material.standingMaterial.rawValuedMaterial.netEnstrophyDebit)
            2 -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ≤
        source.clockAt (source.stateAfter stage) *
          successorMeanWholeVorticityDensity stackedShortCurrent stage := by
  dsimp only
  have materialDebitEq :
      (nativeRestartStandingActionValuedArithmeticMaterial
          (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit =
        wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.nextContact.physicalState -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState := by
    rw [(nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
    rfl
  rw [butterflyLowMassCappedCurrentDebit_iff_meanDensity stage lowMass,
    materialDebitEq]
  have massEq :
      wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState +
          (wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState -
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState) =
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.nextContact.physicalState := by
    ring
  rw [massEq]
  constructor <;> intro payment <;> linarith

/-- Final branch-free direct splice from the complete current action to the
clock consumer.  Both the capped endpoint and the prefix payment are rebuilt
from the same selected receipt; this is the exact source inequality whose
proof closes the concrete law. -/
theorem butterflyLowMassCappedCurrentDebit_iff_cappedWholeAction_le_prefixMass
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyLowMassCappedCurrentDebitAt stage ↔
      source.clockAt (source.stateAfter stage) +
          min
            (wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState +
              (∑' wave : IntegerWavevector,
                ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.actualWholeRowNetWork
                  (source.stateAfter stage).1.physical.nextContact.prefixReceipt
                  wave))
            2 -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ≤
        wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
  let raw := (nativeRestartStandingActionValuedArithmeticMaterial
    (source.stateAfter stage)).standingMaterial.rawValuedMaterial
  have rawDebitEq : raw.netEnstrophyDebit =
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.nextContact.physicalState -
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState := by
    dsimp only [raw]
    rw [(nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
      (nativeRestartStandingActionValuedArithmeticMaterial
      (source.stateAfter stage)).standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
    rfl
  have actionEq : raw.netEnstrophyDebit =
      ∑' wave : IntegerWavevector,
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.actualWholeRowNetWork
          (source.stateAfter stage).1.physical.nextContact.prefixReceipt wave := by
    dsimp only [raw]
    exact GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action _
  have targetMassEq : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.nextContact.physicalState =
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState +
        (∑' wave : IntegerWavevector,
          ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.actualWholeRowNetWork
            (source.stateAfter stage).1.physical.nextContact.prefixReceipt
            wave) := by
    rw [← actionEq, rawDebitEq]
    ring
  rw [butterflyLowMassCappedCurrentDebit_iff_prefixMass stage lowMass,
    targetMassEq]

/-- Authoritative generated-residual mouth.  After preserving the dependent
effect/residual/expansion index, the required current payment is exactly the
whole-action/prefix identity of that selected receipt. -/
theorem
    butterflyActualGeneratedResidualCurrentDebit_iff_cappedWholeAction_le_prefixMass
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    ButterflyActualGeneratedResidualCurrentDebitAt
        stage effect residual expansion ↔
      source.clockAt (source.stateAfter stage) +
          min
            (wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState +
              (∑' wave : IntegerWavevector,
                ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.actualWholeRowNetWork
                  (source.stateAfter stage).1.physical.nextContact.prefixReceipt
                  wave))
            2 -
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ≤
        wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
  rw [butterflyActualGeneratedResidualCurrentDebit_iff_capped
      stage lowMass effect residual expansion,
    butterflyLowMassCappedCurrentDebit_iff_cappedWholeAction_le_prefixMass
      stage lowMass]

/-- The current contact compiler completely resolves failure of the capped
debit.  Either the source is on the strict half-critical side, or the
subcritical absorption row is active and the *combined* unweighted plus
gradient prefix payment is strictly smaller than the same current clock.
No future state or branch witness is supplied. -/
theorem butterflyLowMassCappedCurrentDebit_or_halfCritical_or_clockDeficit
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyLowMassCappedCurrentDebitAt stage ∨
      (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
            (2 * Real.pi) ^ 2 <
          criticalEnstrophyLatticeConstant *
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState ∨
      ((¬ (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
              (2 * Real.pi) ^ 2 <
            criticalEnstrophyLatticeConstant *
              wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState) ∧
        wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
                butterflyGainViscosity *
              wholePrefixVorticityGradientMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit ≤
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ∧
        wholePrefixVorticityMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
                butterflyGainViscosity *
              wholePrefixVorticityGradientMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit <
          source.clockAt (source.stateAfter stage)) := by
  by_cases debit : ButterflyLowMassCappedCurrentDebitAt stage
  · exact Or.inl debit
  · right
    by_cases critical :
        (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
              (2 * Real.pi) ^ 2 <
            criticalEnstrophyLatticeConstant *
              wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState
    · exact Or.inl critical
    · right
      have disposition :=
        (source.stateAfter stage).1.physical
          |>.nextContact_halfCriticalAbsorption_disposition
      have absorption :
          wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.nextContact.physicalState +
              2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
                  butterflyGainViscosity *
                wholePrefixVorticityGradientMass
                  (source.stateAfter stage).1.physical.nextContact.time
                  (source.stateAfter stage).1.physical.nextReceipt.stateLimit ≤
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState := by
        rcases disposition with crossed | absorption
        · exact False.elim (critical crossed)
        · exact absorption
      refine ⟨critical, absorption, ?_⟩
      have gradientNonneg : 0 ≤ wholePrefixVorticityGradientMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit :=
        wholePrefixVorticityGradientMass_nonneg _ _
      have absorptionCoefficientNonneg :
          0 ≤ 2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
            butterflyGainViscosity := by
        exact mul_nonneg (by norm_num)
          (criticalEnstrophyAbsorptionCoefficient_pos
            (1 / 2) (by norm_num) butterflyGainViscosity).le
      have gradientPaymentNonneg : 0 ≤
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
              butterflyGainViscosity *
            wholePrefixVorticityGradientMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit :=
        mul_nonneg absorptionCoefficientNonneg gradientNonneg
      have targetLow : wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.nextContact.physicalState < 2 :=
        ((le_add_of_nonneg_right gradientPaymentNonneg).trans
          absorption).trans_lt lowMass
      have debitIff :=
        butterflyLowMassCappedCurrentDebit_iff_prefixMass stage lowMass
      have deficit := lt_of_not_ge (debitIff.not.mp debit)
      rw [min_eq_left targetLow.le] at deficit
      linarith

/-- The two exact physical alternatives left after the current capped debit
fails.  This is not a branch premise: it is generated by the current
half-critical/absorption compiler. -/
def ButterflyLowMassPhysicalFailureAt (stage : Nat) : Prop :=
  (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
          (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ∨
    ((¬ (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
            (2 * Real.pi) ^ 2 <
          criticalEnstrophyLatticeConstant *
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState) ∧
      wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.nextContact.physicalState +
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
              butterflyGainViscosity *
            wholePrefixVorticityGradientMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit ≤
        wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState ∧
      wholePrefixVorticityMass
            (source.stateAfter stage).1.physical.nextContact.time
            (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
              butterflyGainViscosity *
            wholePrefixVorticityGradientMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit <
        source.clockAt (source.stateAfter stage))

/-- Total source-side strike at a low-mass current.  The framework's exact
outcome either already admits the local clock resolution, or the same
contact emits one of the two named physical failure rows.  In particular,
an obstruction with a valid capped debit is settled before incompatibility
is requested. -/
theorem butterflyLowMassRootResolution_or_physicalFailure
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyLowMassRootResolutionAt stage ∨
      ButterflyLowMassPhysicalFailureAt stage := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment =>
      left
      unfold ButterflyLowMassRootResolutionAt
      rw [outcomeEq]
      trivial
  | generatedResidual effect residual expansion expansionEq payment =>
      rcases butterflyLowMassCappedCurrentDebit_or_halfCritical_or_clockDeficit
          stage lowMass with debit | critical | deficit
      · left
        unfold ButterflyLowMassRootResolutionAt
        rw [outcomeEq]
        exact (butterflyActualGeneratedResidualCurrentDebit_iff_capped
          stage lowMass effect residual expansion).2 debit
      · right
        exact Or.inl critical
      · right
        exact Or.inr deficit
  | obstruction =>
      rcases butterflyLowMassCappedCurrentDebit_or_halfCritical_or_clockDeficit
          stage lowMass with debit | critical | deficit
      · left
        unfold ButterflyLowMassRootResolutionAt
        rw [outcomeEq]
        exact fun notDebit => notDebit debit
      · right
        exact Or.inl critical
      · right
        exact Or.inr deficit

/-- On an actual generated-residual constructor, failure of the capped
current debit cannot lose the root's quantitative provenance.  In the
subcritical absorption alternative the signed standing debit is
nonpositive, so the payment already stored in that same root outcome must
be the positive action-expansion valuation.  No branch or scalar payment is
supplied by the caller. -/
theorem
    butterflyLowMassGeneratedResidual_debit_or_halfCritical_or_expansionClockDeficit
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (_expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (payment : NativeFluidMediumResidualPaymentAt
      effect residual expansion) :
    ButterflyLowMassCappedCurrentDebitAt stage ∨
      (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
            (2 * Real.pi) ^ 2 <
          criticalEnstrophyLatticeConstant *
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState ∨
      ((¬ (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
              (2 * Real.pi) ^ 2 <
            criticalEnstrophyLatticeConstant *
              wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState) ∧
        wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.nextContact.physicalState +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
                butterflyGainViscosity *
              wholePrefixVorticityGradientMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit ≤
          wholeVorticityEuclideanMass
            (source.stateAfter stage).1.physical.contact.physicalState ∧
        0 < source.operationalResidualExpansionDebitAt
          effect.effect residual expansion ∧
        wholePrefixVorticityMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
                butterflyGainViscosity *
              wholePrefixVorticityGradientMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit <
          source.clockAt (source.stateAfter stage)) := by
  rcases butterflyLowMassCappedCurrentDebit_or_halfCritical_or_clockDeficit
      stage lowMass with debit | critical | deficit
  · exact Or.inl debit
  · exact Or.inr (Or.inl critical)
  · right
    right
    refine ⟨deficit.1, deficit.2.1, ?_, deficit.2.2⟩
    cases payment with
    | standingDebit positive =>
        have effectDebitEq : effect.netEnstrophyDebit =
            wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.nextContact.physicalState -
              wholeVorticityEuclideanMass
                (source.stateAfter stage).1.physical.contact.physicalState := by
          unfold NativeFluidMediumExactOperationalEffectAt.netEnstrophyDebit
          rw [effect.effect_eq]
          change
            (nativeRestartStandingActionValuedArithmeticMaterial
              (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit = _
          rw [(nativeRestartStandingActionValuedArithmeticMaterial
              (source.stateAfter stage)).standingMaterial.rawValuedMaterial.netEnstrophyDebit_eq,
            (nativeRestartStandingActionValuedArithmeticMaterial
              (source.stateAfter stage)).standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
            (nativeRestartStandingActionValuedArithmeticMaterial
              (source.stateAfter stage)).standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
          rfl
        have gradientNonneg : 0 ≤
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2)
                butterflyGainViscosity *
              wholePrefixVorticityGradientMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (criticalEnstrophyAbsorptionCoefficient_pos
                (1 / 2) (by norm_num) butterflyGainViscosity).le)
            (wholePrefixVorticityGradientMass_nonneg _ _)
        rw [effectDebitEq] at positive
        exfalso
        linarith [deficit.2.1]
    | expansionDebit positive =>
        exact positive

/-- After the total outcome and the physical absorption row are consumed,
a genuine low-mass clock failure on a generated residual exposes an actual
fresh Fourier face in the very same residual expansion.  This is the
source-owned material available to the next clock splice; no positivity or
inventory witness is accepted separately. -/
theorem butterflyLowMassGeneratedResidual_freshGain_of_clockFailure
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (payment : NativeFluidMediumResidualPaymentAt
      effect residual expansion)
    (clockFailure : ¬ ButterflyLowMassCappedCurrentDebitAt stage)
    (notHalfCritical : ¬
      (1 / 2 : Real) * butterflyGainViscosity.coeff ^ 2 *
            (2 * Real.pi) ^ 2 <
          criticalEnstrophyLatticeConstant *
            wholeVorticityEuclideanMass
              (source.stateAfter stage).1.physical.contact.physicalState) :
    expansion.standingExpansion.physicalModes.Nonempty ∨
      expansion.physicalModes.Nonempty := by
  rcases
      butterflyLowMassGeneratedResidual_debit_or_halfCritical_or_expansionClockDeficit
        stage lowMass effect residual expansion expansionEq payment with
    debit | critical | deficit
  · exact (clockFailure debit).elim
  · exact (notHalfCritical critical).elim
  · have positive := deficit.2.2.1
    change 0 < expansion.unionNetEnstrophyDebit at positive
    exact expansion.positive_unionDebit_has_freshGain positive

/-- Complete same-occurrence residual clock coboundary.  The standing and
action fresh faces are valued through their union, so a Fourier row cannot
be paid twice.  Kinetic dissipation, standing deficit and the one union
complement telescope exactly to the current prefix payment plus the current
source-generated expansion debit. -/
theorem butterflyGeneratedResidual_completeMaterial_coboundary
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    let state := source.stateAfter stage
    let raw := effect.effect.standingMaterial.rawValuedMaterial
    let unionSourceComplement :=
      wholeVorticityEuclideanMass raw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.sourcePhysicalState
    let unionTargetComplement :=
      wholeVorticityEuclideanMass raw.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.targetPhysicalState
    (puncturedWholeVorticityKineticMass
          state.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.sourceRemainingDeficit +
        unionSourceComplement) -
      (puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState /
            (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.targetRemainingDeficit +
        unionTargetComplement) =
      wholePrefixVorticityMass state.1.physical.nextContact.time
          state.1.physical.nextReceipt.stateLimit +
        source.operationalResidualExpansionDebitAt
          effect.effect residual expansion := by
  dsimp only
  let state := source.stateAfter stage
  let raw := effect.effect.standingMaterial.rawValuedMaterial
  have coefficientPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have kineticLedger := state.1.physical.nextContact_kineticDissipation_eq
  have kineticEq :
      puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState /
            (2 * butterflyGainViscosity.coeff) -
          puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState /
            (2 * butterflyGainViscosity.coeff) =
        wholePrefixVorticityMass state.1.physical.nextContact.time
          state.1.physical.nextReceipt.stateLimit := by
    rw [← sub_div]
    apply (div_eq_iff coefficientPos.ne').2
    linarith
  have effectDebitEq : effect.netEnstrophyDebit =
      raw.netEnstrophyDebit := by
    dsimp only [raw]
    unfold NativeFluidMediumExactOperationalEffectAt.netEnstrophyDebit
    rfl
  have standingDeficitEq :
      effect.effect.standingMaterial.sourceRemainingDeficit -
          effect.effect.standingMaterial.targetRemainingDeficit =
        effect.netEnstrophyDebit := by
    have deficit := effect.effect.standingMaterial.deficit_commutes
    rw [effect.effect.standingMaterial.paymentShadow_eq_zero_of_residual
      expansion.standingResidual] at deficit
    norm_num at deficit
    rw [effectDebitEq]
    linarith
  have unionComplementEq :
      (wholeVorticityEuclideanMass raw.sourcePhysicalState -
          finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
            raw.sourcePhysicalState) -
        (wholeVorticityEuclideanMass raw.targetPhysicalState -
          finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
            raw.targetPhysicalState) =
        expansion.unionNetEnstrophyDebit - effect.netEnstrophyDebit := by
    unfold NativeRestartStandingActionResidualExpansionAt.unionNetEnstrophyDebit
    rw [effectDebitEq, raw.netEnstrophyDebit_eq]
    ring
  have expansionDebitEq :
      source.operationalResidualExpansionDebitAt
          effect.effect residual expansion =
        expansion.unionNetEnstrophyDebit := rfl
  rw [expansionDebitEq]
  dsimp only [state, raw] at kineticEq standingDeficitEq unionComplementEq ⊢
  linarith

/-- Exact clock factorization through the complete residual material.  Both
potentials are nonnegative current/target projections of the same expansion,
and their local settlement is equivalent to one quantitative inequality in
which *all* generated finite debit has already been credited. -/
theorem butterflyGeneratedResidual_completeMaterial_clockFactorization
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    let state := source.stateAfter stage
    let raw := effect.effect.standingMaterial.rawValuedMaterial
    let unionSourceComplement :=
      wholeVorticityEuclideanMass raw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.sourcePhysicalState
    let unionTargetComplement :=
      wholeVorticityEuclideanMass raw.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.targetPhysicalState
    let sourcePotential :=
      puncturedWholeVorticityKineticMass
          state.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.sourceRemainingDeficit +
        unionSourceComplement
    let targetPotential :=
      puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.targetRemainingDeficit +
        unionTargetComplement
    0 ≤ sourcePotential ∧ 0 ≤ targetPotential ∧
      (source.clockAt state + targetPotential ≤ sourcePotential ↔
        source.clockAt state ≤ wholePrefixVorticityMass
              state.1.physical.nextContact.time
              state.1.physical.nextReceipt.stateLimit +
            source.operationalResidualExpansionDebitAt
              effect.effect residual expansion) := by
  dsimp only
  let state := source.stateAfter stage
  let raw := effect.effect.standingMaterial.rawValuedMaterial
  have sourceKineticNonneg : 0 ≤
      puncturedWholeVorticityKineticMass
          state.1.physical.contact.physicalState /
        (2 * butterflyGainViscosity.coeff) :=
    div_nonneg (puncturedWholeVorticityKineticMass_nonneg _)
      (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le)
  have targetKineticNonneg : 0 ≤
      puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState /
        (2 * butterflyGainViscosity.coeff) :=
    div_nonneg (puncturedWholeVorticityKineticMass_nonneg _)
      (mul_nonneg (by norm_num) butterflyGainViscosity.coeff_pos.le)
  have sourceDeficitNonneg :
      0 ≤ effect.effect.standingMaterial.sourceRemainingDeficit := by
    rw [effect.effect.standingMaterial.sourceRemainingDeficit_eq]
    exact state.1.standing.remainingCellDeficit_nonneg
  have targetDeficitNonneg :
      0 ≤ effect.effect.standingMaterial.targetRemainingDeficit := by
    rw [effect.effect.standingMaterial.targetRemainingDeficit_eq]
    exact effect.effect.standingMaterial.targetStanding.remainingCellDeficit_nonneg
  have unionSourceNonneg : 0 ≤
      wholeVorticityEuclideanMass raw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.sourcePhysicalState := by
    exact sub_nonneg.mpr
      (ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        expansion.physicalUnionModes raw.sourcePhysicalState)
  have unionTargetNonneg : 0 ≤
      wholeVorticityEuclideanMass raw.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.targetPhysicalState := by
    exact sub_nonneg.mpr
      (ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        expansion.physicalUnionModes raw.targetPhysicalState)
  refine ⟨?_, ?_, ?_⟩
  · exact add_nonneg
      (add_nonneg sourceKineticNonneg sourceDeficitNonneg)
      unionSourceNonneg
  · exact add_nonneg
      (add_nonneg targetKineticNonneg targetDeficitNonneg)
      unionTargetNonneg
  · have coboundary :=
      butterflyGeneratedResidual_completeMaterial_coboundary
        stage effect residual expansion
    dsimp only [state, raw] at coboundary ⊢
    constructor <;> intro payment <;> linarith

/-! ## Credit-bearing total-root splice

The older coupled adapter above projects the generated residual to one
endpoint scalar.  The constructions below retain the complete residual
expansion and capitalize every already-generated settlement waste into the
successor instruction.  Thus a coupled edge is charged only for the net
shortfall left after its union valuation and incoming finite bank have been
consumed. -/

/-- Non-kinetic source account carried by the complete residual material. -/
def butterflyGeneratedResidualSourceAccount
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) : Real :=
  let raw := effect.effect.standingMaterial.rawValuedMaterial
  effect.effect.standingMaterial.sourceRemainingDeficit +
    (wholeVorticityEuclideanMass raw.sourcePhysicalState -
      finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
        raw.sourcePhysicalState)

/-- Non-kinetic target account transported by the same residual expansion. -/
def butterflyGeneratedResidualTargetAccount
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) : Real :=
  let raw := effect.effect.standingMaterial.rawValuedMaterial
  effect.effect.standingMaterial.targetRemainingDeficit +
    (wholeVorticityEuclideanMass raw.targetPhysicalState -
      finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
        raw.targetPhysicalState)

theorem butterflyGeneratedResidualSourceAccount_nonneg
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    0 ≤ butterflyGeneratedResidualSourceAccount
      stage effect residual expansion := by
  have deficitNonneg :
      0 ≤ effect.effect.standingMaterial.sourceRemainingDeficit := by
    rw [effect.effect.standingMaterial.sourceRemainingDeficit_eq]
    exact (source.stateAfter stage).1.standing.remainingCellDeficit_nonneg
  have complementNonneg : 0 ≤
      wholeVorticityEuclideanMass
          effect.effect.standingMaterial.rawValuedMaterial.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy
          expansion.physicalUnionModes
          effect.effect.standingMaterial.rawValuedMaterial.sourcePhysicalState :=
    sub_nonneg.mpr
      (ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        expansion.physicalUnionModes
        effect.effect.standingMaterial.rawValuedMaterial.sourcePhysicalState)
  exact add_nonneg deficitNonneg complementNonneg

theorem butterflyGeneratedResidualTargetAccount_nonneg
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    0 ≤ butterflyGeneratedResidualTargetAccount
      stage effect residual expansion := by
  have deficitNonneg :
      0 ≤ effect.effect.standingMaterial.targetRemainingDeficit := by
    rw [effect.effect.standingMaterial.targetRemainingDeficit_eq]
    exact effect.effect.standingMaterial.targetStanding.remainingCellDeficit_nonneg
  have complementNonneg : 0 ≤
      wholeVorticityEuclideanMass
          effect.effect.standingMaterial.rawValuedMaterial.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy
          expansion.physicalUnionModes
          effect.effect.standingMaterial.rawValuedMaterial.targetPhysicalState :=
    sub_nonneg.mpr
      (ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        expansion.physicalUnionModes
        effect.effect.standingMaterial.rawValuedMaterial.targetPhysicalState)
  exact add_nonneg deficitNonneg complementNonneg

/-- The complete residual account loses exactly the generated union debit.
This is the quantitative projection that the endpoint-only adapter omitted. -/
theorem butterflyGeneratedResidualAccount_coboundary
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    butterflyGeneratedResidualSourceAccount stage effect residual expansion -
        butterflyGeneratedResidualTargetAccount stage effect residual expansion =
      source.operationalResidualExpansionDebitAt
        effect.effect residual expansion := by
  have complete := butterflyGeneratedResidual_completeMaterial_coboundary
    stage effect residual expansion
  have coefficientPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have kineticLedger :=
    (source.stateAfter stage).1.physical.nextContact_kineticDissipation_eq
  have kineticEq :
      puncturedWholeVorticityKineticMass
            (source.stateAfter stage).1.physical.contact.physicalState /
            (2 * butterflyGainViscosity.coeff) -
          puncturedWholeVorticityKineticMass
            (source.stateAfter stage).1.physical.nextContact.physicalState /
            (2 * butterflyGainViscosity.coeff) =
        wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit := by
    rw [← sub_div]
    apply (div_eq_iff coefficientPos.ne').2
    linarith
  dsimp only [butterflyGeneratedResidualSourceAccount,
    butterflyGeneratedResidualTargetAccount] at complete ⊢
  linarith

/-- A finite root instruction retains its predecessor's complete total
disposition.  In particular, a coupled predecessor keeps the generated
expansion, physical payment and `nextNormalForm`; they are not projected to
a stage-indexed scalar. -/
def ButterflyCreditBearingPredecessorAt (state : source.State) : Type :=
  Σ stage : Nat,
    Σ outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage),
      { _disposition : SourceGeneratedStandingActionRunClockDispositionAt
          stackedInitialActionMaterialInstruction stage outcome //
        state = source.stateAfter (stage + 1) }

/-- Root-owned finite bank.  Its value is part of the generated instruction,
while `predecessor?` retains the complete material that generated it. -/
structure ButterflyCreditBearingClockInstructionAt
    (state : source.State) : Type where
  stage : Nat
  state_eq : state = source.stateAfter stage
  bank : Real
  bank_nonneg : 0 ≤ bank
  predecessor? : Option (ButterflyCreditBearingPredecessorAt state)

def butterflyKineticBankClockState
    (stage : Nat) (bank : Real) (bankNonneg : 0 ≤ bank) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) where
  potential := kineticCompensatedPotential
      butterflyActionKineticCoefficient (source.stateAfter stage) + bank
  potential_nonneg := add_nonneg
    (kineticCompensatedPotential_nonneg
      butterflyActionKineticCoefficient
      butterflyActionKineticCoefficient_nonneg _) bankNonneg

def butterflyCreditBearingClockState
    {state : source.State}
    (instruction : ButterflyCreditBearingClockInstructionAt state) :
    SourceGeneratedRootClockStateAt source state where
  potential := kineticCompensatedPotential
      butterflyActionKineticCoefficient state + instruction.bank
  potential_nonneg := add_nonneg
    (kineticCompensatedPotential_nonneg
      butterflyActionKineticCoefficient
      butterflyActionKineticCoefficient_nonneg state)
    instruction.bank_nonneg

/-- The concrete initial instruction carries a finite full physical account.
This is a current source readout, not a caller-supplied headroom premise. -/
def butterflyInitialCreditBank : Real :=
  (source.initial).1.standing.remainingCellDeficit +
    wholeVorticityEuclideanMass
      (source.initial).1.physical.contact.physicalState

theorem butterflyInitialCreditBank_nonneg :
    0 ≤ butterflyInitialCreditBank := by
  unfold butterflyInitialCreditBank
  have wholeNonneg : 0 ≤ wholeVorticityEuclideanMass
      (source.initial).1.physical.contact.physicalState := by
    have finiteLe :=
      ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        (∅ : Finset IntegerWavevector)
        (source.initial).1.physical.contact.physicalState
    simpa [finiteStateVorticityCoefficientEnstrophy] using finiteLe
  exact add_nonneg
    (source.initial.1.standing.remainingCellDeficit_nonneg)
    wholeNonneg

/-- One actual sideband already forces the compiler-owned first target above
the kinetic threshold.  The proof uses the source-selected reserve and the
same row's strict generated gain; no target-mass premise is supplied. -/
theorem stackedShortCurrent_nextContact_wholeMass_gt_two :
    (2 : Real) < wholeVorticityEuclideanMass
      stackedShortCurrent.nextContact.physicalState := by
  let wave := plusSideband
  have waveMem : wave ∈ stackedSidebandModes := by
    simp [wave, stackedSidebandModes, plusSideband]
  have reserve :=
    (stackedShortContact_sourcePatch.2.2 wave waveMem).1
  have seedMass :=
    butterflyFirstStackPhysicalState_negOne_sideband_mass_eq wave
      (Or.inl rfl)
  change complexCoordinateAmplitudeSq (stackedSeedState wave) = 121 / 8
    at seedMass
  have cauchy := complexCoordinateRealInner_sq_le
    (stackedSeedState wave)
    (stackedShortCurrent.contact.physicalState wave)
  unfold sourceReserveAt at reserve
  rw [seedMass] at cauchy
  have sourceMass : (2 : Real) < complexCoordinateAmplitudeSq
      (stackedShortCurrent.contact.physicalState wave) := by
    nlinarith
  have targetGain := stackedSideband_nextContact_amplitudeSq_gt
    wave waveMem
  have targetMass : (2 : Real) < complexCoordinateAmplitudeSq
      (stackedShortCurrent.nextContact.physicalState wave) :=
    sourceMass.trans targetGain
  have finiteLeWhole :=
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      ({wave} : Finset IntegerWavevector)
      stackedShortCurrent.nextContact.physicalState
  have singletonMass :
      finiteStateVorticityCoefficientEnstrophy
          ({wave} : Finset IntegerWavevector)
          stackedShortCurrent.nextContact.physicalState =
        complexCoordinateAmplitudeSq
          (stackedShortCurrent.nextContact.physicalState wave) := by
    simp [finiteStateVorticityCoefficientEnstrophy]
  rw [singletonMass] at finiteLeWhole
  exact targetMass.trans_le finiteLeWhole

def butterflyCreditBearingInitialInstruction :
    ButterflyCreditBearingClockInstructionAt source.initial where
  stage := 0
  state_eq := rfl
  bank := butterflyInitialCreditBank
  bank_nonneg := butterflyInitialCreditBank_nonneg
  predecessor? := none

/-- Exact remaining obligation after the complete current material and the
incoming bank have both been retained.  Settled constructors add no source
obligation.  Coupled constructors use their actual expansion target, so the
union debit is consumed by the complete-material coboundary. -/
def ButterflyCreditBearingCurrentPaymentAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Prop :=
  match disposition with
  | .settled _settlement => True
  | .generatedResidualAdvance (effect := effect) (residual := residual)
      (expansion := expansion) _actionResidual _nextNormalForm =>
      source.clockAt (source.stateAfter stage) +
          (kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter stage) + instruction.bank
  | .obstructionAdvance (obstruction := obstruction)
      _actionResidual _nextNormalForm =>
      source.clockAt (source.stateAfter stage) +
          (kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage obstruction.effect obstruction.residual
                obstruction.expansion) ≤
        kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter stage) + instruction.bank

/-- Scalar readout of the corrected coupled mouth.  The old prefix payment
is augmented by the same expansion's union debit and by the incoming bank
after reserving the expansion's source account.  All three terms come from
the current dependent instruction/material pair. -/
theorem butterflyCoupledCompletePayment_iff_endpointResidual
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    (source.clockAt (source.stateAfter stage) +
          (kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter stage) + instruction.bank) ↔
      let state := source.stateAfter stage
      let prefixMass := wholePrefixVorticityMass
        state.1.physical.nextContact.time
        state.1.physical.nextReceipt.stateLimit
      (-state.2.yCellEndpointResidualReadout) ≤
        (2 * butterflyGainViscosity.coeff *
              finiteModeKineticAmbientFactor state.2.dyadicChildModes +
            state.2.yCellCoreCharge) * prefixMass +
          state.2.yCellCoreCharge *
            source.operationalResidualExpansionDebitAt
              effect.effect residual expansion +
          state.2.yCellCoreCharge *
            (instruction.bank -
              butterflyGeneratedResidualSourceAccount
                stage effect residual expansion) := by
  dsimp only
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  let prefixMass := wholePrefixVorticityMass
    state.1.physical.nextContact.time
    state.1.physical.nextReceipt.stateLimit
  have chargePos : 0 < state.2.yCellCoreCharge :=
    state.2.yCellCoreCharge_pos
  have debitCoboundary :=
    butterflyCoupledActionKineticCurrentDebit_eq_clockCoboundary
      stage effect residual
  have debitPrefix :=
    butterflyCoupledActionKineticCurrentDebit_eq_prefixAction stage
  have actual := actualDyadicWholeActionReadout_eq_core_add_complement state
  have endpoint := state.2.yCellEndpointResidualReadout_eq_action_add_euler
  have clockEq : source.clockAt state =
      state.1.physical.nextContact.time.1 := rfl
  have actionEq :
      source.clockAt state *
            (actualDyadicWholeActionReadout state -
              state.2.yCellCoreCharge) +
          state.2.yCellEulerErrorReadout =
        state.2.yCellEndpointResidualReadout := by
    rw [clockEq, actual, endpoint]
    ring
  have baseCoboundary :
      state.2.yCellCoreCharge *
          (kineticCompensatedPotential butterflyActionKineticCoefficient state -
            kineticCompensatedPotential butterflyActionKineticCoefficient
              nextState - source.clockAt state) =
        (2 * butterflyGainViscosity.coeff *
              finiteModeKineticAmbientFactor state.2.dyadicChildModes +
            state.2.yCellCoreCharge) * prefixMass +
          state.2.yCellEndpointResidualReadout := by
    dsimp only [state, nextState, prefixMass] at debitCoboundary debitPrefix actionEq
    dsimp only [state, nextState, prefixMass]
    linarith
  have accountCoboundary :=
    butterflyGeneratedResidualAccount_coboundary
      stage effect residual expansion
  dsimp only [state, nextState, prefixMass] at baseCoboundary accountCoboundary
  have totalCoboundary :
      (source.stateAfter stage).2.yCellCoreCharge *
          (kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter stage) -
              kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) -
              source.clockAt (source.stateAfter stage) +
            instruction.bank -
              butterflyGeneratedResidualTargetAccount
                stage effect residual expansion) =
        (2 * butterflyGainViscosity.coeff *
              finiteModeKineticAmbientFactor
                (source.stateAfter stage).2.dyadicChildModes +
            (source.stateAfter stage).2.yCellCoreCharge) *
              wholePrefixVorticityMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
          (source.stateAfter stage).2.yCellEndpointResidualReadout +
          (source.stateAfter stage).2.yCellCoreCharge *
            source.operationalResidualExpansionDebitAt
              effect.effect residual expansion +
          (source.stateAfter stage).2.yCellCoreCharge *
            (instruction.bank -
              butterflyGeneratedResidualSourceAccount
                stage effect residual expansion) := by
    calc
      _ = (source.stateAfter stage).2.yCellCoreCharge *
            (kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter stage) -
              kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) -
              source.clockAt (source.stateAfter stage)) +
          (source.stateAfter stage).2.yCellCoreCharge *
            (butterflyGeneratedResidualSourceAccount
                stage effect residual expansion -
              butterflyGeneratedResidualTargetAccount
                stage effect residual expansion) +
          (source.stateAfter stage).2.yCellCoreCharge *
            (instruction.bank -
              butterflyGeneratedResidualSourceAccount
                stage effect residual expansion) := by ring
      _ = _ := by rw [baseCoboundary, accountCoboundary]
  constructor
  · intro payment
    have netNonneg : 0 ≤
        kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter stage) -
            kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter (stage + 1)) -
            source.clockAt (source.stateAfter stage) + instruction.bank -
          butterflyGeneratedResidualTargetAccount
            stage effect residual expansion := by
      linarith
    have scaledNonneg := mul_nonneg chargePos.le netNonneg
    rw [totalCoboundary] at scaledNonneg
    linarith
  · intro payment
    have totalNonneg : 0 ≤
        (2 * butterflyGainViscosity.coeff *
              finiteModeKineticAmbientFactor
                (source.stateAfter stage).2.dyadicChildModes +
            (source.stateAfter stage).2.yCellCoreCharge) *
              wholePrefixVorticityMass
                (source.stateAfter stage).1.physical.nextContact.time
                (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
          (source.stateAfter stage).2.yCellEndpointResidualReadout +
          (source.stateAfter stage).2.yCellCoreCharge *
            source.operationalResidualExpansionDebitAt
              effect.effect residual expansion +
          (source.stateAfter stage).2.yCellCoreCharge *
            (instruction.bank -
              butterflyGeneratedResidualSourceAccount
                stage effect residual expansion) := by
      linarith
    rw [← totalCoboundary] at totalNonneg
    have netNonneg :=
      (mul_nonneg_iff_of_pos_left chargePos).mp totalNonneg
    linarith

/-- The generated residual's standing successor is not a parallel future
table: after consuming the compiler equality it is exactly the standing
material installed on the root-owned next state. -/
theorem butterflyGeneratedResidual_nextStandingMaterial_commutes
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual) :
    HEq expansion.standingExpansion.nextMaterial
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter (stage + 1))).standingMaterial := by
  subst expansion
  cases Subsingleton.elim effect
    (nativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
  rfl

/-- The action fresh-gain face used by the current residual is already
installed in the compiler-owned successor action carrier.  Thus its target
complement may be carried as a typed successor instruction; no sibling
inventory or post-hoc radius is required. -/
theorem butterflyGeneratedResidual_actionModes_installedAtNext
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual) :
    expansion.physicalModes ⊆
      (source.stateAfter (stage + 1)).2.modes := by
  subst expansion
  cases Subsingleton.elim effect
    (nativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
  intro wave waveMem
  change wave ∈
      (nativeRestartStandingActionValuedArithmeticMaterial
        (source.stateAfter stage)).actionFreshGainModes at waveMem
  change wave ∈ (source.stateAfter stage).2.advance.modes
  exact (Finset.mem_filter.mp waveMem).1

/-- Capitalize an already-generated settlement waste instead of discarding
it.  The successor bank is `bank + waste`, and the outer edge has zero
waste because the complete amount is retained by the next instruction. -/
def butterflyKineticAdvance_capitalizeBank
    (stage : Nat)
    (bank : Real)
    (bankNonneg : 0 ≤ bank)
    (advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyActionKineticClockState stage)
      (butterflyActionKineticClockState (stage + 1))) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (butterflyKineticBankClockState stage bank bankNonneg)
        (butterflyKineticBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let nextBank : Real := bank + advance.waste
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg bankNonneg advance.waste_nonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := advance.settlement
        change
          kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter stage) =
            source.clockAt (source.stateAfter stage) +
              kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) + advance.waste
          at settlement
        change
          kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter stage) + bank =
            source.clockAt (source.stateAfter stage) +
              (kineticCompensatedPotential butterflyActionKineticCoefficient
                  (source.stateAfter (stage + 1)) + nextBank) + 0
        dsimp only [nextBank]
        linarith }

def butterflyKineticSettlement_capitalizeBank
    (stage : Nat)
    (bank : Real)
    (bankNonneg : 0 ≤ bank)
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (settlement : SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyActionKineticClockState stage)
      (butterflyActionKineticClockState (stage + 1)) outcome) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyKineticBankClockState stage bank bankNonneg)
        (butterflyKineticBankClockState (stage + 1)
          nextBank.1 nextBank.2) outcome := by
  cases settlement with
  | exactPayment advance =>
      rcases butterflyKineticAdvance_capitalizeBank
        stage bank bankNonneg advance with ⟨nextBank, nextAdvance⟩
      exact ⟨nextBank, .exactPayment nextAdvance⟩
  | generatedResidual advance =>
      rcases butterflyKineticAdvance_capitalizeBank
        stage bank bankNonneg advance with ⟨nextBank, nextAdvance⟩
      exact ⟨nextBank, .generatedResidual nextAdvance⟩
  | obstructionAlternative advance =>
      rcases butterflyKineticAdvance_capitalizeBank
        stage bank bankNonneg advance with ⟨nextBank, nextAdvance⟩
      exact ⟨nextBank, .obstructionAlternative nextAdvance⟩
  | obstructionIncompatible incompatible =>
      exact False.elim incompatible

/-- Consume a coupled expansion and capitalize its complete same-edge
surplus.  The target complement and every leftover unit both enter the
successor bank; no post-hoc successor debt is created. -/
def butterflyCoupledAdvance_capitalizeCompleteMaterial
    (stage : Nat)
    (bank : Real)
    (bankNonneg : 0 ≤ bank)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (domination :
      source.clockAt (source.stateAfter stage) +
          (kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter stage) + bank) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (butterflyKineticBankClockState stage bank bankNonneg)
        (butterflyKineticBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let targetAccount := butterflyGeneratedResidualTargetAccount
    stage effect residual expansion
  let surplus :=
    kineticCompensatedPotential butterflyActionKineticCoefficient
          (source.stateAfter stage) + bank -
      source.clockAt (source.stateAfter stage) -
      (kineticCompensatedPotential butterflyActionKineticCoefficient
          (source.stateAfter (stage + 1)) + targetAccount)
  have targetNonneg : 0 ≤ targetAccount :=
    butterflyGeneratedResidualTargetAccount_nonneg
      stage effect residual expansion
  have surplusNonneg : 0 ≤ surplus := by
    dsimp only [surplus, targetAccount]
    linarith
  let nextBank := targetAccount + surplus
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg targetNonneg surplusNonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        change
          kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter stage) + bank =
            source.clockAt (source.stateAfter stage) +
              (kineticCompensatedPotential butterflyActionKineticCoefficient
                  (source.stateAfter (stage + 1)) + nextBank) + 0
        dsimp only [nextBank, surplus, targetAccount]
        ring }

/-- One complete total-root transition.  The settled constructor transports
its original waste; a coupled constructor transports its expansion,
physical payment and next normal form through `predecessor?`, while its
complete target account and surplus become the successor bank. -/
noncomputable def butterflyCreditBearingTransition_of_payment
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (currentPayment : ButterflyCreditBearingCurrentPaymentAt
      stage instruction disposition) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCreditBearingClockState instruction)
        (butterflyCreditBearingClockState nextInstruction) outcome := by
  cases disposition with
  | settled settlement =>
      let kineticSettlement :=
        butterflyActionKineticClockSettlement_of_mixedSettlement
          stage settlement
      rcases butterflyKineticSettlement_capitalizeBank
        stage instruction.bank instruction.bank_nonneg kineticSettlement with
        ⟨nextBank, nextSettlement⟩
      let predecessor : ButterflyCreditBearingPredecessorAt
          (source.stateAfter (stage + 1)) :=
        ⟨stage, _, ⟨.settled settlement, rfl⟩⟩
      let nextInstruction : ButterflyCreditBearingClockInstructionAt
          (source.stateAfter (stage + 1)) :=
        { stage := stage + 1
          state_eq := rfl
          bank := nextBank.1
          bank_nonneg := nextBank.2
          predecessor? := some predecessor }
      refine ⟨nextInstruction, ?_⟩
      simpa only [butterflyCreditBearingClockState,
        butterflyKineticBankClockState,
        NativeFluidMediumSource.stateAfter_succ, nextInstruction,
        source, stackedStandingActionMediumSource] using
        nextSettlement
  | generatedResidualAdvance actionResidual nextNormalForm =>
      rename_i effect residual expansion expansionEq residualPayment
      change
        source.clockAt (source.stateAfter stage) +
            (kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount
                stage effect residual expansion) ≤
          kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter stage) + instruction.bank
        at currentPayment
      rcases butterflyCoupledAdvance_capitalizeCompleteMaterial
        stage instruction.bank instruction.bank_nonneg effect residual
          expansion currentPayment with ⟨nextBank, nextAdvance⟩
      let generatedDisposition :
          SourceGeneratedStandingActionRunClockDispositionAt
            stackedInitialActionMaterialInstruction stage
              (.generatedResidual effect residual expansion expansionEq
                residualPayment) :=
        .generatedResidualAdvance actionResidual nextNormalForm
      let predecessor : ButterflyCreditBearingPredecessorAt
          (source.stateAfter (stage + 1)) :=
        ⟨stage, _, ⟨generatedDisposition, rfl⟩⟩
      let nextInstruction : ButterflyCreditBearingClockInstructionAt
          (source.stateAfter (stage + 1)) :=
        { stage := stage + 1
          state_eq := rfl
          bank := nextBank.1
          bank_nonneg := nextBank.2
          predecessor? := some predecessor }
      refine ⟨nextInstruction, ?_⟩
      simpa only [butterflyCreditBearingClockState,
        butterflyKineticBankClockState,
        NativeFluidMediumSource.stateAfter_succ, nextInstruction,
        source, stackedStandingActionMediumSource] using
        (SourceGeneratedRootClockSettlementAt.generatedResidual
          (effect := effect) (residual := residual)
          (expansion := expansion) (expansion_eq := expansionEq)
          (payment := residualPayment) nextAdvance)
  | obstructionAdvance actionResidual nextNormalForm =>
      rename_i obstruction demand
      change
        source.clockAt (source.stateAfter stage) +
            (kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount stage
                obstruction.effect obstruction.residual
                  obstruction.expansion) ≤
          kineticCompensatedPotential butterflyActionKineticCoefficient
              (source.stateAfter stage) + instruction.bank
        at currentPayment
      rcases butterflyCoupledAdvance_capitalizeCompleteMaterial
        stage instruction.bank instruction.bank_nonneg obstruction.effect
          obstruction.residual obstruction.expansion currentPayment with
        ⟨nextBank, nextAdvance⟩
      let generatedDisposition :
          SourceGeneratedStandingActionRunClockDispositionAt
            stackedInitialActionMaterialInstruction stage
              (.obstruction obstruction demand) :=
        .obstructionAdvance actionResidual nextNormalForm
      let predecessor : ButterflyCreditBearingPredecessorAt
          (source.stateAfter (stage + 1)) :=
        ⟨stage, _, ⟨generatedDisposition, rfl⟩⟩
      let nextInstruction : ButterflyCreditBearingClockInstructionAt
          (source.stateAfter (stage + 1)) :=
        { stage := stage + 1
          state_eq := rfl
          bank := nextBank.1
          bank_nonneg := nextBank.2
          predecessor? := some predecessor }
      refine ⟨nextInstruction, ?_⟩
      simpa only [butterflyCreditBearingClockState,
        butterflyKineticBankClockState,
        NativeFluidMediumSource.stateAfter_succ, nextInstruction,
        source, stackedStandingActionMediumSource] using
        (SourceGeneratedRootClockSettlementAt.obstructionAlternative
          (obstruction := obstruction) (demand := demand) nextAdvance)

/-- Framework totality at the corrected interface.  Failure is now exactly
the net current shortfall after complete expansion valuation and carried
credit, never the old endpoint-only scalar. -/
def ButterflyCreditBearingTransitionResultAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (butterflyCreditBearingClockState nextInstruction) outcome) ⊕
    PLift (¬ ButterflyCreditBearingCurrentPaymentAt
      stage instruction disposition)

noncomputable def butterflyCreditBearingTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyCreditBearingTransitionResultAt
      stage instruction disposition := by
  by_cases payment : ButterflyCreditBearingCurrentPaymentAt
      stage instruction disposition
  · exact Sum.inl
      (butterflyCreditBearingTransition_of_payment
        stage instruction disposition payment)
  · exact Sum.inr ⟨payment⟩

/-- Vertical rebase identity for two consecutive actual generated
residuals.  The physical current, kinetic account and standing remaining
deficit cancel definitionally through the compiler-owned successor.  The
entire cross-edge responsibility is therefore the change of the two
generated complement faces—nothing else is missing from the ledger. -/
theorem butterflyConsecutiveGeneratedResidual_completeMaterial_rebase
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (nextEffect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter (stage + 1)))
    (nextResidual : GeneratedParallelResidualAt
      nextEffect.effect nextEffect.arithmeticMaterial)
    (nextExpansion : source.OperationalResidualExpansionAt
      nextEffect.effect nextResidual)
    (nextExpansionEq : nextExpansion =
      source.generateOperationalResidualExpansionAt
        nextEffect.effect nextResidual) :
    let state := source.stateAfter stage
    let nextState := source.stateAfter (stage + 1)
    let raw := effect.effect.standingMaterial.rawValuedMaterial
    let nextRaw := nextEffect.effect.standingMaterial.rawValuedMaterial
    let targetPotential :=
      puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.targetRemainingDeficit +
        (wholeVorticityEuclideanMass raw.targetPhysicalState -
          finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
            raw.targetPhysicalState)
    let nextSourcePotential :=
      puncturedWholeVorticityKineticMass
          nextState.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        nextEffect.effect.standingMaterial.sourceRemainingDeficit +
        (wholeVorticityEuclideanMass nextRaw.sourcePhysicalState -
          finiteStateVorticityCoefficientEnstrophy nextExpansion.physicalUnionModes
            nextRaw.sourcePhysicalState)
    targetPotential - nextSourcePotential =
      (wholeVorticityEuclideanMass raw.targetPhysicalState -
          finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
            raw.targetPhysicalState) -
        (wholeVorticityEuclideanMass nextRaw.sourcePhysicalState -
          finiteStateVorticityCoefficientEnstrophy nextExpansion.physicalUnionModes
            nextRaw.sourcePhysicalState) := by
  subst expansion
  subst nextExpansion
  cases Subsingleton.elim effect
    (nativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
  cases Subsingleton.elim nextEffect
    (nativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter (stage + 1)))
  have kineticEq : puncturedWholeVorticityKineticMass
        (source.stateAfter stage).1.physical.nextContact.physicalState =
      puncturedWholeVorticityKineticMass
        (source.stateAfter (stage + 1)).1.physical.contact.physicalState := rfl
  have deficitEq :
      (nativeFluidMediumExactOperationalEffectAt source
          (source.stateAfter stage)).effect.standingMaterial.targetRemainingDeficit =
        (nativeFluidMediumExactOperationalEffectAt source
          (source.stateAfter (stage + 1))).effect.standingMaterial.sourceRemainingDeficit := rfl
  dsimp only
  rw [kineticEq, deficitEq]
  ring

/-- Exact successor-coverage criterion.  Once both residuals are the
compiler-generated adjacent occurrences, carrying the current target clock
face into the next source face is equivalent to one and only one physical
statement: the two target complements cover the two successor-source
complements. -/
theorem butterflyConsecutiveGeneratedResidual_nextCovered_iff_complements
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (nextEffect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter (stage + 1)))
    (nextResidual : GeneratedParallelResidualAt
      nextEffect.effect nextEffect.arithmeticMaterial)
    (nextExpansion : source.OperationalResidualExpansionAt
      nextEffect.effect nextResidual)
    (nextExpansionEq : nextExpansion =
      source.generateOperationalResidualExpansionAt
        nextEffect.effect nextResidual) :
    let state := source.stateAfter stage
    let nextState := source.stateAfter (stage + 1)
    let raw := effect.effect.standingMaterial.rawValuedMaterial
    let nextRaw := nextEffect.effect.standingMaterial.rawValuedMaterial
    let targetUnionComplement :=
      wholeVorticityEuclideanMass raw.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.targetPhysicalState
    let nextSourceUnionComplement :=
      wholeVorticityEuclideanMass nextRaw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy nextExpansion.physicalUnionModes
          nextRaw.sourcePhysicalState
    let targetPotential :=
      puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.targetRemainingDeficit +
        targetUnionComplement
    let nextSourcePotential :=
      puncturedWholeVorticityKineticMass
          nextState.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        nextEffect.effect.standingMaterial.sourceRemainingDeficit +
        nextSourceUnionComplement
    nextSourcePotential ≤ targetPotential ↔
      nextSourceUnionComplement ≤ targetUnionComplement := by
  dsimp only
  have rebase :=
    butterflyConsecutiveGeneratedResidual_completeMaterial_rebase
      stage effect residual expansion expansionEq nextEffect nextResidual
        nextExpansion nextExpansionEq
  dsimp only at rebase ⊢
  constructor <;> intro covered <;> linarith

/-- The complete vertical residual law in one mouth.  Its successor
potential is the canonical source potential of the next generated residual,
not an edge-local target shell.  Consequently payment and complement rebase
appear as one exact current-source inequality, ready for the root clock
recursor without a future recurrence premise. -/
theorem butterflyConsecutiveGeneratedResidual_completeClockFactorization
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (nextEffect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter (stage + 1)))
    (nextResidual : GeneratedParallelResidualAt
      nextEffect.effect nextEffect.arithmeticMaterial)
    (nextExpansion : source.OperationalResidualExpansionAt
      nextEffect.effect nextResidual)
    (nextExpansionEq : nextExpansion =
      source.generateOperationalResidualExpansionAt
        nextEffect.effect nextResidual) :
    let state := source.stateAfter stage
    let nextState := source.stateAfter (stage + 1)
    let raw := effect.effect.standingMaterial.rawValuedMaterial
    let nextRaw := nextEffect.effect.standingMaterial.rawValuedMaterial
    let sourceUnionComplement :=
      wholeVorticityEuclideanMass raw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.sourcePhysicalState
    let targetUnionComplement :=
      wholeVorticityEuclideanMass raw.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.targetPhysicalState
    let nextSourceUnionComplement :=
      wholeVorticityEuclideanMass nextRaw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy nextExpansion.physicalUnionModes
          nextRaw.sourcePhysicalState
    let sourcePotential :=
      puncturedWholeVorticityKineticMass
          state.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        effect.effect.standingMaterial.sourceRemainingDeficit +
        sourceUnionComplement
    let nextSourcePotential :=
      puncturedWholeVorticityKineticMass
          nextState.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) +
        nextEffect.effect.standingMaterial.sourceRemainingDeficit +
        nextSourceUnionComplement
    0 ≤ sourcePotential ∧ 0 ≤ nextSourcePotential ∧
      (source.clockAt state + nextSourcePotential ≤ sourcePotential ↔
        source.clockAt state + nextSourceUnionComplement ≤
          wholePrefixVorticityMass state.1.physical.nextContact.time
              state.1.physical.nextReceipt.stateLimit +
            source.operationalResidualExpansionDebitAt
              effect.effect residual expansion +
            targetUnionComplement) := by
  dsimp only
  have currentFactor :=
    butterflyGeneratedResidual_completeMaterial_clockFactorization
      stage effect residual expansion
  have nextFactor :=
    butterflyGeneratedResidual_completeMaterial_clockFactorization
      (stage + 1) nextEffect nextResidual nextExpansion
  have currentCoboundary :=
    butterflyGeneratedResidual_completeMaterial_coboundary
      stage effect residual expansion
  have rebase :=
    butterflyConsecutiveGeneratedResidual_completeMaterial_rebase
      stage effect residual expansion expansionEq nextEffect nextResidual
        nextExpansion nextExpansionEq
  dsimp only at currentFactor nextFactor currentCoboundary rebase ⊢
  refine ⟨currentFactor.1, nextFactor.1, ?_⟩
  constructor <;> intro payment <;> linarith

/-- Finite renewal normal form of the complete residual law.  Expanding the
two complement rows and the exact positive-part valuations cancels every
current target term.  The vertical source obligation is therefore a single
comparison between the fresh-face masses already present at the two
adjacent source occurrences. -/
theorem butterflyConsecutiveGeneratedResidual_completeDebit_iff_freshMassRenewal
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (nextEffect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter (stage + 1)))
    (nextResidual : GeneratedParallelResidualAt
      nextEffect.effect nextEffect.arithmeticMaterial)
    (nextExpansion : source.OperationalResidualExpansionAt
      nextEffect.effect nextResidual)
    (nextExpansionEq : nextExpansion =
      source.generateOperationalResidualExpansionAt
        nextEffect.effect nextResidual) :
    let state := source.stateAfter stage
    let raw := effect.effect.standingMaterial.rawValuedMaterial
    let nextRaw := nextEffect.effect.standingMaterial.rawValuedMaterial
    let currentTargetComplement :=
      wholeVorticityEuclideanMass raw.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
          raw.targetPhysicalState
    let nextSourceComplement :=
      wholeVorticityEuclideanMass nextRaw.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy nextExpansion.physicalUnionModes
          nextRaw.sourcePhysicalState
    (source.clockAt state + nextSourceComplement ≤
        wholePrefixVorticityMass state.1.physical.nextContact.time
            state.1.physical.nextReceipt.stateLimit +
          source.operationalResidualExpansionDebitAt
            effect.effect residual expansion +
          currentTargetComplement) ↔
      (source.clockAt state +
          finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
            raw.sourcePhysicalState ≤
        wholePrefixVorticityMass state.1.physical.nextContact.time
            state.1.physical.nextReceipt.stateLimit +
          finiteStateVorticityCoefficientEnstrophy nextExpansion.physicalUnionModes
            nextRaw.sourcePhysicalState) := by
  dsimp only
  have expansionDebitEq :
      source.operationalResidualExpansionDebitAt
          effect.effect residual expansion =
        expansion.unionNetEnstrophyDebit := rfl
  have targetSourceEq :
      effect.effect.standingMaterial.rawValuedMaterial.targetPhysicalState =
        nextEffect.effect.standingMaterial.rawValuedMaterial.sourcePhysicalState := by
    subst expansion
    subst nextExpansion
    cases Subsingleton.elim effect
      (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter stage))
    cases Subsingleton.elim nextEffect
      (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter (stage + 1)))
    rw [(nativeFluidMediumExactOperationalEffectAt source
          (source.stateAfter stage)).effect.standingMaterial.rawValuedMaterial.targetPhysicalState_eq,
      (nativeFluidMediumExactOperationalEffectAt source
          (source.stateAfter (stage + 1))).effect.standingMaterial.rawValuedMaterial.sourcePhysicalState_eq]
    rfl
  rw [expansionDebitEq]
  unfold NativeRestartStandingActionResidualExpansionAt.unionNetEnstrophyDebit
  rw [targetSourceEq]
  constructor <;> intro payment <;> linarith

/-- The low-mass source obligation is indexed by the root outcome already
generated on this occurrence.  Exact payment carries no extra scalar: that
constructor is physically impossible below the cap.  Only an actual
residual or obstruction must supply the current-edge physical debit. -/
noncomputable def ButterflyLowMassOutcomeCurrentDebitAt
    (stage : Nat) : Prop :=
  match nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) with
  | .exactPayment .. => True
  | .generatedResidual .. => ButterflyLowMassCappedCurrentDebitAt stage
  | .obstruction .. => ButterflyLowMassCappedCurrentDebitAt stage

/-- Consume the outcome-indexed low-mass debit.  The framework resolves the
total root disposition; the source scalar is inspected only in the two
actual residual constructors. -/
noncomputable def cappedMassKineticRootSettlement_of_lowMassOutcomeDebit
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (debit : ButterflyLowMassOutcomeCurrentDebitAt stage) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  unfold ButterflyLowMassOutcomeCurrentDebitAt at debit
  rw [outcomeEq] at debit
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact False.elim (lowMass_rootExact_isEmpty
        stage lowMass effect commutes)
  | generatedResidual =>
      exact .generatedResidual
        (sourceGeneratedRootClockAdvance_of_potential_domination debit)
  | obstruction =>
      exact .obstructionAlternative
        (sourceGeneratedRootClockAdvance_of_potential_domination debit)

/-- The low-mass debit is consumed only on the actual residual or
obstruction constructor; exact payment has already been ruled out by the
same physical current. -/
noncomputable def cappedMassKineticRootSettlement_of_lowMassDebit
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (debit : ButterflyLowMassCappedCurrentDebitAt stage) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  let advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) :=
    sourceGeneratedRootClockAdvance_of_potential_domination debit
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact False.elim (lowMass_rootExact_isEmpty
        stage lowMass effect commutes)
  | generatedResidual => exact .generatedResidual advance
  | obstruction => exact .obstructionAlternative advance

def TargetMassTwoAt (state : source.State) : Prop :=
  2 ≤ wholeVorticityEuclideanMass
    state.1.physical.nextContact.physicalState

theorem initialTargetMassTwo : TargetMassTwoAt source.initial := by
  let wave := plusSideband
  have waveMem : wave ∈ stackedSidebandModes := by
    simp [wave, stackedSidebandModes]
  have reserve := (stackedShortContact_sourcePatch.2.2 wave waveMem).1
  have seedMass : complexCoordinateAmplitudeSq (stackedSeedState wave) =
      121 / 8 := by
    have seedReserve := stackedSeedState_sideband_reserve_eq wave waveMem
    unfold sourceReserveAt at seedReserve
    rw [complexCoordinateRealInner_self] at seedReserve
    simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      using seedReserve
  have cauchy := complexCoordinateRealInner_sq_le
    (stackedSeedState wave)
    (stackedShortCurrent.contact.physicalState wave)
  unfold sourceReserveAt at reserve
  rw [seedMass] at cauchy
  have sourceRowMass : 2 < complexCoordinateAmplitudeSq
      (stackedShortCurrent.contact.physicalState wave) := by
    nlinarith
  have targetRowMass : 2 < complexCoordinateAmplitudeSq
      (stackedShortCurrent.nextContact.physicalState wave) :=
    sourceRowMass.trans
      (stackedSideband_nextContact_amplitudeSq_gt wave waveMem)
  have rowLeWhole : complexCoordinateAmplitudeSq
        (stackedShortCurrent.nextContact.physicalState wave) ≤
      wholeVorticityEuclideanMass
        stackedShortCurrent.nextContact.physicalState := by
    have finiteLe := finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      ({wave} : Finset IntegerWavevector)
      stackedShortCurrent.nextContact.physicalState
    simpa [finiteStateVorticityCoefficientEnstrophy] using finiteLe
  change 2 ≤ wholeVorticityEuclideanMass
    stackedShortCurrent.nextContact.physicalState
  exact (targetRowMass.trans_le rowLeWhole).le

def kineticBarrierRootExactAdvance
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (kineticBarrierClockState (source.stateAfter stage))
      (kineticBarrierClockState (source.stateAfter (stage + 1))) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  have paid := standingActionRootExact_paymentIncrement_eq_one effect commutes
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel + 1 := by
    change
      ((source.stateAfter stage).1.standing.next).anchorLevel = _
    rw [cellStanding_anchorLevel_next, paid]
  have anchorCurrent : state.1.standing.anchorLevel =
      (runCellStanding stackedShortCurrent stage).anchorLevel := by
    have currentEq : (source.stateAfter stage).1 =
        runRuntime stackedShortCurrent stage := by
      exact standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    dsimp only [state]
    rw [currentEq]
    rfl
  have clockLe := standingActionRootExact_clock_le_barrierModel
    stackedInitialActionMaterialInstruction stage effect commutes
  change source.clockAt state ≤
    standingActionBarrierModel butterflyGainViscosity
      (runCellStanding stackedShortCurrent stage).anchorLevel at clockLe
  rw [← anchorCurrent] at clockLe
  change state.1.physical.nextContact.time.1 ≤
    standingActionBarrierModel butterflyGainViscosity
      state.1.standing.anchorLevel at clockLe
  have kineticLe := nextContact_kineticMass_le state.1.physical
  have tailStep := standingActionBarrierTail_step butterflyGainViscosity
    state.1.standing.anchorLevel
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change source.clockAt state + kineticBarrierPotential nextState ≤
    kineticBarrierPotential state
  unfold kineticBarrierPotential
  rw [tailStep, anchorNext]
  have denominatorPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have kineticScaled :
      puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState /
          (2 * butterflyGainViscosity.coeff) ≤
        puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) :=
    (div_le_div_iff_of_pos_right denominatorPos).2 kineticLe
  have nextKineticEq :
      puncturedWholeVorticityKineticMass
          nextState.1.physical.contact.physicalState =
        puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState := by rfl
  rw [nextKineticEq]
  change
    state.1.physical.nextContact.time.1 +
          (standingActionBarrierTail butterflyGainViscosity
              (state.1.standing.anchorLevel + 1) +
            puncturedWholeVorticityKineticMass
                state.1.physical.nextContact.physicalState /
              (2 * butterflyGainViscosity.coeff)) ≤
      standingActionBarrierModel butterflyGainViscosity
          state.1.standing.anchorLevel +
        standingActionBarrierTail butterflyGainViscosity
            (state.1.standing.anchorLevel + 1) +
          puncturedWholeVorticityKineticMass
              state.1.physical.contact.physicalState /
            (2 * butterflyGainViscosity.coeff)
  linarith

def kineticBarrierRootResidualAdvance
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (kineticBarrierClockState (source.stateAfter stage))
      (kineticBarrierClockState (source.stateAfter (stage + 1))) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  have notPaid := standingActionRootResidual_paymentIncrement_ne_one
    effect residual
  have incrementLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_paymentIncrement_le_one
      state.1.standing
  have incrementZero : state.1.standing.paymentIncrement = 0 := by
    dsimp only [source, state] at notPaid incrementLe ⊢
    omega
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel := by
    change
      ((source.stateAfter stage).1.standing.next).anchorLevel = _
    rw [cellStanding_anchorLevel_next, incrementZero, Nat.add_zero]
  let massPrefix : Real := wholePrefixVorticityMass
    state.1.physical.nextContact.time
    state.1.physical.nextReceipt.stateLimit
  have rectangle :=
    state.1.physical.nextContact_terminalMass_sub_one_mul_time_le_prefix
  have clockLePrefix : state.1.physical.nextContact.time.1 ≤ massPrefix := by
    have massFactor : 1 ≤
        wholeVorticityEuclideanMass
            state.1.physical.nextContact.physicalState - 1 := by
      dsimp only [TargetMassTwoAt] at targetMass
      linarith
    have clockScale : state.1.physical.nextContact.time.1 ≤
        state.1.physical.nextContact.time.1 *
          (wholeVorticityEuclideanMass
            state.1.physical.nextContact.physicalState - 1) := by
      calc
        state.1.physical.nextContact.time.1 =
            state.1.physical.nextContact.time.1 * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left massFactor
          state.1.physical.nextContact.time_pos.le
    exact clockScale.trans rectangle
  have kineticDissipation := nextContact_kineticDissipation_le
    state.1.physical
  have coefficientPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  have prefixLeKineticDrop : massPrefix ≤
      (puncturedWholeVorticityKineticMass
          state.1.physical.contact.physicalState -
        puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState) /
        (2 * butterflyGainViscosity.coeff) := by
    apply (le_div_iff₀ coefficientPos).2
    dsimp only [massPrefix]
    linarith
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change source.clockAt state + kineticBarrierPotential nextState ≤
    kineticBarrierPotential state
  unfold kineticBarrierPotential
  rw [anchorNext]
  have clockLeDrop := clockLePrefix.trans prefixLeKineticDrop
  have dropSplit :
      (puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState) /
          (2 * butterflyGainViscosity.coeff) =
        puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) -
        puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState /
          (2 * butterflyGainViscosity.coeff) := by ring
  rw [dropSplit] at clockLeDrop
  have nextKineticEq :
      puncturedWholeVorticityKineticMass
          nextState.1.physical.contact.physicalState =
        puncturedWholeVorticityKineticMass
          state.1.physical.nextContact.physicalState := by rfl
  rw [nextKineticEq]
  change
    state.1.physical.nextContact.time.1 +
          (standingActionBarrierTail butterflyGainViscosity
              state.1.standing.anchorLevel +
            puncturedWholeVorticityKineticMass
                state.1.physical.nextContact.physicalState /
              (2 * butterflyGainViscosity.coeff)) ≤
      standingActionBarrierTail butterflyGainViscosity
          state.1.standing.anchorLevel +
        puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff)
  linarith

/-- A retained-standing residual whose actual target mass is still at least
two can spend the kinetic account already installed in the incoming prepaid
face.  The transition drops the unused moving/reset accounts and emits the
pure kinetic-barrier face for the compiler-owned successor. -/
def standingActionMovingKinetic_to_kineticBarrier_residualAdvance
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (standingActionMovingKineticClockState stage)
      (kineticBarrierClockState (source.stateAfter (stage + 1))) := by
  have kineticAdvance :=
    kineticBarrierRootResidualAdvance stage effect residual targetMass
  have kineticDomination :
      source.clockAt (source.stateAfter stage) +
          kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
        kineticBarrierPotential (source.stateAfter stage) := by
    have settlement := kineticAdvance.settlement
    have wasteNonneg := kineticAdvance.waste_nonneg
    change
      kineticBarrierPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          kineticBarrierPotential (source.stateAfter (stage + 1)) +
            kineticAdvance.waste at settlement
    linarith
  have currentKineticLePrepaid :
      kineticBarrierPotential (source.stateAfter stage) ≤
        standingActionMovingKineticClockPotential stage := by
    unfold kineticBarrierPotential
      standingActionMovingKineticClockPotential
      standingActionMovingClockPotential
    have resetNonneg := standingActionMovingResetReserve_nonneg
      (source.stateAfter stage).1.standing.anchorLevel
    have weightedNonneg : 0 ≤
        standingActionMovingResidualWeight
            (source.stateAfter stage).1.standing.anchorLevel *
          standingActionMovingResidualPotential stage :=
      mul_nonneg
        (standingActionMovingResidualWeight_pos _).le
        (standingActionMovingResidualPotential_nonneg stage)
    linarith
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  exact kineticDomination.trans currentKineticLePrepaid

/-- Total root outcome on an incoming prepaid face when the actual residual
target retains two units of whole mass.  Exact payment stays in prepaid mode;
both residual constructors consume the installed kinetic account and emit a
pure kinetic-barrier successor face. -/
noncomputable def standingActionMovingKineticRootSettlement_of_targetMass
    (stage : Nat)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    Σ nextClock : SourceGeneratedRootClockStateAt source
        (source.successor (source.stateAfter stage)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (standingActionMovingKineticClockState stage) nextClock
        (nativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter stage)) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact ⟨standingActionMovingKineticClockState (stage + 1),
        .exactPayment
          (standingActionMovingKineticClockRootExactAdvance
            stage effect commutes)⟩
  | generatedResidual effect residual expansion expansionEq payment =>
      exact ⟨kineticBarrierClockState (source.stateAfter (stage + 1)),
        .generatedResidual
          (standingActionMovingKinetic_to_kineticBarrier_residualAdvance
            stage effect residual targetMass)⟩
  | obstruction obstruction demand =>
      exact ⟨kineticBarrierClockState (source.stateAfter (stage + 1)),
        .obstructionAlternative
          (standingActionMovingKinetic_to_kineticBarrier_residualAdvance
            stage obstruction.effect obstruction.residual targetMass)⟩

noncomputable def kineticBarrierRootSettlement
    (stage : Nat)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      (kineticBarrierClockState (source.stateAfter stage))
      (kineticBarrierClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  generalize outcomeEq : nativeFluidMediumRootOperationalOutcomeAt source
    (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact .exactPayment
        (kineticBarrierRootExactAdvance stage effect commutes)
  | generatedResidual effect residual expansion expansionEq payment =>
      exact .generatedResidual
        (kineticBarrierRootResidualAdvance stage effect residual targetMass)
  | obstruction obstruction demand =>
      exact .obstructionAlternative
        (kineticBarrierRootResidualAdvance stage obstruction.effect
          obstruction.residual targetMass)

/-! ## Complete credit on the kinetic-barrier base -/

/-- The kinetic/barrier account with the finite root bank retained.  Unlike
the compatibility action-kinetic face, this base has no endpoint residual;
on a root residual its barrier row is definitionally unchanged and the
complete expansion account supplies the entire additional coboundary. -/
def butterflyKineticBarrierBankClockState
    (stage : Nat) (bank : Real) (bankNonneg : 0 ≤ bank) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) where
  potential := kineticBarrierPotential (source.stateAfter stage) + bank
  potential_nonneg := add_nonneg
    (kineticBarrierPotential_nonneg (source.stateAfter stage)) bankNonneg

def butterflyCompleteCreditClockState
    {state : source.State}
    (instruction : ButterflyCreditBearingClockInstructionAt state) :
    SourceGeneratedRootClockStateAt source state where
  potential := kineticBarrierPotential state + instruction.bank
  potential_nonneg := add_nonneg
    (kineticBarrierPotential_nonneg state) instruction.bank_nonneg

/-- Capitalize the waste of a kinetic-barrier advance into the successor
bank.  This is the exact analogue of the earlier compatibility lift, now on
the base that commutes with the complete residual material. -/
def butterflyKineticBarrierAdvance_capitalizeBank
    (stage : Nat)
    (bank : Real)
    (bankNonneg : 0 ≤ bank)
    (advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (kineticBarrierClockState (source.stateAfter stage))
      (kineticBarrierClockState (source.stateAfter (stage + 1)))) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (butterflyKineticBarrierBankClockState stage bank bankNonneg)
        (butterflyKineticBarrierBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let nextBank : Real := bank + advance.waste
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg bankNonneg advance.waste_nonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := advance.settlement
        change
          kineticBarrierPotential (source.stateAfter stage) =
            source.clockAt (source.stateAfter stage) +
              kineticBarrierPotential (source.stateAfter (stage + 1)) +
                advance.waste at settlement
        change
          kineticBarrierPotential (source.stateAfter stage) + bank =
            source.clockAt (source.stateAfter stage) +
              (kineticBarrierPotential (source.stateAfter (stage + 1)) +
                nextBank) + 0
        dsimp only [nextBank]
        linarith }

/-- Low-target complete-material advance.  Every part of the current
surplus is retained in the successor bank, together with the exact target
account of the same residual expansion. -/
def butterflyKineticBarrierCompleteAdvance
    (stage : Nat)
    (bank : Real)
    (bankNonneg : 0 ≤ bank)
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (domination :
      source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        kineticBarrierPotential (source.stateAfter stage) + bank) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (butterflyKineticBarrierBankClockState stage bank bankNonneg)
        (butterflyKineticBarrierBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let targetAccount := butterflyGeneratedResidualTargetAccount
    stage effect residual expansion
  let surplus :=
    kineticBarrierPotential (source.stateAfter stage) + bank -
      source.clockAt (source.stateAfter stage) -
      (kineticBarrierPotential (source.stateAfter (stage + 1)) +
        targetAccount)
  have targetNonneg : 0 ≤ targetAccount :=
    butterflyGeneratedResidualTargetAccount_nonneg
      stage effect residual expansion
  have surplusNonneg : 0 ≤ surplus := by
    dsimp only [surplus, targetAccount]
    linarith
  let nextBank := targetAccount + surplus
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg targetNonneg surplusNonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        change
          kineticBarrierPotential (source.stateAfter stage) + bank =
            source.clockAt (source.stateAfter stage) +
              (kineticBarrierPotential (source.stateAfter (stage + 1)) +
                nextBank) + 0
        dsimp only [nextBank, surplus, targetAccount]
        ring }

/-- Only a low-target residual needs the complete bank inequality.  Exact
incidence and every residual with target mass at least two are paid by the
kinetic/barrier base itself. -/
def ButterflyCompleteCreditOutcomePaymentAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage)) :
    NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) → Type
  | .exactPayment .. => PUnit
  | .generatedResidual effect residual expansion .. =>
      PLift (TargetMassTwoAt (source.stateAfter stage)) ⊕
        PLift (source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount
                stage effect residual expansion) ≤
          kineticBarrierPotential (source.stateAfter stage) +
            instruction.bank)
  | .obstruction obstruction _demand =>
      PLift (TargetMassTwoAt (source.stateAfter stage)) ⊕
        PLift (source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount stage
                obstruction.effect obstruction.residual
                  obstruction.expansion) ≤
          kineticBarrierPotential (source.stateAfter stage) +
            instruction.bank)

def butterflyCompleteCreditOutcomePayment_of_targetMass
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage))
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    ButterflyCompleteCreditOutcomePaymentAt
      stage instruction outcome := by
  cases outcome with
  | exactPayment => exact PUnit.unit
  | generatedResidual => exact Sum.inl ⟨targetMass⟩
  | obstruction => exact Sum.inl ⟨targetMass⟩

theorem butterflyCompleteCreditInitialTargetMass :
    TargetMassTwoAt (source.stateAfter 0) := by
  unfold TargetMassTwoAt
  change (2 : Real) ≤ wholeVorticityEuclideanMass
    stackedShortCurrent.nextContact.physicalState
  exact stackedShortCurrent_nextContact_wholeMass_gt_two.le

def butterflyCompleteCreditInitialPayment :
    ButterflyCompleteCreditOutcomePaymentAt 0
      butterflyCreditBearingInitialInstruction
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter 0)) :=
  butterflyCompleteCreditOutcomePayment_of_targetMass 0
    butterflyCreditBearingInitialInstruction _
      butterflyCompleteCreditInitialTargetMass

/-- Exact low-target mouth on the complete credit base.  The action endpoint
residual has disappeared: after the kinetic/barrier base and full expansion
are both retained, the sole quantitative row is prefix mass plus union debit
plus incoming credit relative to the expansion's source account. -/
theorem butterflyKineticBarrierCompletePayment_iff
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    (source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        kineticBarrierPotential (source.stateAfter stage) +
          instruction.bank) ↔
      source.clockAt (source.stateAfter stage) ≤
        wholePrefixVorticityMass
            (source.stateAfter stage).1.physical.nextContact.time
            (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
          source.operationalResidualExpansionDebitAt
            effect.effect residual expansion +
          (instruction.bank -
            butterflyGeneratedResidualSourceAccount
              stage effect residual expansion) := by
  let state := source.stateAfter stage
  let nextState := source.stateAfter (stage + 1)
  have notPaid := standingActionRootResidual_paymentIncrement_ne_one
    effect residual
  have incrementLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_paymentIncrement_le_one
      state.1.standing
  have incrementZero : state.1.standing.paymentIncrement = 0 := by
    dsimp only [state, source, stackedStandingActionMediumSource]
      at notPaid incrementLe ⊢
    omega
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel := by
    dsimp only [nextState, state]
    change ((source.stateAfter stage).1.standing.next).anchorLevel = _
    rw [cellStanding_anchorLevel_next, incrementZero, Nat.add_zero]
  have complete := butterflyGeneratedResidual_completeMaterial_coboundary
    stage effect residual expansion
  have nextKineticEq :
      puncturedWholeVorticityKineticMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState =
        puncturedWholeVorticityKineticMass
          (source.stateAfter stage).1.physical.nextContact.physicalState := by
    rfl
  have totalCoboundary :
      (kineticBarrierPotential (source.stateAfter stage) +
          instruction.bank) -
        (kineticBarrierPotential (source.stateAfter (stage + 1)) +
          butterflyGeneratedResidualTargetAccount
            stage effect residual expansion) =
      wholePrefixVorticityMass
          (source.stateAfter stage).1.physical.nextContact.time
          (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
        source.operationalResidualExpansionDebitAt
          effect.effect residual expansion +
        (instruction.bank -
          butterflyGeneratedResidualSourceAccount
            stage effect residual expansion) := by
    unfold kineticBarrierPotential
    dsimp only [state, nextState] at anchorNext
    rw [anchorNext, nextKineticEq]
    dsimp only [butterflyGeneratedResidualSourceAccount,
      butterflyGeneratedResidualTargetAccount] at complete ⊢
    linarith
  constructor <;> intro payment <;> linarith

def butterflyCompleteCreditNextInstruction
    (stage : Nat)
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (nextBank : { value : Real // 0 ≤ value }) :
    ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)) where
  stage := stage + 1
  state_eq := rfl
  bank := nextBank.1
  bank_nonneg := nextBank.2
  predecessor? := some ⟨stage, outcome, ⟨disposition, rfl⟩⟩

/-- Total root settlement once the low-target complete-credit mouth is
available.  The action disposition is retained verbatim in the successor
instruction, while the root outcome alone decides which already-generated
physical account pays. -/
noncomputable def butterflyCompleteCreditTransition_of_payment
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (currentPayment : ButterflyCompleteCreditOutcomePaymentAt
      stage instruction outcome) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCompleteCreditClockState instruction)
        (butterflyCompleteCreditClockState nextInstruction) outcome := by
  cases outcome with
  | exactPayment effect rooted commutes =>
      let advance := kineticBarrierRootExactAdvance stage effect commutes
      rcases butterflyKineticBarrierAdvance_capitalizeBank
        stage instruction.bank instruction.bank_nonneg advance with
        ⟨nextBank, nextAdvance⟩
      let nextInstruction := butterflyCompleteCreditNextInstruction
        stage disposition nextBank
      refine ⟨nextInstruction, ?_⟩
      simpa only [butterflyCompleteCreditClockState,
        butterflyKineticBarrierBankClockState,
        NativeFluidMediumSource.stateAfter_succ, nextInstruction,
        butterflyCompleteCreditNextInstruction,
        source, stackedStandingActionMediumSource] using
        (SourceGeneratedRootClockSettlementAt.exactPayment
          (effect := effect) (rooted := rooted) (commutes := commutes)
          nextAdvance)
  | generatedResidual effect residual expansion expansionEq payment =>
      rcases currentPayment with targetMass | domination
      · let advance := kineticBarrierRootResidualAdvance
          stage effect residual targetMass.down
        rcases butterflyKineticBarrierAdvance_capitalizeBank
          stage instruction.bank instruction.bank_nonneg advance with
          ⟨nextBank, nextAdvance⟩
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage disposition nextBank
        refine ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.generatedResidual
            (effect := effect) (residual := residual)
            (expansion := expansion) (expansion_eq := expansionEq)
            (payment := payment) nextAdvance)
      · rcases butterflyKineticBarrierCompleteAdvance
          stage instruction.bank instruction.bank_nonneg effect residual
            expansion domination.down with ⟨nextBank, nextAdvance⟩
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage disposition nextBank
        refine ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.generatedResidual
            (effect := effect) (residual := residual)
            (expansion := expansion) (expansion_eq := expansionEq)
            (payment := payment) nextAdvance)
  | obstruction obstruction demand =>
      rcases currentPayment with targetMass | domination
      · let advance := kineticBarrierRootResidualAdvance stage
          obstruction.effect obstruction.residual targetMass.down
        rcases butterflyKineticBarrierAdvance_capitalizeBank
          stage instruction.bank instruction.bank_nonneg advance with
          ⟨nextBank, nextAdvance⟩
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage disposition nextBank
        refine ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.obstructionAlternative
            (obstruction := obstruction) (demand := demand) nextAdvance)
      · rcases butterflyKineticBarrierCompleteAdvance stage
          instruction.bank instruction.bank_nonneg obstruction.effect
            obstruction.residual obstruction.expansion domination.down with
          ⟨nextBank, nextAdvance⟩
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage disposition nextBank
        refine ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.obstructionAlternative
            (obstruction := obstruction) (demand := demand) nextAdvance)

noncomputable def butterflyCompleteCreditInitialTransition :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter 1),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter 0)
        (butterflyCompleteCreditClockState
          butterflyCreditBearingInitialInstruction)
        (butterflyCompleteCreditClockState nextInstruction)
        (nativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter 0)) :=
  butterflyCompleteCreditTransition_of_payment 0
    butterflyCreditBearingInitialInstruction
    (sourceGeneratedStandingActionRunClockDisposition
      stackedInitialActionMaterialInstruction 0)
    butterflyCompleteCreditInitialPayment

/-- Correct total transition.  Its negative constructor can occur only on
a residual/obstruction whose actual target mass is below two and whose
complete prefix/union/credit payment fails. -/
def ButterflyCompleteCreditTransitionResultAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (_disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (butterflyCompleteCreditClockState nextInstruction) outcome) ⊕
    PLift (IsEmpty (ButterflyCompleteCreditOutcomePaymentAt
      stage instruction outcome))

noncomputable def butterflyCompleteCreditTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyCompleteCreditTransitionResultAt
      stage instruction disposition := by
  by_cases available : Nonempty (ButterflyCompleteCreditOutcomePaymentAt
      stage instruction outcome)
  · exact Sum.inl
      (butterflyCompleteCreditTransition_of_payment
        stage instruction disposition (Classical.choice available))
  · exact Sum.inr ⟨⟨fun payment => available ⟨payment⟩⟩⟩

/-- Exact physical content of a failed complete-credit transition.  There is
no failure constructor on an exact root payment; on either residual outcome
failure means both that the actual target fell below two and that the full
prefix/union/credit domination failed. -/
def ButterflyCompleteCreditLowTargetShortfallAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage)) :
    NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) → Prop
  | .exactPayment .. => False
  | .generatedResidual effect residual expansion .. =>
      ¬ TargetMassTwoAt (source.stateAfter stage) ∧
      ¬ (source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount
                stage effect residual expansion) ≤
          kineticBarrierPotential (source.stateAfter stage) +
            instruction.bank)
  | .obstruction obstruction _demand =>
      ¬ TargetMassTwoAt (source.stateAfter stage) ∧
      ¬ (source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount stage
                obstruction.effect obstruction.residual
                  obstruction.expansion) ≤
          kineticBarrierPotential (source.stateAfter stage) +
            instruction.bank)

theorem butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)) :
    IsEmpty (ButterflyCompleteCreditOutcomePaymentAt
        stage instruction outcome) ↔
      ButterflyCompleteCreditLowTargetShortfallAt
        stage instruction outcome := by
  cases outcome with
  | exactPayment effect rooted commutes =>
      constructor
      · intro empty
        exact empty.false PUnit.unit
      · intro impossible
        exact False.elim impossible
  | generatedResidual effect residual expansion expansionEq payment =>
      constructor
      · intro empty
        constructor
        · intro targetMass
          exact empty.false (Sum.inl ⟨targetMass⟩)
        · intro domination
          exact empty.false (Sum.inr ⟨domination⟩)
      · rintro ⟨notTargetMass, notDomination⟩
        constructor
        intro payment
        cases payment with
        | inl targetMass => exact notTargetMass targetMass.down
        | inr domination => exact notDomination domination.down
  | obstruction obstruction demand =>
      constructor
      · intro empty
        constructor
        · intro targetMass
          exact empty.false (Sum.inl ⟨targetMass⟩)
        · intro domination
          exact empty.false (Sum.inr ⟨domination⟩)
      · rintro ⟨notTargetMass, notDomination⟩
        constructor
        intro payment
        cases payment with
        | inl targetMass => exact notTargetMass targetMass.down
        | inr domination => exact notDomination domination.down

/-! ## Low-mass capped alternative on the same complete-credit current -/

def ButterflyCompleteCreditCappedCoverageAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage)) : Prop :=
  cappedMassKineticClockPotential (source.stateAfter stage) ≤
    (butterflyCompleteCreditClockState instruction).potential

theorem butterflyCompleteCreditCappedCoverage_iff
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyCompleteCreditCappedCoverageAt stage instruction ↔
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState ≤
        standingActionBarrierTail butterflyGainViscosity
            (source.stateAfter stage).1.standing.anchorLevel +
          instruction.bank := by
  unfold ButterflyCompleteCreditCappedCoverageAt
    cappedMassKineticClockPotential butterflyCompleteCreditClockState
    kineticBarrierPotential
  rw [min_eq_left lowMass.le]
  constructor <;> intro coverage <;> linarith

/-- The low-mass capped debit is already a valid alternative settlement from
the complete-credit current whenever that current covers the capped source
face.  The generated advance retains the exact difference as its waste. -/
def butterflyCompleteCredit_to_cappedMassAdvance
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (debit : ButterflyLowMassCappedCurrentDebitAt stage)
    (coverage : ButterflyCompleteCreditCappedCoverageAt
      stage instruction) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) := by
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  exact debit.trans coverage

noncomputable def butterflyCompleteCreditCappedRootSettlement
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (lowMass : wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (debit : ButterflyLowMassCappedCurrentDebitAt stage)
    (coverage : ButterflyCompleteCreditCappedCoverageAt
      stage instruction) :
    SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (cappedMassKineticClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  let advance := butterflyCompleteCredit_to_cappedMassAdvance
    stage instruction debit coverage
  generalize outcomeEq : nativeFluidMediumRootOperationalOutcomeAt source
    (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact False.elim (lowMass_rootExact_isEmpty
        stage lowMass effect commutes)
  | generatedResidual => exact .generatedResidual advance
  | obstruction => exact .obstructionAlternative advance

/-- The capped face with its unused current-side slack retained.  This is
the successor interpretation used by a complete-to-capped switch; the
instruction still stores the full predecessor disposition. -/
def butterflyCappedCreditClockState
    {state : source.State}
    (instruction : ButterflyCreditBearingClockInstructionAt state) :
    SourceGeneratedRootClockStateAt source state where
  potential := cappedMassKineticClockPotential state + instruction.bank
  potential_nonneg := add_nonneg
    (cappedMassKineticClockPotential_nonneg state)
    instruction.bank_nonneg

/-- Spend the current face's complete account on the actual clock and capped
successor.  The exact remainder is retained as bank, including when the
uncredited capped base would fail to pay this edge. -/
private noncomputable def butterflyCurrentToCappedTransition_of_domination
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (covered : source.clockAt (source.stateAfter stage) +
      cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
        currentClock.potential) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        currentClock (butterflyCappedCreditClockState nextInstruction)
        outcome := by
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨currentClock.potential - source.clockAt (source.stateAfter stage) -
        cappedMassKineticClockPotential (source.stateAfter (stage + 1)),
      by linarith⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) currentClock
      (butterflyCappedCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        change currentClock.potential =
          source.clockAt (source.stateAfter stage) +
            (cappedMassKineticClockPotential (source.stateAfter (stage + 1)) +
              nextBank.1) + 0
        dsimp only [nextBank]
        ring }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment => exact .exactPayment advance
  | generatedResidual => exact .generatedResidual advance
  | obstruction => exact .obstructionAlternative advance

/-- The current account can fund the existing kinetic/barrier successor
directly.  The operational residual remains in the physical root and the
complete predecessor disposition, independently of the clock bank. -/
private noncomputable def butterflyCurrentToCompleteTransition_of_domination
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (covered : source.clockAt (source.stateAfter stage) +
      kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
        currentClock.potential) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        currentClock (butterflyCompleteCreditClockState nextInstruction)
        outcome := by
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨currentClock.potential - source.clockAt (source.stateAfter stage) -
        kineticBarrierPotential (source.stateAfter (stage + 1)),
      by linarith⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) currentClock
      (butterflyCompleteCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        change currentClock.potential =
          source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              nextBank.1) + 0
        dsimp only [nextBank]
        ring }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment => exact .exactPayment advance
  | generatedResidual => exact .generatedResidual advance
  | obstruction => exact .obstructionAlternative advance

/-- A complete-credit current that switches to the capped face does not
discard the coverage slack or the capped settlement waste.  Their complete
sum becomes the successor bank, while the predecessor field retains the
same outcome-indexed action disposition. -/
noncomputable def butterflyCompleteCreditToCappedTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (lowMass : wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (debit : ButterflyLowMassCappedCurrentDebitAt stage)
    (coverage : ButterflyCompleteCreditCappedCoverageAt
      stage instruction) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCompleteCreditClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome := by
  let cappedAdvance := butterflyCompleteCredit_to_cappedMassAdvance
    stage instruction debit coverage
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨cappedAdvance.waste, cappedAdvance.waste_nonneg⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (butterflyCappedCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := cappedAdvance.settlement
        change
          (butterflyCompleteCreditClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              cappedMassKineticClockPotential
                (source.stateAfter (stage + 1)) + cappedAdvance.waste
          at settlement
        change
          (butterflyCompleteCreditClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              (cappedMassKineticClockPotential
                  (source.stateAfter (stage + 1)) + nextBank.1) + 0
        simpa only [nextBank, add_zero, add_assoc] using settlement }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact False.elim (lowMass_rootExact_isEmpty
        stage lowMass effect commutes)
  | generatedResidual =>
      exact .generatedResidual retainedAdvance
  | obstruction =>
      exact .obstructionAlternative retainedAdvance

/-- Direct low-mass transition after consuming both complete-material and
capped physical faces.  The two positive constructors already contain the
root settlement and compiler-owned successor instruction.  The negative
constructor retains the proof that complete payment is empty and exposes
only capped-coverage failure or the existing physical-failure row. -/
def ButterflyCompleteCreditLowMassTotalTransitionAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (butterflyCompleteCreditClockState nextInstruction) outcome) ⊕
    ((Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCompleteCreditClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome) ⊕
      (PLift (IsEmpty (ButterflyCompleteCreditOutcomePaymentAt
          stage instruction outcome)) ×
        (PLift (ButterflyLowMassCappedCurrentDebitAt stage ∧
            ¬ ButterflyCompleteCreditCappedCoverageAt stage instruction) ⊕
          PLift (ButterflyLowMassPhysicalFailureAt stage))))

noncomputable def butterflyCompleteCreditLowMassTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (lowMass : wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState < 2)
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyCompleteCreditLowMassTotalTransitionAt
      stage instruction disposition := by
  by_cases complete : Nonempty
      (ButterflyCompleteCreditOutcomePaymentAt stage instruction outcome)
  · exact Sum.inl (butterflyCompleteCreditTransition_of_payment
      stage instruction disposition (Classical.choice complete))
  · by_cases capped : ButterflyLowMassCappedCurrentDebitAt stage
    · by_cases coverage : ButterflyCompleteCreditCappedCoverageAt
          stage instruction
      · exact Sum.inr (Sum.inl
          (butterflyCompleteCreditToCappedTransition
            stage instruction disposition lowMass capped coverage))
      · have emptyPayment : IsEmpty
            (ButterflyCompleteCreditOutcomePaymentAt
              stage instruction outcome) :=
          ⟨fun payment => complete ⟨payment⟩⟩
        exact Sum.inr (Sum.inr
          (⟨emptyPayment⟩, Sum.inl ⟨⟨capped, coverage⟩⟩))
    · have physicalFailure : ButterflyLowMassPhysicalFailureAt stage :=
        (butterflyLowMassCappedCurrentDebit_or_halfCritical_or_clockDeficit
          stage lowMass).resolve_left capped
      have emptyPayment : IsEmpty
          (ButterflyCompleteCreditOutcomePaymentAt
            stage instruction outcome) :=
        ⟨fun payment => complete ⟨payment⟩⟩
      exact Sum.inr (Sum.inr
        (⟨emptyPayment⟩, Sum.inr ⟨physicalFailure⟩))

/-- A coupled credit instruction whose actual target still carries two
units of whole mass never reaches the net-shortfall branch.  The already
installed kinetic/barrier account pays the edge, while the mixed face and
incoming bank are discarded only after they have causally funded this
successor mode. -/
def butterflyCreditBearing_to_kineticBarrier_residualAdvance
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (kineticBarrierClockState (source.stateAfter (stage + 1))) := by
  have kineticAdvance :=
    kineticBarrierRootResidualAdvance stage effect residual targetMass
  have kineticDomination :
      source.clockAt (source.stateAfter stage) +
          kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
        kineticBarrierPotential (source.stateAfter stage) := by
    have settlement := kineticAdvance.settlement
    have wasteNonneg := kineticAdvance.waste_nonneg
    change
      kineticBarrierPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          kineticBarrierPotential (source.stateAfter (stage + 1)) +
            kineticAdvance.waste at settlement
    linarith
  have currentBarrierLeCredit :
      kineticBarrierPotential (source.stateAfter stage) ≤
        (butterflyCreditBearingClockState instruction).potential := by
    have resetNonneg := standingActionDyadicResetReserve_nonneg
      stackedShortCurrent (source.stateAfter stage).2
    have faceNonneg := standingActionFrozenDyadicFacePotential_nonneg
      (source.stateAfter stage).2 (source.stateAfter stage).1
    have kineticEq :
        puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.contact.physicalState /
            (2 * butterflyGainViscosity.coeff) =
          butterflyActionKineticCoefficient *
            puncturedWholeVorticityKineticMass
              (source.stateAfter stage).1.physical.contact.physicalState := by
      unfold butterflyActionKineticCoefficient
      rw [div_eq_mul_inv]
      ring
    change
      kineticBarrierPotential (source.stateAfter stage) ≤
        kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter stage) + instruction.bank
    unfold kineticBarrierPotential kineticCompensatedPotential
      standingActionMixedClockPotential
    rw [kineticEq]
    linarith [instruction.bank_nonneg]
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  exact kineticDomination.trans currentBarrierLeCredit

def butterflyCreditBearingKineticAlternative_of_coupledDisposition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (coupled : match disposition with
      | .settled _ => False
      | .generatedResidualAdvance _ _ => True
      | .obstructionAdvance _ _ => True)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (kineticBarrierClockState (source.stateAfter (stage + 1))) outcome := by
  cases disposition with
  | settled settlement => exact False.elim coupled
  | generatedResidualAdvance actionResidual nextNormalForm =>
      rename_i effect residual expansion expansionEq payment
      exact .generatedResidual
        (butterflyCreditBearing_to_kineticBarrier_residualAdvance
          stage instruction effect residual targetMass)
  | obstructionAdvance actionResidual nextNormalForm =>
      rename_i obstruction demand
      exact .obstructionAlternative
        (butterflyCreditBearing_to_kineticBarrier_residualAdvance
          stage instruction obstruction.effect obstruction.residual
            targetMass)

/-! ## Six-branch rich-current composition -/

/-- The source-side mixed face omitted by the lean kinetic/barrier base.
It is finite and nonnegative on the current actual occurrence. -/
def butterflyRichCurrentPrepaidCredit (stage : Nat) : Real :=
  standingActionDyadicResetReserve stackedShortCurrent
      (source.stateAfter stage).2 +
    standingActionFrozenDyadicFacePotential
      (source.stateAfter stage).2 (source.stateAfter stage).1

theorem butterflyRichCurrentPrepaidCredit_nonneg (stage : Nat) :
    0 ≤ butterflyRichCurrentPrepaidCredit stage := by
  unfold butterflyRichCurrentPrepaidCredit
  exact add_nonneg
    (standingActionDyadicResetReserve_nonneg
      stackedShortCurrent (source.stateAfter stage).2)
    (standingActionFrozenDyadicFacePotential_nonneg
      (source.stateAfter stage).2 (source.stateAfter stage).1)

theorem butterflyCreditBearingClockState_eq_complete_add_prepaid
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage)) :
    (butterflyCreditBearingClockState instruction).potential =
      kineticBarrierPotential (source.stateAfter stage) +
        (instruction.bank + butterflyRichCurrentPrepaidCredit stage) := by
  unfold butterflyCreditBearingClockState kineticCompensatedPotential
    butterflyActionKineticCoefficient kineticBarrierPotential
    standingActionMixedClockPotential butterflyRichCurrentPrepaidCredit
  rw [div_eq_mul_inv]
  ring

/-- Scalar normal form after every existing current-side asset has been
retained.  Compared with the lean complete-material mouth, the richer root
credits exactly the mixed reset/frozen-face account before exposing a source
shortfall. -/
theorem butterflyRichCompletePayment_iff
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual) :
    (source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        (butterflyCreditBearingClockState instruction).potential) ↔
      source.clockAt (source.stateAfter stage) ≤
        wholePrefixVorticityMass
            (source.stateAfter stage).1.physical.nextContact.time
            (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
          source.operationalResidualExpansionDebitAt
            effect.effect residual expansion +
          (instruction.bank + butterflyRichCurrentPrepaidCredit stage -
            butterflyGeneratedResidualSourceAccount
              stage effect residual expansion) := by
  let enrichedInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage) :=
    { stage := instruction.stage
      state_eq := instruction.state_eq
      bank := instruction.bank + butterflyRichCurrentPrepaidCredit stage
      bank_nonneg := add_nonneg instruction.bank_nonneg
        (butterflyRichCurrentPrepaidCredit_nonneg stage)
      predecessor? := instruction.predecessor? }
  have factor := butterflyKineticBarrierCompletePayment_iff
    stage enrichedInstruction effect residual expansion
  have richEq :=
    butterflyCreditBearingClockState_eq_complete_add_prepaid
      stage instruction
  change
    (source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        kineticBarrierPotential (source.stateAfter stage) +
          enrichedInstruction.bank) ↔ _ at factor
  dsimp only [enrichedInstruction] at factor
  rw [richEq]
  exact factor

/-- Complete-material settlement from the richer incoming clock face.  The
mixed/reset face and incoming bank remain on the causal source side; after
the current clock and complete target account are deducted, every unit of
surplus is installed in the compiler-owned successor bank. -/
def butterflyRichToCompleteMaterialAdvance
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (domination :
      source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤
        (butterflyCreditBearingClockState instruction).potential) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (butterflyCreditBearingClockState instruction)
        (butterflyKineticBarrierBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let targetAccount := butterflyGeneratedResidualTargetAccount
    stage effect residual expansion
  let surplus :=
    (butterflyCreditBearingClockState instruction).potential -
      source.clockAt (source.stateAfter stage) -
      (kineticBarrierPotential (source.stateAfter (stage + 1)) +
        targetAccount)
  have targetNonneg : 0 ≤ targetAccount :=
    butterflyGeneratedResidualTargetAccount_nonneg
      stage effect residual expansion
  have surplusNonneg : 0 ≤ surplus := by
    dsimp only [surplus, targetAccount]
    linarith
  let nextBank := targetAccount + surplus
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg targetNonneg surplusNonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        change
          (butterflyCreditBearingClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              (kineticBarrierPotential (source.stateAfter (stage + 1)) +
                nextBank) + 0
        dsimp only [nextBank, surplus, targetAccount]
        ring }

/-- A high-target coupled settlement already lands on the pure
kinetic/barrier face.  Its exact waste is retained as the successor bank,
rather than being discarded at the rich-to-complete mode switch. -/
def butterflyRichKineticAdvance_capitalizeToComplete
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (advance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (kineticBarrierClockState (source.stateAfter (stage + 1)))) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage)
        (butterflyCreditBearingClockState instruction)
        (butterflyKineticBarrierBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let nextBank : Real := advance.waste
  have nextBankNonneg : 0 ≤ nextBank := advance.waste_nonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := advance.settlement
        change
          (butterflyCreditBearingClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              kineticBarrierPotential (source.stateAfter (stage + 1)) +
                advance.waste at settlement
        change
          (butterflyCreditBearingClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              (kineticBarrierPotential (source.stateAfter (stage + 1)) +
                nextBank) + 0
        simpa only [nextBank, add_zero, add_assoc] using settlement }

/-- The authoritative six-branch payment interface on the rich incoming
clock.  Four framework-settled constructors need no scalar.  Only the two
actual coupled constructors read either the already generated high-target
kinetic payment or the complete expansion domination, both indexed by the
same dependent disposition. -/
def ButterflyRichCompleteOutcomePaymentAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  match disposition with
  | .settled _ => PUnit
  | .generatedResidualAdvance (effect := effect) (residual := residual)
      (expansion := expansion) _actionResidual _nextNormalForm =>
      PLift (TargetMassTwoAt (source.stateAfter stage)) ⊕
        PLift (source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount
                stage effect residual expansion) ≤
          (butterflyCreditBearingClockState instruction).potential)
  | .obstructionAdvance (obstruction := obstruction)
      _actionResidual _nextNormalForm =>
      PLift (TargetMassTwoAt (source.stateAfter stage)) ⊕
        PLift (source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              butterflyGeneratedResidualTargetAccount stage
                obstruction.effect obstruction.residual
                  obstruction.expansion) ≤
          (butterflyCreditBearingClockState instruction).potential)

def butterflyRichCompleteOutcomePayment_of_targetMass
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (targetMass : TargetMassTwoAt (source.stateAfter stage)) :
    ButterflyRichCompleteOutcomePaymentAt
      stage instruction disposition := by
  cases disposition with
  | settled => exact PUnit.unit
  | generatedResidualAdvance => exact Sum.inl ⟨targetMass⟩
  | obstructionAdvance => exact Sum.inl ⟨targetMass⟩

/-- Source-table normal form of an unavailable rich/complete payment.  The
settled constructors have no shortfall.  On either coupled constructor the
target is genuinely low and the exact prefix/union/bank/mixed credit row is
strictly insufficient. -/
def ButterflyRichCompleteSourceShortfallAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Prop :=
  match disposition with
  | .settled _ => False
  | .generatedResidualAdvance (effect := effect) (residual := residual)
      (expansion := expansion) _actionResidual _nextNormalForm =>
      ¬ TargetMassTwoAt (source.stateAfter stage) ∧
        ¬ (source.clockAt (source.stateAfter stage) ≤
          wholePrefixVorticityMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
            source.operationalResidualExpansionDebitAt
              effect.effect residual expansion +
            (instruction.bank + butterflyRichCurrentPrepaidCredit stage -
              butterflyGeneratedResidualSourceAccount
                stage effect residual expansion))
  | .obstructionAdvance (obstruction := obstruction)
      _actionResidual _nextNormalForm =>
      ¬ TargetMassTwoAt (source.stateAfter stage) ∧
        ¬ (source.clockAt (source.stateAfter stage) ≤
          wholePrefixVorticityMass
              (source.stateAfter stage).1.physical.nextContact.time
              (source.stateAfter stage).1.physical.nextReceipt.stateLimit +
            source.operationalResidualExpansionDebitAt
              obstruction.effect.effect obstruction.residual
                obstruction.expansion +
            (instruction.bank + butterflyRichCurrentPrepaidCredit stage -
              butterflyGeneratedResidualSourceAccount stage
                obstruction.effect obstruction.residual
                  obstruction.expansion))

theorem butterflyRichCompleteOutcomePayment_isEmpty_iff_sourceShortfall
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    IsEmpty (ButterflyRichCompleteOutcomePaymentAt
        stage instruction disposition) ↔
      ButterflyRichCompleteSourceShortfallAt
        stage instruction disposition := by
  cases disposition with
  | settled settlement =>
      constructor
      · intro empty
        exact empty.false PUnit.unit
      · intro impossible
        exact False.elim impossible
  | generatedResidualAdvance actionResidual nextNormalForm =>
      rename_i effect residual expansion expansionEq residualPayment
      constructor
      · intro empty
        constructor
        · intro targetMass
          exact empty.false (Sum.inl ⟨targetMass⟩)
        · intro sourcePayment
          have domination := (butterflyRichCompletePayment_iff
            stage instruction effect residual expansion).2 sourcePayment
          exact empty.false (Sum.inr ⟨domination⟩)
      · rintro ⟨notTargetMass, notSourcePayment⟩
        constructor
        intro payment
        cases payment with
        | inl targetMass => exact notTargetMass targetMass.down
        | inr domination =>
            exact notSourcePayment ((butterflyRichCompletePayment_iff
              stage instruction effect residual expansion).1
                domination.down)
  | obstructionAdvance actionResidual nextNormalForm =>
      rename_i obstruction demand
      constructor
      · intro empty
        constructor
        · intro targetMass
          exact empty.false (Sum.inl ⟨targetMass⟩)
        · intro sourcePayment
          have domination := (butterflyRichCompletePayment_iff
            stage instruction obstruction.effect obstruction.residual
              obstruction.expansion).2 sourcePayment
          exact empty.false (Sum.inr ⟨domination⟩)
      · rintro ⟨notTargetMass, notSourcePayment⟩
        constructor
        intro payment
        cases payment with
        | inl targetMass => exact notTargetMass targetMass.down
        | inr domination =>
            exact notSourcePayment ((butterflyRichCompletePayment_iff
              stage instruction obstruction.effect obstruction.residual
                obstruction.expansion).1 domination.down)

/-- Positive six-branch transition: settled rows remain on the rich face;
coupled rows emit the lean complete-credit successor. -/
def ButterflyRichCompletePaidTransitionAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (_disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (butterflyCreditBearingClockState nextInstruction) outcome) ⊕
    (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (butterflyCompleteCreditClockState nextInstruction) outcome)

noncomputable def butterflyRichCompleteTransition_of_payment
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (currentPayment : ButterflyRichCompleteOutcomePaymentAt
      stage instruction disposition) :
    ButterflyRichCompletePaidTransitionAt
      stage instruction disposition := by
  cases disposition with
  | settled settlement =>
      have oldPayment : ButterflyCreditBearingCurrentPaymentAt
          stage instruction (.settled settlement) := by trivial
      exact Sum.inl (butterflyCreditBearingTransition_of_payment
        stage instruction (.settled settlement) oldPayment)
  | generatedResidualAdvance actionResidual nextNormalForm =>
      rename_i effect residual expansion expansionEq residualPayment
      rcases currentPayment with targetMass | domination
      · let advance :=
          butterflyCreditBearing_to_kineticBarrier_residualAdvance
            stage instruction effect residual targetMass.down
        rcases butterflyRichKineticAdvance_capitalizeToComplete
          stage instruction advance with ⟨nextBank, nextAdvance⟩
        let generatedDisposition :
            SourceGeneratedStandingActionRunClockDispositionAt
              stackedInitialActionMaterialInstruction stage
                (.generatedResidual effect residual expansion expansionEq
                  residualPayment) :=
          .generatedResidualAdvance actionResidual nextNormalForm
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage generatedDisposition nextBank
        refine Sum.inr ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.generatedResidual
            (effect := effect) (residual := residual)
            (expansion := expansion) (expansion_eq := expansionEq)
            (payment := residualPayment) nextAdvance)
      · rcases butterflyRichToCompleteMaterialAdvance
          stage instruction effect residual expansion domination.down with
          ⟨nextBank, nextAdvance⟩
        let generatedDisposition :
            SourceGeneratedStandingActionRunClockDispositionAt
              stackedInitialActionMaterialInstruction stage
                (.generatedResidual effect residual expansion expansionEq
                  residualPayment) :=
          .generatedResidualAdvance actionResidual nextNormalForm
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage generatedDisposition nextBank
        refine Sum.inr ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.generatedResidual
            (effect := effect) (residual := residual)
            (expansion := expansion) (expansion_eq := expansionEq)
            (payment := residualPayment) nextAdvance)
  | obstructionAdvance actionResidual nextNormalForm =>
      rename_i obstruction demand
      rcases currentPayment with targetMass | domination
      · let advance :=
          butterflyCreditBearing_to_kineticBarrier_residualAdvance
            stage instruction obstruction.effect obstruction.residual
              targetMass.down
        rcases butterflyRichKineticAdvance_capitalizeToComplete
          stage instruction advance with ⟨nextBank, nextAdvance⟩
        let generatedDisposition :
            SourceGeneratedStandingActionRunClockDispositionAt
              stackedInitialActionMaterialInstruction stage
                (.obstruction obstruction demand) :=
          .obstructionAdvance actionResidual nextNormalForm
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage generatedDisposition nextBank
        refine Sum.inr ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.obstructionAlternative
            (obstruction := obstruction) (demand := demand) nextAdvance)
      · rcases butterflyRichToCompleteMaterialAdvance stage instruction
          obstruction.effect obstruction.residual obstruction.expansion
            domination.down with ⟨nextBank, nextAdvance⟩
        let generatedDisposition :
            SourceGeneratedStandingActionRunClockDispositionAt
              stackedInitialActionMaterialInstruction stage
                (.obstruction obstruction demand) :=
          .obstructionAdvance actionResidual nextNormalForm
        let nextInstruction := butterflyCompleteCreditNextInstruction
          stage generatedDisposition nextBank
        refine Sum.inr ⟨nextInstruction, ?_⟩
        simpa only [butterflyCompleteCreditClockState,
          butterflyKineticBarrierBankClockState,
          NativeFluidMediumSource.stateAfter_succ, nextInstruction,
          butterflyCompleteCreditNextInstruction,
          source, stackedStandingActionMediumSource] using
          (SourceGeneratedRootClockSettlementAt.obstructionAlternative
            (obstruction := obstruction) (demand := demand) nextAdvance)

/-- Framework totality after the four immediate settlements and both
complete coupled alternatives are consumed.  Its negative constructor is
therefore an exact dependent shortfall on an actual coupled row. -/
def ButterflyRichCompleteTransitionResultAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  ButterflyRichCompletePaidTransitionAt stage instruction disposition ⊕
    PLift (IsEmpty (ButterflyRichCompleteOutcomePaymentAt
      stage instruction disposition))

noncomputable def butterflyRichCompleteTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyRichCompleteTransitionResultAt
      stage instruction disposition := by
  by_cases available : Nonempty (ButterflyRichCompleteOutcomePaymentAt
      stage instruction disposition)
  · exact Sum.inl (butterflyRichCompleteTransition_of_payment
      stage instruction disposition (Classical.choice available))
  · exact Sum.inr ⟨⟨fun payment => available ⟨payment⟩⟩⟩

/-- Current capped payment generated without a branch premise.  Above the
cap it is the universal capped ledger; below the cap it is precisely the
same-occurrence capped debit. -/
def ButterflyCappedCurrentPaymentAt (stage : Nat) : Type :=
  PLift (2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState) ⊕
    PLift (wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 ∧
      ButterflyLowMassCappedCurrentDebitAt stage)

/-- The negative branch of the capped compiler retains the low-current fact
that generated the half-critical/absorption row.  Dropping this field made
an impossible initial capped failure indistinguishable from a later genuine
low-mass occurrence. -/
structure ButterflyCappedCurrentPhysicalFailureAt (stage : Nat) : Prop where
  currentMass_lt_two : wholeVorticityEuclideanMass
    (source.stateAfter stage).1.physical.contact.physicalState < 2
  physicalFailure : ButterflyLowMassPhysicalFailureAt stage

def butterflyCappedCurrentAdvance
    (stage : Nat)
    (payment : ButterflyCappedCurrentPaymentAt stage) :
    SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) := by
  rcases payment with currentMass | lowMassDebit
  · exact cappedMassKineticRootClockAdvance stage currentMass.down
  · exact sourceGeneratedRootClockAdvance_of_potential_domination
      lowMassDebit.down.2

/-- Exhausting the current capped ledger leaves exactly the already
generated half-critical/absorption physical row. -/
noncomputable def butterflyCappedCurrentPayment_or_physicalFailure
    (stage : Nat) :
    ButterflyCappedCurrentPaymentAt stage ⊕
      PLift (ButterflyCappedCurrentPhysicalFailureAt stage) := by
  by_cases currentMass : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState
  · exact Sum.inl (Sum.inl ⟨currentMass⟩)
  · have lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2 :=
      lt_of_not_ge currentMass
    by_cases debit : ButterflyLowMassCappedCurrentDebitAt stage
    · exact Sum.inl (Sum.inr ⟨⟨lowMass, debit⟩⟩)
    · exact Sum.inr ⟨
        { currentMass_lt_two := lowMass
          physicalFailure :=
            (butterflyLowMassCappedCurrentDebit_or_halfCritical_or_clockDeficit
              stage lowMass).resolve_left debit }⟩

/-- Coverage of the capped source face by the richer mixed/kinetic/bank
current.  This consumes the actual source-side prepaid face before any
physical shortfall is exposed. -/
def ButterflyRichCappedCoverageAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage)) : Prop :=
  cappedMassKineticClockPotential (source.stateAfter stage) ≤
    (butterflyCreditBearingClockState instruction).potential

theorem butterflyRichCappedCoverage_iff
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2) :
    ButterflyRichCappedCoverageAt stage instruction ↔
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState ≤
        standingActionMixedClockPotential (source.stateAfter stage) +
          instruction.bank := by
  unfold ButterflyRichCappedCoverageAt cappedMassKineticClockPotential
    butterflyCreditBearingClockState kineticCompensatedPotential
    butterflyActionKineticCoefficient
  rw [min_eq_left lowMass.le, div_eq_mul_inv]
  constructor <;> intro coverage <;> linarith

/-- Switch from the rich current to the capped successor only after the
current capped ledger and source-face coverage have both been generated.
All coverage slack and settlement waste become the successor bank, and the
complete action disposition remains in its predecessor payload. -/
noncomputable def butterflyRichToCappedTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (payment : ButterflyCappedCurrentPaymentAt stage)
    (coverage : ButterflyRichCappedCoverageAt stage instruction) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCreditBearingClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome := by
  let cappedAdvance := butterflyCappedCurrentAdvance stage payment
  have cappedDomination :
      source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
        cappedMassKineticClockPotential (source.stateAfter stage) := by
    have settlement := cappedAdvance.settlement
    have wasteNonneg := cappedAdvance.waste_nonneg
    change
      cappedMassKineticClockPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) +
            cappedAdvance.waste at settlement
    linarith
  let richAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) :=
    sourceGeneratedRootClockAdvance_of_potential_domination
      (cappedDomination.trans coverage)
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨richAdvance.waste, richAdvance.waste_nonneg⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCreditBearingClockState instruction)
      (butterflyCappedCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := richAdvance.settlement
        change
          (butterflyCreditBearingClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              cappedMassKineticClockPotential
                (source.stateAfter (stage + 1)) + richAdvance.waste
          at settlement
        change
          (butterflyCreditBearingClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              (cappedMassKineticClockPotential
                  (source.stateAfter (stage + 1)) + nextBank.1) + 0
        simpa only [nextBank, add_zero, add_assoc] using settlement }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment => exact .exactPayment retainedAdvance
  | generatedResidual => exact .generatedResidual retainedAdvance
  | obstruction => exact .obstructionAlternative retainedAdvance

/-- All currently generated clock assets consumed in one dependent result:
the four immediate mixed settlements, the complete coupled material, and
the capped physical alternative.  Only the final constructor remains for
source physics. -/
structure ButterflyFullyCreditedCurrentShortfallAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type where
  private mk ::
  richCompletePayment_isEmpty :
    IsEmpty (ButterflyRichCompleteOutcomePaymentAt
      stage instruction disposition)
  sourceShortfall : ButterflyRichCompleteSourceShortfallAt
    stage instruction disposition
  cappedCreditShortfall :
    (butterflyCreditBearingClockState instruction).potential <
      source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1))
  completeCreditShortfall :
    (butterflyCreditBearingClockState instruction).potential <
      source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1))
  cappedOrPhysical :
    (ButterflyCappedCurrentPaymentAt stage ×
        PLift (¬ ButterflyRichCappedCoverageAt stage instruction)) ⊕
      PLift (ButterflyCappedCurrentPhysicalFailureAt stage)

def butterflyRichCompleteInitialPayment :
    ButterflyRichCompleteOutcomePaymentAt 0
      butterflyCreditBearingInitialInstruction
      (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction 0) :=
  butterflyRichCompleteOutcomePayment_of_targetMass 0
    butterflyCreditBearingInitialInstruction _
      butterflyCompleteCreditInitialTargetMass

theorem butterflyFullyCreditedInitialShortfall_isEmpty :
    IsEmpty (ButterflyFullyCreditedCurrentShortfallAt 0
      butterflyCreditBearingInitialInstruction
      (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction 0)) :=
  ⟨fun shortfall =>
    shortfall.richCompletePayment_isEmpty.false
      butterflyRichCompleteInitialPayment⟩

def ButterflyRichTotalTransitionResultAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  ButterflyRichCompletePaidTransitionAt stage instruction disposition ⊕
    ((Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCreditBearingClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome) ⊕
      ButterflyFullyCreditedCurrentShortfallAt
        stage instruction disposition)

noncomputable def butterflyRichTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyRichTotalTransitionResultAt
      stage instruction disposition := by
  rcases butterflyRichCompleteTotalTransition
      stage instruction disposition with paid | emptyComplete
  · exact Sum.inl paid
  · by_cases covered : source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
          (butterflyCreditBearingClockState instruction).potential
    · exact Sum.inr (Sum.inl
        (butterflyCurrentToCappedTransition_of_domination stage
          (butterflyCreditBearingClockState instruction) disposition covered))
    have shortfall := lt_of_not_ge covered
    by_cases completeCovered : source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
          (butterflyCreditBearingClockState instruction).potential
    · exact Sum.inl (Sum.inr
        (butterflyCurrentToCompleteTransition_of_domination stage
          (butterflyCreditBearingClockState instruction) disposition completeCovered))
    rcases butterflyCappedCurrentPayment_or_physicalFailure stage with
      cappedPayment | physicalFailure
    · by_cases coverage : ButterflyRichCappedCoverageAt stage instruction
      · exact Sum.inr (Sum.inl (butterflyRichToCappedTransition
          stage instruction disposition cappedPayment coverage))
      · exact Sum.inr (Sum.inr
          { richCompletePayment_isEmpty := emptyComplete.down
            sourceShortfall :=
              (butterflyRichCompleteOutcomePayment_isEmpty_iff_sourceShortfall
                stage instruction disposition).mp emptyComplete.down
            cappedCreditShortfall := shortfall
            completeCreditShortfall := lt_of_not_ge completeCovered
            cappedOrPhysical := Sum.inl (cappedPayment, ⟨coverage⟩) })
    · exact Sum.inr (Sum.inr
        { richCompletePayment_isEmpty := emptyComplete.down
          sourceShortfall :=
            (butterflyRichCompleteOutcomePayment_isEmpty_iff_sourceShortfall
              stage instruction disposition).mp emptyComplete.down
          cappedCreditShortfall := shortfall
          completeCreditShortfall := lt_of_not_ge completeCovered
          cappedOrPhysical := Sum.inr physicalFailure })

/-- The three credit-bearing faces that can be emitted by the total root
transition.  The constructor retains the complete instruction, including
its bank and predecessor disposition; only `clockState` is a scalar
projection. -/
inductive ButterflyCreditClockFaceAt (state : source.State) : Type
  | rich (instruction : ButterflyCreditBearingClockInstructionAt state)
  | complete (instruction : ButterflyCreditBearingClockInstructionAt state)
  | capped (instruction : ButterflyCreditBearingClockInstructionAt state)

def ButterflyCreditClockFaceAt.clockState
    {state : source.State} :
    ButterflyCreditClockFaceAt state →
      SourceGeneratedRootClockStateAt source state
  | .rich instruction => butterflyCreditBearingClockState instruction
  | .complete instruction => butterflyCompleteCreditClockState instruction
  | .capped instruction => butterflyCappedCreditClockState instruction

/-- Minimal initial instruction for the recursive clock.  The initial
physical mass already activates the capped ledger, so no speculative rich
bank is needed before the first root transition. -/
def butterflyZeroBankInitialInstruction :
    ButterflyCreditBearingClockInstructionAt source.initial where
  stage := 0
  state_eq := rfl
  bank := 0
  bank_nonneg := le_rfl
  predecessor? := none

theorem stackedShortCurrent_contact_wholeMass_gt_two :
    (2 : Real) < wholeVorticityEuclideanMass
      stackedShortCurrent.contact.physicalState := by
  have finiteGt := stackedShortContact_sourceInventoryMass_gt_seed
  have finiteLe := finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    butterflyFirstStackModes stackedShortCurrent.contact.physicalState
  have twoLtFinite : (2 : Real) <
      finiteStateVorticityCoefficientEnstrophy butterflyFirstStackModes
        stackedShortCurrent.contact.physicalState := by
    exact (by norm_num : (2 : Real) < 173 / 2).trans finiteGt
  exact twoLtFinite.trans_le finiteLe

def butterflyCappedInitialCurrentPayment :
    ButterflyCappedCurrentPaymentAt 0 :=
  Sum.inl ⟨by
    change (2 : Real) ≤ wholeVorticityEuclideanMass
      stackedShortCurrent.contact.physicalState
    exact stackedShortCurrent_contact_wholeMass_gt_two.le⟩

def ButterflyMixedToRichCoverageAt
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage)) : Prop :=
  standingActionMixedClockPotential (source.stateAfter stage) +
      butterflyActionKineticCoefficient *
        puncturedWholeVorticityKineticMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState ≤
    currentClock.potential

/-- Reuse a framework-generated mixed settlement from any richer current
that already covers the mixed source account and the successor kinetic
account.  The remaining slack becomes the successor rich bank; no mixed-only
mode or post-hoc debt is introduced. -/
noncomputable def butterflyCurrentToRichTransition_of_mixedSettlement
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (mixedSettlement : SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMixedClockState (source.stateAfter stage))
      (standingActionMixedClockState (source.stateAfter (stage + 1))) outcome)
    (coverage : ButterflyMixedToRichCoverageAt stage currentClock) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage) currentClock
        (butterflyCreditBearingClockState nextInstruction) outcome := by
  have mixedDomination :
      source.clockAt (source.stateAfter stage) +
          standingActionMixedClockPotential (source.stateAfter (stage + 1)) ≤
        standingActionMixedClockPotential (source.stateAfter stage) := by
    have advance := mixedSettlement.resolved
    have settlement := advance.settlement
    have wasteNonneg := advance.waste_nonneg
    change
      standingActionMixedClockPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          standingActionMixedClockPotential (source.stateAfter (stage + 1)) +
            advance.waste at settlement
    linarith
  have richBaseDomination :
      source.clockAt (source.stateAfter stage) +
          kineticCompensatedPotential butterflyActionKineticCoefficient
            (source.stateAfter (stage + 1)) ≤ currentClock.potential := by
    unfold ButterflyMixedToRichCoverageAt at coverage
    unfold kineticCompensatedPotential
    linarith
  let richAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) currentClock
      (butterflyKineticBankClockState (stage + 1) 0 le_rfl) := by
    apply sourceGeneratedRootClockAdvance_of_potential_domination
    simpa only [butterflyKineticBankClockState, add_zero] using
      richBaseDomination
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨richAdvance.waste, richAdvance.waste_nonneg⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) currentClock
      (butterflyCreditBearingClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := richAdvance.settlement
        change
          currentClock.potential = source.clockAt (source.stateAfter stage) +
            (kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) + 0) + richAdvance.waste
          at settlement
        simp only [add_zero] at settlement
        change
          currentClock.potential = source.clockAt (source.stateAfter stage) +
            (kineticCompensatedPotential butterflyActionKineticCoefficient
                (source.stateAfter (stage + 1)) + nextBank.1) + 0
        simpa only [nextBank, add_zero, add_assoc] using settlement }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment => exact .exactPayment retainedAdvance
  | generatedResidual => exact .generatedResidual retainedAdvance
  | obstruction => exact .obstructionAlternative retainedAdvance

/-- Lift an already generated kinetic/barrier payment through an arbitrary
current face that covers its source account, and retain the entire slack in
the successor complete bank. -/
noncomputable def butterflyCurrentToCompleteTransition_of_kineticAdvance
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (baseAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (kineticBarrierClockState (source.stateAfter stage))
      (kineticBarrierClockState (source.stateAfter (stage + 1))))
    (coverage : kineticBarrierPotential (source.stateAfter stage) ≤
      currentClock.potential) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage) currentClock
        (butterflyCompleteCreditClockState nextInstruction) outcome := by
  have baseDomination :
      source.clockAt (source.stateAfter stage) +
          kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
        kineticBarrierPotential (source.stateAfter stage) := by
    have settlement := baseAdvance.settlement
    have wasteNonneg := baseAdvance.waste_nonneg
    change
      kineticBarrierPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          kineticBarrierPotential (source.stateAfter (stage + 1)) +
            baseAdvance.waste at settlement
    linarith
  let liftedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) currentClock
      (kineticBarrierClockState (source.stateAfter (stage + 1))) :=
    sourceGeneratedRootClockAdvance_of_potential_domination
      (baseDomination.trans coverage)
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨liftedAdvance.waste, liftedAdvance.waste_nonneg⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) currentClock
      (butterflyCompleteCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := liftedAdvance.settlement
        change
          currentClock.potential = source.clockAt (source.stateAfter stage) +
            kineticBarrierPotential (source.stateAfter (stage + 1)) +
              liftedAdvance.waste at settlement
        change
          currentClock.potential = source.clockAt (source.stateAfter stage) +
            (kineticBarrierPotential (source.stateAfter (stage + 1)) +
              nextBank.1) + 0
        simpa only [nextBank, add_zero, add_assoc] using settlement }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment => exact .exactPayment retainedAdvance
  | generatedResidual => exact .generatedResidual retainedAdvance
  | obstruction => exact .obstructionAlternative retainedAdvance

/-- Complete-material advance from an arbitrary current clock.  The caller
does not supply a payment scalar: `domination` is the exact same-occurrence
projection consumed by the face classifier below. -/
def butterflyCurrentToCompleteMaterialAdvance
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (domination : source.clockAt (source.stateAfter stage) +
        (kineticBarrierPotential (source.stateAfter (stage + 1)) +
          butterflyGeneratedResidualTargetAccount
            stage effect residual expansion) ≤ currentClock.potential) :
    Σ nextBank : { value : Real // 0 ≤ value },
      SourceGeneratedRootClockAdvanceAt source
        (source.stateAfter stage) currentClock
        (butterflyKineticBarrierBankClockState (stage + 1)
          nextBank.1 nextBank.2) := by
  let targetAccount := butterflyGeneratedResidualTargetAccount
    stage effect residual expansion
  let surplus := currentClock.potential -
    source.clockAt (source.stateAfter stage) -
      (kineticBarrierPotential (source.stateAfter (stage + 1)) +
        targetAccount)
  have targetNonneg : 0 ≤ targetAccount :=
    butterflyGeneratedResidualTargetAccount_nonneg
      stage effect residual expansion
  have surplusNonneg : 0 ≤ surplus := by
    dsimp only [surplus, targetAccount]
    linarith
  let nextBank := targetAccount + surplus
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg targetNonneg surplusNonneg
  refine ⟨⟨nextBank, nextBankNonneg⟩, ?_⟩
  exact
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        change currentClock.potential = source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            nextBank) + 0
        dsimp only [nextBank, surplus, targetAccount]
        ring }

noncomputable def
    butterflyCurrentToCompleteGeneratedResidualTransition_of_domination
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    (effect : NativeFluidMediumExactOperationalEffectAt source
      (source.stateAfter stage))
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt
      effect.effect residual)
    (expansionEq : expansion =
      source.generateOperationalResidualExpansionAt effect.effect residual)
    (residualPayment : NativeFluidMediumResidualPaymentAt
      effect residual expansion)
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage
        (.generatedResidual effect residual expansion expansionEq
          residualPayment))
    (domination : source.clockAt (source.stateAfter stage) +
        (kineticBarrierPotential (source.stateAfter (stage + 1)) +
          butterflyGeneratedResidualTargetAccount
            stage effect residual expansion) ≤ currentClock.potential) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage) currentClock
        (butterflyCompleteCreditClockState nextInstruction)
        (.generatedResidual effect residual expansion expansionEq
          residualPayment) := by
  rcases butterflyCurrentToCompleteMaterialAdvance stage currentClock
      effect residual expansion domination with ⟨nextBank, nextAdvance⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  refine ⟨nextInstruction, ?_⟩
  simpa only [butterflyCompleteCreditClockState,
    butterflyKineticBarrierBankClockState,
    NativeFluidMediumSource.stateAfter_succ, nextInstruction,
    butterflyCompleteCreditNextInstruction,
    source, stackedStandingActionMediumSource] using
    (SourceGeneratedRootClockSettlementAt.generatedResidual
      (effect := effect) (residual := residual)
      (expansion := expansion) (expansion_eq := expansionEq)
      (payment := residualPayment) nextAdvance)

noncomputable def butterflyCurrentToCompleteObstructionTransition_of_domination
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    (obstruction : NativeFluidMediumOperationalObstructionAt source
      (source.stateAfter stage))
    (demand : SourceGeneratedU7DemandAt
      (nativeFluidMediumU7Producer source) obstruction
        ((nativeFluidMediumU7Producer source).generateDemand obstruction))
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage
        (.obstruction obstruction demand))
    (domination : source.clockAt (source.stateAfter stage) +
        (kineticBarrierPotential (source.stateAfter (stage + 1)) +
          butterflyGeneratedResidualTargetAccount stage
            obstruction.effect obstruction.residual obstruction.expansion) ≤
      currentClock.potential) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage) currentClock
        (butterflyCompleteCreditClockState nextInstruction)
        (.obstruction obstruction demand) := by
  rcases butterflyCurrentToCompleteMaterialAdvance stage currentClock
      obstruction.effect obstruction.residual obstruction.expansion
        domination with ⟨nextBank, nextAdvance⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  refine ⟨nextInstruction, ?_⟩
  simpa only [butterflyCompleteCreditClockState,
    butterflyKineticBarrierBankClockState,
    NativeFluidMediumSource.stateAfter_succ, nextInstruction,
    butterflyCompleteCreditNextInstruction,
    source, stackedStandingActionMediumSource] using
    (SourceGeneratedRootClockSettlementAt.obstructionAlternative
      (obstruction := obstruction) (demand := demand) nextAdvance)

/-- A complete face may switch to the capped successor at any current, not
only after a caller exposes `currentMass < 2`.  The failed complete payment
itself eliminates the exact root constructor.  All switch slack is retained
in the successor bank. -/
noncomputable def butterflyCompleteToCappedTransition_of_empty
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (emptyComplete : IsEmpty (ButterflyCompleteCreditOutcomePaymentAt
      stage instruction outcome))
    (payment : ButterflyCappedCurrentPaymentAt stage)
    (coverage : ButterflyCompleteCreditCappedCoverageAt
      stage instruction) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCompleteCreditClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome := by
  let cappedAdvance := butterflyCappedCurrentAdvance stage payment
  have cappedDomination :
      source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
        cappedMassKineticClockPotential (source.stateAfter stage) := by
    have settlement := cappedAdvance.settlement
    have wasteNonneg := cappedAdvance.waste_nonneg
    change
      cappedMassKineticClockPotential (source.stateAfter stage) =
        source.clockAt (source.stateAfter stage) +
          cappedMassKineticClockPotential (source.stateAfter (stage + 1)) +
            cappedAdvance.waste at settlement
    linarith
  let completeAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (cappedMassKineticClockState (source.stateAfter (stage + 1))) :=
    sourceGeneratedRootClockAdvance_of_potential_domination
      (cappedDomination.trans coverage)
  let nextBank : { value : Real // 0 ≤ value } :=
    ⟨completeAdvance.waste, completeAdvance.waste_nonneg⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBank
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (butterflyCappedCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := completeAdvance.settlement
        change
          (butterflyCompleteCreditClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              cappedMassKineticClockPotential
                (source.stateAfter (stage + 1)) + completeAdvance.waste
          at settlement
        change
          (butterflyCompleteCreditClockState instruction).potential =
            source.clockAt (source.stateAfter stage) +
              (cappedMassKineticClockPotential
                  (source.stateAfter (stage + 1)) + nextBank.1) + 0
        simpa only [nextBank, add_zero, add_assoc] using settlement }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment =>
      exact False.elim (emptyComplete.false PUnit.unit)
  | generatedResidual => exact .generatedResidual retainedAdvance
  | obstruction => exact .obstructionAlternative retainedAdvance

def ButterflySettledMixedCoverageFailureAt
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Prop :=
  match disposition with
  | .settled _ => ¬ ButterflyMixedToRichCoverageAt stage currentClock
  | .generatedResidualAdvance .. => True
  | .obstructionAdvance .. => True

structure ButterflyCompleteFaceShortfallAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type where
  private mk ::
  completePayment_isEmpty : IsEmpty
    (ButterflyCompleteCreditOutcomePaymentAt stage instruction outcome)
  completeSourceShortfall : ButterflyCompleteCreditLowTargetShortfallAt
    stage instruction outcome
  cappedCreditShortfall :
    (butterflyCompleteCreditClockState instruction).potential <
      source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1))
  completeCreditShortfall :
    (butterflyCompleteCreditClockState instruction).potential <
      source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1))
  cappedOrPhysical :
    (ButterflyCappedCurrentPaymentAt stage ×
        PLift (¬ ButterflyCompleteCreditCappedCoverageAt
          stage instruction)) ⊕
      PLift (ButterflyCappedCurrentPhysicalFailureAt stage)
  mixedSettlementUnavailable : ButterflySettledMixedCoverageFailureAt
    stage (butterflyCompleteCreditClockState instruction)
      disposition

def ButterflyCompleteFaceTransitionResultAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCompleteCreditClockState instruction)
      (butterflyCompleteCreditClockState nextInstruction) outcome) ⊕
    ((Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCompleteCreditClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome) ⊕
      ((Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
          (source.stateAfter (stage + 1)),
        SourceGeneratedRootClockSettlementAt source
          (source.stateAfter stage)
          (butterflyCompleteCreditClockState instruction)
          (butterflyCreditBearingClockState nextInstruction) outcome) ⊕
        ButterflyCompleteFaceShortfallAt stage instruction disposition))

noncomputable def butterflyCompleteFaceTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyCompleteFaceTransitionResultAt
      stage instruction disposition := by
  rcases butterflyCompleteCreditTotalTransition
      stage instruction disposition with completeNext | emptyComplete
  · exact Sum.inl completeNext
  · by_cases covered : source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
          (butterflyCompleteCreditClockState instruction).potential
    · exact Sum.inr (Sum.inl
        (butterflyCurrentToCappedTransition_of_domination stage
          (butterflyCompleteCreditClockState instruction) disposition covered))
    have shortfall := lt_of_not_ge covered
    by_cases completeCovered : source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
          (butterflyCompleteCreditClockState instruction).potential
    · exact Sum.inl
        (butterflyCurrentToCompleteTransition_of_domination stage
          (butterflyCompleteCreditClockState instruction) disposition completeCovered)
    rcases butterflyCappedCurrentPayment_or_physicalFailure stage with
      cappedPayment | physicalFailure
    · by_cases coverage : ButterflyCompleteCreditCappedCoverageAt
          stage instruction
      · exact Sum.inr (Sum.inl
          (butterflyCompleteToCappedTransition_of_empty stage instruction
            disposition emptyComplete.down cappedPayment coverage))
      · cases disposition with
        | settled settlement =>
            by_cases mixedCoverage : ButterflyMixedToRichCoverageAt stage
                (butterflyCompleteCreditClockState instruction)
            · exact Sum.inr (Sum.inr (Sum.inl
                (butterflyCurrentToRichTransition_of_mixedSettlement
                  stage (butterflyCompleteCreditClockState instruction)
                    (.settled settlement) settlement mixedCoverage)))
            · exact Sum.inr (Sum.inr (Sum.inr
                { completePayment_isEmpty := emptyComplete.down
                  completeSourceShortfall :=
                    (butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
                      stage instruction _).mp emptyComplete.down
                  cappedCreditShortfall := shortfall
                  completeCreditShortfall := lt_of_not_ge completeCovered
                  cappedOrPhysical := Sum.inl (cappedPayment, ⟨coverage⟩)
                  mixedSettlementUnavailable := mixedCoverage }))
        | generatedResidualAdvance =>
            exact Sum.inr (Sum.inr (Sum.inr
              { completePayment_isEmpty := emptyComplete.down
                completeSourceShortfall :=
                  (butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
                    stage instruction _).mp emptyComplete.down
                cappedCreditShortfall := shortfall
                completeCreditShortfall := lt_of_not_ge completeCovered
                cappedOrPhysical := Sum.inl (cappedPayment, ⟨coverage⟩)
                mixedSettlementUnavailable := True.intro }))
        | obstructionAdvance =>
            exact Sum.inr (Sum.inr (Sum.inr
              { completePayment_isEmpty := emptyComplete.down
                completeSourceShortfall :=
                  (butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
                    stage instruction _).mp emptyComplete.down
                cappedCreditShortfall := shortfall
                completeCreditShortfall := lt_of_not_ge completeCovered
                cappedOrPhysical := Sum.inl (cappedPayment, ⟨coverage⟩)
                mixedSettlementUnavailable := True.intro }))
    · cases disposition with
      | settled settlement =>
          by_cases mixedCoverage : ButterflyMixedToRichCoverageAt stage
              (butterflyCompleteCreditClockState instruction)
          · exact Sum.inr (Sum.inr (Sum.inl
              (butterflyCurrentToRichTransition_of_mixedSettlement
                stage (butterflyCompleteCreditClockState instruction)
                  (.settled settlement) settlement mixedCoverage)))
          · exact Sum.inr (Sum.inr (Sum.inr
              { completePayment_isEmpty := emptyComplete.down
                completeSourceShortfall :=
                  (butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
                    stage instruction _).mp emptyComplete.down
                cappedCreditShortfall := shortfall
                completeCreditShortfall := lt_of_not_ge completeCovered
                cappedOrPhysical := Sum.inr physicalFailure
                mixedSettlementUnavailable := mixedCoverage }))
      | generatedResidualAdvance =>
          exact Sum.inr (Sum.inr (Sum.inr
            { completePayment_isEmpty := emptyComplete.down
              completeSourceShortfall :=
                (butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
                  stage instruction _).mp emptyComplete.down
              cappedCreditShortfall := shortfall
              completeCreditShortfall := lt_of_not_ge completeCovered
              cappedOrPhysical := Sum.inr physicalFailure
              mixedSettlementUnavailable := True.intro }))
      | obstructionAdvance =>
          exact Sum.inr (Sum.inr (Sum.inr
            { completePayment_isEmpty := emptyComplete.down
              completeSourceShortfall :=
                (butterflyCompleteCreditOutcomePayment_isEmpty_iff_shortfall
                  stage instruction _).mp emptyComplete.down
              cappedCreditShortfall := shortfall
              completeCreditShortfall := lt_of_not_ge completeCovered
              cappedOrPhysical := Sum.inr physicalFailure
              mixedSettlementUnavailable := True.intro }))

/-- The capped mode keeps its incoming bank and capitalizes the exact base
settlement waste.  The complete predecessor disposition is retained in the
compiler-owned successor instruction. -/
noncomputable def butterflyCappedCreditTransition_of_payment
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (payment : ButterflyCappedCurrentPaymentAt stage) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCappedCreditClockState instruction)
        (butterflyCappedCreditClockState nextInstruction) outcome := by
  let baseAdvance := butterflyCappedCurrentAdvance stage payment
  let nextBank : Real := instruction.bank + baseAdvance.waste
  have nextBankNonneg : 0 ≤ nextBank :=
    add_nonneg instruction.bank_nonneg baseAdvance.waste_nonneg
  let nextBankValue : { value : Real // 0 ≤ value } :=
    ⟨nextBank, nextBankNonneg⟩
  let nextInstruction := butterflyCompleteCreditNextInstruction
    stage disposition nextBankValue
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage)
      (butterflyCappedCreditClockState instruction)
      (butterflyCappedCreditClockState nextInstruction) :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have settlement := baseAdvance.settlement
        change
          cappedMassKineticClockPotential (source.stateAfter stage) =
            source.clockAt (source.stateAfter stage) +
              cappedMassKineticClockPotential
                (source.stateAfter (stage + 1)) + baseAdvance.waste
          at settlement
        change
          cappedMassKineticClockPotential (source.stateAfter stage) +
              instruction.bank =
            source.clockAt (source.stateAfter stage) +
              (cappedMassKineticClockPotential
                  (source.stateAfter (stage + 1)) + nextBankValue.1) + 0
        dsimp only [nextBankValue, nextBank]
        linarith }
  refine ⟨nextInstruction, ?_⟩
  cases outcome with
  | exactPayment => exact .exactPayment retainedAdvance
  | generatedResidual => exact .generatedResidual retainedAdvance
  | obstruction => exact .obstructionAlternative retainedAdvance

/-- A settled mixed row can be reused only when the exact current
disposition actually carries that settlement.  The negative constructors
are empty by construction; callers cannot present an unrelated mixed
settlement or choose a future branch. -/
def ButterflyCappedSettledMixedPaymentAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  match disposition with
  | .settled _ => PLift (ButterflyMixedToRichCoverageAt stage
      (butterflyCappedCreditClockState instruction))
  | .generatedResidualAdvance .. => PLift False
  | .obstructionAdvance .. => PLift False

/-- Every existing complete-current payment, restated for an arbitrary
incoming clock face.  The payment remains indexed by the actual root
outcome.  In particular, the residual constructors retain the exact
generated expansion account rather than projecting it to a scalar debit. -/
def ButterflyCurrentCompleteOutcomePaymentAt
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage)) :
    NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) → Type
  | .exactPayment .. =>
      PLift (kineticBarrierPotential (source.stateAfter stage) ≤
        currentClock.potential)
  | .generatedResidual effect residual expansion .. =>
      PLift (TargetMassTwoAt (source.stateAfter stage) ∧
        kineticBarrierPotential (source.stateAfter stage) ≤
          currentClock.potential) ⊕
      PLift (source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount
              stage effect residual expansion) ≤ currentClock.potential)
  | .obstruction obstruction _demand =>
      PLift (TargetMassTwoAt (source.stateAfter stage) ∧
        kineticBarrierPotential (source.stateAfter stage) ≤
          currentClock.potential) ⊕
      PLift (source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            butterflyGeneratedResidualTargetAccount stage
              obstruction.effect obstruction.residual
                obstruction.expansion) ≤ currentClock.potential)

/-- Consume an arbitrary-current complete payment and emit the complete
successor face.  This is one dependent fold over the original outcome: the
kinetic and complete-expansion alternatives never detach from their
physical effect, residual, write-back, or generated next. -/
noncomputable def butterflyCurrentToCompleteTransition_of_payment
    (stage : Nat)
    (currentClock : SourceGeneratedRootClockStateAt source
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (currentPayment : ButterflyCurrentCompleteOutcomePaymentAt
      stage currentClock outcome) :
    Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage) currentClock
        (butterflyCompleteCreditClockState nextInstruction) outcome := by
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact butterflyCurrentToCompleteTransition_of_kineticAdvance
        stage currentClock disposition
          (kineticBarrierRootExactAdvance stage effect commutes)
          currentPayment.down
  | generatedResidual effect residual expansion expansionEq payment =>
      rcases currentPayment with kineticPayment | completePayment
      · exact butterflyCurrentToCompleteTransition_of_kineticAdvance
          stage currentClock disposition
            (kineticBarrierRootResidualAdvance stage effect residual
              kineticPayment.down.1)
            kineticPayment.down.2
      · exact
          butterflyCurrentToCompleteGeneratedResidualTransition_of_domination
            stage currentClock effect residual expansion expansionEq payment
              disposition completePayment.down
  | obstruction obstruction demand =>
      rcases currentPayment with kineticPayment | completePayment
      · exact butterflyCurrentToCompleteTransition_of_kineticAdvance
          stage currentClock disposition
            (kineticBarrierRootResidualAdvance stage obstruction.effect
              obstruction.residual kineticPayment.down.1)
            kineticPayment.down.2
      · exact butterflyCurrentToCompleteObstructionTransition_of_domination
          stage currentClock obstruction demand disposition
            completePayment.down

/-- All already-generated alternatives available after the capped base
fails: either reuse the exact settled mixed row, or consume the actual
outcome's kinetic/complete material. -/
def ButterflyCappedAlternativePaymentAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  ButterflyCappedSettledMixedPaymentAt stage instruction disposition ⊕
    ButterflyCurrentCompleteOutcomePaymentAt stage
      (butterflyCappedCreditClockState instruction) outcome

/-- Consume a capped alternative in the same root transition.  The
successor face is chosen by the payment actually generated: rich for the
settled mixed row, complete for the kinetic/full-material row. -/
noncomputable def butterflyCappedAlternativeTransition_of_payment
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome)
    (payment : ButterflyCappedAlternativePaymentAt
      stage instruction disposition) :
    Σ nextFace : ButterflyCreditClockFaceAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCappedCreditClockState instruction)
        nextFace.clockState outcome := by
  rcases payment with mixedPayment | completePayment
  · cases disposition with
    | settled settlement =>
        rcases butterflyCurrentToRichTransition_of_mixedSettlement
            stage (butterflyCappedCreditClockState instruction)
              (.settled settlement) settlement mixedPayment.down with
          ⟨nextInstruction, nextSettlement⟩
        exact ⟨.rich nextInstruction, nextSettlement⟩
    | generatedResidualAdvance => exact False.elim mixedPayment.down
    | obstructionAdvance => exact False.elim mixedPayment.down
  · rcases butterflyCurrentToCompleteTransition_of_payment
        stage (butterflyCappedCreditClockState instruction)
          disposition completePayment with
      ⟨nextInstruction, nextSettlement⟩
    exact ⟨.complete nextInstruction, nextSettlement⟩

structure ButterflyCappedFaceShortfallAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type where
  private mk ::
  physicalFailure : ButterflyCappedCurrentPhysicalFailureAt stage
  cappedCreditShortfall :
    (butterflyCappedCreditClockState instruction).potential <
      source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1))
  completeCreditShortfall :
    (butterflyCappedCreditClockState instruction).potential <
      source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1))
  alternativePayment_isEmpty : IsEmpty
    (ButterflyCappedAlternativePaymentAt stage instruction disposition)

theorem butterflyCappedInitialShortfall_isEmpty :
    IsEmpty (ButterflyCappedFaceShortfallAt 0
      butterflyZeroBankInitialInstruction
      (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction 0)) := by
  constructor
  intro shortfall
  have highMass : (2 : Real) ≤ wholeVorticityEuclideanMass
      (source.stateAfter 0).1.physical.contact.physicalState := by
    change (2 : Real) ≤ wholeVorticityEuclideanMass
      stackedShortCurrent.contact.physicalState
    exact stackedShortCurrent_contact_wholeMass_gt_two.le
  exact (not_lt_of_ge highMass)
    shortfall.physicalFailure.currentMass_lt_two

def ButterflyCappedFaceTransitionResultAt
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextInstruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (butterflyCappedCreditClockState instruction)
      (butterflyCappedCreditClockState nextInstruction) outcome) ⊕
    ((Σ nextFace : ButterflyCreditClockFaceAt
        (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (butterflyCappedCreditClockState instruction)
        nextFace.clockState outcome) ⊕
      ButterflyCappedFaceShortfallAt stage instruction disposition)

noncomputable def butterflyCappedFaceTotalTransition
    (stage : Nat)
    (instruction : ButterflyCreditBearingClockInstructionAt
      (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyCappedFaceTransitionResultAt
      stage instruction disposition := by
  rcases butterflyCappedCurrentPayment_or_physicalFailure stage with
    payment | physicalFailure
  · exact Sum.inl (butterflyCappedCreditTransition_of_payment
      stage instruction disposition payment)
  · by_cases covered : source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1)) ≤
          (butterflyCappedCreditClockState instruction).potential
    · exact Sum.inl
        (butterflyCurrentToCappedTransition_of_domination stage
          (butterflyCappedCreditClockState instruction) disposition covered)
    by_cases completeCovered : source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1)) ≤
          (butterflyCappedCreditClockState instruction).potential
    · rcases butterflyCurrentToCompleteTransition_of_domination stage
        (butterflyCappedCreditClockState instruction) disposition completeCovered with
          ⟨nextInstruction, settlement⟩
      exact Sum.inr (Sum.inl ⟨.complete nextInstruction, settlement⟩)
    by_cases available : Nonempty (ButterflyCappedAlternativePaymentAt
        stage instruction disposition)
    · exact Sum.inr (Sum.inl
        (butterflyCappedAlternativeTransition_of_payment
          stage instruction disposition (Classical.choice available)))
    · exact Sum.inr (Sum.inr
        { physicalFailure := physicalFailure.down
          cappedCreditShortfall := lt_of_not_ge covered
          completeCreditShortfall := lt_of_not_ge completeCovered
          alternativePayment_isEmpty :=
            ⟨fun payment => available ⟨payment⟩⟩ })

/-- The sole residual type seen by the recursive root clock after selecting
the current compiler-generated face.  Each branch is still indexed by its
exact instruction and root disposition; no scalar or future branch is
detached from the face that generated it. -/
def ButterflyCreditClockFaceResidualAt
    (stage : Nat)
    (face : ButterflyCreditClockFaceAt (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  match face with
  | .rich instruction =>
      ButterflyFullyCreditedCurrentShortfallAt
        stage instruction disposition
  | .complete instruction =>
      ButterflyCompleteFaceShortfallAt stage instruction disposition
  | .capped instruction =>
      ButterflyCappedFaceShortfallAt stage instruction disposition

def ButterflyCreditClockFaceTransitionResultAt
    (stage : Nat)
    (face : ButterflyCreditClockFaceAt (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) : Type :=
  (Σ nextFace : ButterflyCreditClockFaceAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage) face.clockState nextFace.clockState outcome) ⊕
    ButterflyCreditClockFaceResidualAt stage face disposition

noncomputable def butterflyCreditClockFaceTotalTransition
    (stage : Nat)
    (face : ButterflyCreditClockFaceAt (source.stateAfter stage))
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (disposition : SourceGeneratedStandingActionRunClockDispositionAt
      stackedInitialActionMaterialInstruction stage outcome) :
    ButterflyCreditClockFaceTransitionResultAt
      stage face disposition := by
  cases face with
  | rich instruction =>
      rcases butterflyRichTotalTransition stage instruction disposition with
        richOrComplete | cappedOrShortfall
      · rcases richOrComplete with richNext | completeNext
        · rcases richNext with ⟨nextInstruction, settlement⟩
          exact Sum.inl ⟨.rich nextInstruction, settlement⟩
        · rcases completeNext with ⟨nextInstruction, settlement⟩
          exact Sum.inl ⟨.complete nextInstruction, settlement⟩
      · rcases cappedOrShortfall with cappedNext | shortfall
        · rcases cappedNext with ⟨nextInstruction, settlement⟩
          exact Sum.inl ⟨.capped nextInstruction, settlement⟩
        · exact Sum.inr shortfall
  | complete instruction =>
      rcases butterflyCompleteFaceTotalTransition
          stage instruction disposition with completeNext | cappedOrShortfall
      · rcases completeNext with ⟨nextInstruction, settlement⟩
        exact Sum.inl ⟨.complete nextInstruction, settlement⟩
      · rcases cappedOrShortfall with cappedNext | richOrShortfall
        · rcases cappedNext with ⟨nextInstruction, settlement⟩
          exact Sum.inl ⟨.capped nextInstruction, settlement⟩
        · rcases richOrShortfall with richNext | shortfall
          · rcases richNext with ⟨nextInstruction, settlement⟩
            exact Sum.inl ⟨.rich nextInstruction, settlement⟩
          · exact Sum.inr shortfall
  | capped instruction =>
      rcases butterflyCappedFaceTotalTransition
          stage instruction disposition with cappedNext | alternativeOrShortfall
      · rcases cappedNext with ⟨nextInstruction, settlement⟩
        exact Sum.inl ⟨.capped nextInstruction, settlement⟩
      · rcases alternativeOrShortfall with alternativeNext | shortfall
        · exact Sum.inl alternativeNext
        · exact Sum.inr shortfall

/-- The authoritative first root-clock transition after every generated
asset has been composed.  Its successor dependent face is selected by the
total root disposition itself; the fully credited residual is eliminated
by the same source-selected target-mass receipt. -/
noncomputable def butterflyRichInitialRootTransition :
    Σ nextFace : ButterflyCreditClockFaceAt
        (source.successor source.initial),
      SourceGeneratedRootClockSettlementAt source source.initial
        (butterflyCreditBearingClockState
          butterflyCreditBearingInitialInstruction)
        nextFace.clockState
        (nativeFluidMediumRootOperationalOutcomeAt source source.initial) := by
  let disposition := sourceGeneratedStandingActionRunClockDisposition
    stackedInitialActionMaterialInstruction 0
  rcases butterflyRichTotalTransition 0
      butterflyCreditBearingInitialInstruction disposition with
    richOrComplete | cappedOrShortfall
  · rcases richOrComplete with richNext | completeNext
    · rcases richNext with ⟨nextInstruction, settlement⟩
      exact ⟨.rich nextInstruction, by
        simpa only [source, stackedStandingActionMediumSource,
          ButterflyCreditClockFaceAt.clockState,
          NativeFluidMediumSource.stateAfter_zero,
          NativeFluidMediumSource.stateAfter_succ] using settlement⟩
    · rcases completeNext with ⟨nextInstruction, settlement⟩
      exact ⟨.complete nextInstruction, by
        simpa only [source, stackedStandingActionMediumSource,
          ButterflyCreditClockFaceAt.clockState,
          NativeFluidMediumSource.stateAfter_zero,
          NativeFluidMediumSource.stateAfter_succ] using settlement⟩
  · rcases cappedOrShortfall with cappedNext | shortfall
    · rcases cappedNext with ⟨nextInstruction, settlement⟩
      exact ⟨.capped nextInstruction, by
        simpa only [source, stackedStandingActionMediumSource,
          ButterflyCreditClockFaceAt.clockState,
          NativeFluidMediumSource.stateAfter_zero,
          NativeFluidMediumSource.stateAfter_succ] using settlement⟩
    · exact False.elim
        (butterflyFullyCreditedInitialShortfall_isEmpty.false shortfall)

/-- The first occurrence not paid by the moving-inventory instruction still
has a total current-side root settlement.  The root's exact constructor uses
its existing moving settlement.  A genuine residual uses the kinetic ledger
when its actual target mass is at least two, and otherwise spends the same
edge's strict whole-mass collapse.  The branch and both clock faces are
generated here; callers provide only the already-settled finite prefix. -/
noncomputable def butterflyFirstUnpaidRootSettlement
    (stage : Nat)
    (priorDebit : ∀ prior < stage,
      ButterflyOutcomeCurrentDebitAt prior) :
    Σ currentClock : SourceGeneratedRootClockStateAt source
        (source.stateAfter stage),
      Σ nextClock : SourceGeneratedRootClockStateAt source
          (source.successor (source.stateAfter stage)),
        SourceGeneratedRootClockSettlementAt source
          (source.stateAfter stage) currentClock nextClock
          (nativeFluidMediumRootOperationalOutcomeAt source
            (source.stateAfter stage)) := by
  classical
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact ⟨standingActionMovingClockState stage,
        standingActionMovingClockState (stage + 1),
        .exactPayment
          (standingActionMovingClockRootExactAdvance stage effect commutes)⟩
  | generatedResidual effect residual expansion expansionEq payment =>
      by_cases targetMass : TargetMassTwoAt (source.stateAfter stage)
      · exact ⟨kineticBarrierClockState (source.stateAfter stage),
          kineticBarrierClockState (source.stateAfter (stage + 1)),
          .generatedResidual
            (kineticBarrierRootResidualAdvance
              stage effect residual targetMass)⟩
      · exact ⟨wholeMassClockState (source.stateAfter stage),
          wholeMassClockState (source.stateAfter (stage + 1)),
          .generatedResidual
            (wholeMassRootClockAdvance_of_collapse
              stage priorDebit targetMass)⟩
  | obstruction obstruction demand =>
      by_cases targetMass : TargetMassTwoAt (source.stateAfter stage)
      · exact ⟨kineticBarrierClockState (source.stateAfter stage),
          kineticBarrierClockState (source.stateAfter (stage + 1)),
          .obstructionAlternative
            (kineticBarrierRootResidualAdvance stage obstruction.effect
              obstruction.residual targetMass)⟩
      · exact ⟨wholeMassClockState (source.stateAfter stage),
          wholeMassClockState (source.stateAfter (stage + 1)),
          .obstructionAlternative
            (wholeMassRootClockAdvance_of_collapse
              stage priorDebit targetMass)⟩

/-- Causally aligned version of the first-unpaid total settlement.  The
incoming face is fixed before the outcome: moving reserve and kinetic entropy
are both prepaid.  The actual root outcome then generates exactly one
successor face—prepaid after exact payment, kinetic after a high-mass
residual, or same-edge scaled whole mass after a collapse. -/
noncomputable def butterflyFirstUnpaidPrepaidRootSettlement
    (stage : Nat)
    (priorDebit : ∀ prior < stage,
      ButterflyOutcomeCurrentDebitAt prior) :
    Σ nextClock : SourceGeneratedRootClockStateAt source
        (source.successor (source.stateAfter stage)),
      SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage)
        (standingActionMovingKineticClockState stage) nextClock
        (nativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter stage)) := by
  classical
  by_cases targetMass : TargetMassTwoAt (source.stateAfter stage)
  · exact standingActionMovingKineticRootSettlement_of_targetMass
      stage targetMass
  · have notTargetMassTwo : ¬ 2 ≤ wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.nextContact.physicalState := by
      simpa only [TargetMassTwoAt] using targetMass
    generalize outcomeEq :
      nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage) = outcome
    cases outcome with
    | exactPayment effect rooted commutes =>
        exact ⟨standingActionMovingKineticClockState (stage + 1),
          .exactPayment
            (standingActionMovingKineticClockRootExactAdvance
              stage effect commutes)⟩
    | generatedResidual effect residual expansion expansionEq payment =>
        rcases
          standingActionMovingKinetic_to_scaledWholeMass_collapseAdvance
            stage priorDebit notTargetMassTwo with
          ⟨nextClock, advance⟩
        exact ⟨nextClock, .generatedResidual advance⟩
    | obstruction obstruction demand =>
        rcases
          standingActionMovingKinetic_to_scaledWholeMass_collapseAdvance
            stage priorDebit notTargetMassTwo with
          ⟨nextClock, advance⟩
        exact ⟨nextClock, .obstructionAlternative advance⟩

def standingActionMovingCappedClockSettlement_of_movingSettlement
    (stage : Nat)
    (currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState)
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)}
    (settlement : SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMovingClockState stage)
      (standingActionMovingClockState (stage + 1)) outcome) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMovingCappedClockState stage)
      (standingActionMovingCappedClockState (stage + 1)) outcome := by
  cases settlement with
  | exactPayment advance =>
      exact .exactPayment
        (standingActionMovingCappedClockAdvance_of_movingAdvance
          stage currentMassTwo advance)
  | generatedResidual advance =>
      exact .generatedResidual
        (standingActionMovingCappedClockAdvance_of_movingAdvance
          stage currentMassTwo advance)
  | obstructionAlternative advance =>
      exact .obstructionAlternative
        (standingActionMovingCappedClockAdvance_of_movingAdvance
          stage currentMassTwo advance)
  | obstructionIncompatible incompatible =>
      exact .obstructionIncompatible incompatible

noncomputable def standingActionMovingCappedClockRootSettlement_of_outcomeDebit
    (stage : Nat)
    (currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState)
    (instruction : ButterflyOutcomeCurrentDebitAt stage) :
    SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      (standingActionMovingCappedClockState stage)
      (standingActionMovingCappedClockState (stage + 1))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) :=
  standingActionMovingCappedClockSettlement_of_movingSettlement
    stage currentMassTwo
    (standingActionMovingClockRootSettlement_of_outcomeDebit
      stage instruction)

/-- Framework-generated paid prefix with a physically capped backup account
already installed.  The mass hypothesis at each edge is a conclusion of the
previous paid prefix, not a future table field. -/
theorem butterflyMovingCappedClockPrefix_add_potential_le_initial
    (length : Nat)
    (currentDebit : ∀ stage < length,
      ButterflyOutcomeCurrentDebitAt stage) :
    (∑ stage ∈ Finset.range length,
        source.clockAt (source.stateAfter stage)) +
        standingActionMovingCappedClockPotential length ≤
      standingActionMovingCappedClockPotential 0 := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      have priorDebit : ∀ stage < length,
          ButterflyOutcomeCurrentDebitAt stage := fun stage stageLt =>
        currentDebit stage (stageLt.trans (Nat.lt_succ_self length))
      have prior := inductionHypothesis priorDebit
      have currentMassGt :=
        butterflyRun_currentMass_gt_eightyFive_of_priorOutcomeDebit
          length priorDebit
      have currentEq :
          (source.stateAfter length).1.physical =
            run stackedShortCurrent length := by
        have generated :=
          standingActionWholeRestartMediumSource_stateAfter_current
            stackedInitialActionMaterialInstruction length
        exact congrArg (fun current => current.physical) generated
      have currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
          (source.stateAfter length).1.physical.contact.physicalState := by
        rw [currentEq]
        exact currentMassGt.le.trans' (by norm_num)
      have edge :=
        (standingActionMovingCappedClockRootSettlement_of_outcomeDebit
          length currentMassTwo
            (currentDebit length (Nat.lt_succ_self length))).resolved
      have settlement := edge.settlement
      have wasteNonneg := edge.waste_nonneg
      change
        standingActionMovingCappedClockPotential length =
          source.clockAt (source.stateAfter length) +
            standingActionMovingCappedClockPotential (length + 1) + edge.waste
        at settlement
      rw [Finset.sum_range_succ]
      linarith

/-- Final causal splice at the first occurrence not covered by the moving
instruction.  The root outcome is preserved, but no branch is needed to
choose the successor clock face: the capped physical ledger is total for
this high-mass incoming occurrence. -/
noncomputable def butterflyFirstUnpaidMovingCappedRootSettlement
    (stage : Nat)
    (priorDebit : ∀ prior < stage,
      ButterflyOutcomeCurrentDebitAt prior) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (standingActionMovingCappedClockState stage)
      (cappedMassKineticClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  have currentMassGt :=
    butterflyRun_currentMass_gt_eightyFive_of_priorOutcomeDebit
      stage priorDebit
  have currentEq :
      (source.stateAfter stage).1.physical =
        run stackedShortCurrent stage := by
    have generated :=
      standingActionWholeRestartMediumSource_stateAfter_current
        stackedInitialActionMaterialInstruction stage
    exact congrArg (fun current => current.physical) generated
  have currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState := by
    rw [currentEq]
    exact currentMassGt.le.trans' (by norm_num)
  let advance := standingActionMovingCapped_to_cappedMassKineticAdvance
    stage currentMassTwo
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment => exact .exactPayment advance
  | generatedResidual => exact .generatedResidual advance
  | obstruction => exact .obstructionAlternative advance

/-! ## Total root-disposition recursion -/

/-- One generated clock instruction on an exact root state.  It contains no
reserve predicate and no branch history: the root compiler will inspect the
current total disposition when advancing it. -/
structure ButterflyTotalRootClockInstructionAt
    (state : source.State) : Type where
  stage : Nat
  state_eq : state = source.stateAfter stage

def butterflyTotalRootClockState
    {state : source.State}
    (instruction : ButterflyTotalRootClockInstructionAt state) :
    SourceGeneratedRootClockStateAt source state := by
  rcases instruction with ⟨stage, rfl⟩
  exact cappedMassKineticClockState (source.stateAfter stage)

def butterflyTotalRootClockInitialInstruction :
    ButterflyTotalRootClockInstructionAt source.initial where
  stage := 0
  state_eq := rfl

/-- Above the cap the physical account settles every root constructor, so
the framework—not the source—performs the qualitative case split. -/
noncomputable def cappedMassKineticRootSettlement_of_currentMassTwo
    (stage : Nat)
    (currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  let advance := cappedMassKineticRootClockAdvance stage currentMassTwo
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment => exact .exactPayment advance
  | generatedResidual => exact .generatedResidual advance
  | obstruction => exact .obstructionAlternative advance

/-- Consume a low-mass local resolution without merging the residual and
obstruction constructors.  Only the actual generated-residual branch reads
a scalar debit. -/
noncomputable def cappedMassKineticRootSettlement_of_lowMassResolution
    (stage : Nat)
    (lowMass : wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState < 2)
    (resolution : ButterflyLowMassRootResolutionAt stage) :
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage)
      (cappedMassKineticClockState (source.stateAfter stage))
      (cappedMassKineticClockState (source.stateAfter (stage + 1)))
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage) = outcome
  unfold ButterflyLowMassRootResolutionAt at resolution
  rw [outcomeEq] at resolution
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact False.elim (lowMass_rootExact_isEmpty
        stage lowMass effect commutes)
  | generatedResidual effect residual expansion expansionEq payment =>
      have capped : ButterflyLowMassCappedCurrentDebitAt stage :=
        (butterflyActualGeneratedResidualCurrentDebit_iff_capped
          stage lowMass effect residual expansion).mp resolution
      exact .generatedResidual
        (sourceGeneratedRootClockAdvance_of_potential_domination capped)
  | obstruction =>
      by_cases capped : ButterflyLowMassCappedCurrentDebitAt stage
      · exact .obstructionAlternative
          (sourceGeneratedRootClockAdvance_of_potential_domination capped)
      · exact .obstructionIncompatible (resolution capped)

/-- Assemble the total root clock from a source-local resolver.  The
framework recursively supplies the current outcome and successor; the
resolver is consulted only after the current state is known to be low mass.
It is private so no final consumer can accept it as a premise. -/
private noncomputable def
    butterflyStandingActionRootClockLaw_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    SourceGeneratedRootClockLaw source where
  ClockInstructionAt := ButterflyTotalRootClockInstructionAt
  clockState := butterflyTotalRootClockState
  initialInstruction := butterflyTotalRootClockInitialInstruction
  transitionAt := by
    intro state instruction
    rcases instruction with ⟨stage, rfl⟩
    let nextInstruction : ButterflyTotalRootClockInstructionAt
        (source.successor (source.stateAfter stage)) :=
      { stage := stage + 1
        state_eq := (NativeFluidMediumSource.stateAfter_succ
          source stage).symm }
    refine ⟨nextInstruction, ?_⟩
    by_cases currentMassTwo : 2 ≤ wholeVorticityEuclideanMass
        (source.stateAfter stage).1.physical.contact.physicalState
    · simpa only [butterflyTotalRootClockState] using
        cappedMassKineticRootSettlement_of_currentMassTwo
          stage currentMassTwo
    · have lowMass : wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 :=
        lt_of_not_ge currentMassTwo
      simpa only [butterflyTotalRootClockState] using
        cappedMassKineticRootSettlement_of_lowMassResolution
          stage lowMass (resolve stage lowMass)

/-- Private end-to-end splice used to keep the consumer boundary honest.
Once the source supplies the current residual debit, no additional branch,
recurrence or future instruction remains between it and the frozen clock
telescope. -/
private noncomputable def butterflyStandingActionClockLaw_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    SourceGeneratedStandingActionClockLaw concreteCounterexampleInitial where
  initialActionMaterial := stackedInitialActionMaterialInstruction
  clockLaw := butterflyStandingActionRootClockLaw_of_localResolution resolve

private theorem concreteCounterexample_contactTime_summable_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    Summable fun stage =>
      (run concreteCounterexampleInitial stage).contact.time.1 :=
  (butterflyStandingActionClockLaw_of_localResolution resolve
    ).contactTime_summable

private theorem concreteCounterexample_elapsedTime_bddAbove_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    BddAbove (Set.range (elapsedTime concreteCounterexampleInitial)) :=
  contactTime_summable_forces_elapsedTime_bddAbove
    concreteCounterexampleInitial
    (concreteCounterexample_contactTime_summable_of_localResolution resolve)

private theorem
    concreteCounterexample_accumulatedSerrinAction_unbounded_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    ¬ BddAbove (Set.range
      (wholeRestartAccumulatedSerrinAction concreteCounterexampleInitial)) :=
  contactTime_summable_forces_accumulatedSerrinAction_unbounded
    concreteCounterexampleInitial
    (concreteCounterexample_contactTime_summable_of_localResolution resolve)

private theorem
    concreteCounterexample_completeSerrinReceiptFamily_isEmpty_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    ¬ (∀ requestedTime : Real, 0 < requestedTime →
      Nonempty (WholeContinuousMildSerrinReceipt
        concreteCounterexampleViscosity
        concreteCounterexampleInitial.initialState requestedTime)) :=
  contactTime_summable_excludes_completeSerrinReceiptFamily
    concreteCounterexampleInitial
    (concreteCounterexample_contactTime_summable_of_localResolution resolve)

private theorem
    concreteCounterexample_canonicalCompleteSerrinReceipt_isEmpty_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    IsEmpty (WholeContinuousMildSerrinReceipt
      concreteCounterexampleViscosity
      concreteCounterexampleInitial.initialState
      (completeSerrinAccumulationHorizon concreteCounterexampleInitial)) :=
  completeSerrinAccumulationHorizon_receipt_isEmpty
    concreteCounterexampleInitial
    (concreteCounterexample_elapsedTime_bddAbove_of_localResolution resolve)

private theorem
    concreteCounterexample_standardGlobalWholeMildSerrinSolution_isEmpty_of_localResolution
    (resolve : ∀ stage : Nat,
      wholeVorticityEuclideanMass
          (source.stateAfter stage).1.physical.contact.physicalState < 2 →
        ButterflyLowMassRootResolutionAt stage) :
    IsEmpty (StandardGlobalWholeMildSerrinSolutionAt
      concreteCounterexampleViscosity
      concreteCounterexampleInitial.initialState) :=
  contactTime_summable_standardGlobalWholeMildSerrinSolutionAt_isEmpty
    concreteCounterexampleInitial
    (concreteCounterexample_contactTime_summable_of_localResolution resolve)

end

end ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
end NavierStokes
end SaturationMonoid
